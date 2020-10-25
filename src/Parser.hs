--
-- Parser for minimal lazy language
-- TODO: Add Pairs
module Parser where

import           Prelude hiding (Num(..))
import           Algebra.Classes

import           Term
import           Types
import           Control.Monad(when)
import           Data.List(nub)
import           Data.LinearProgram hiding (Var)
import qualified Data.Map as Map
import           Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import           Text.ParserCombinators.Parsec.Language 
                     

-- type synonym for
-- int state for generating type annotations on-the-fly
type Parser = Parsec String Int

-- setup a Parsec tokenizer
lexer :: P.TokenParser Int
lexer = P.makeTokenParser termLanguage

termLanguage 
  = emptyDef { commentStart   = "{-"
             , commentEnd     = "-}"
             , commentLine    = "--"
             , nestedComments = True
             , identStart     = lower
             , identLetter     = alphaNum <|> oneOf "_'"
             , opStart   = opLetter haskellStyle
             , opLetter  = oneOf ":!#$%&*+./<=>?\\^|-~"
             , reservedOpNames= ["=", "|", "->", "\\", "@", "#"]
             , reservedNames  = ["let", "letcons", "match", "in", 
                                 "with", "otherwise",
                                 "if", "then", "else"]
             , caseSensitive  = True
             }

                           
-- tokens (using Parsec tokenizer)
integer    = P.integer lexer
float      = P.float lexer
identifier = P.identifier lexer
reserved   = P.reserved lexer
reservedOp = P.reservedOp lexer
symbol     = P.symbol lexer
whiteSpace = P.whiteSpace lexer
comma      = P.comma lexer
dot        = P.dot lexer
colon      = P.colon lexer
semi       = P.semi lexer
natural    = P.natural lexer
naturalOrFloat = P.naturalOrFloat lexer
charLiteral= P.charLiteral lexer
stringLiteral = P.stringLiteral lexer
parens     = P.parens lexer
brackets   = P.brackets lexer
angles     = P.angles lexer
braces     = P.braces lexer
lexeme     = P.lexeme lexer
commaSep   = P.commaSep lexer
operator   = P.operator lexer
bar = reservedOp "|"

-- identifier beginning with a capital letter
capitalIdent = lexeme $ 
               do { c <- upper
                  ; cs<- many (identLetter termLanguage)
                  ; return (c:cs)
                  }

toplevel :: Parser (Term ())
toplevel = do { whiteSpace
              ; t <- appterm 
              ; whiteSpace
              ; eof
              ; return t 
              }

-- a self-delimited term
term = do { reservedOp "\\"
          ; xs <- many1 identifier
          ; reservedOp "->"
          ; e <- appterm
          ; return (foldr Lambda e xs)
          }
       <|> do { reserved "let" 
              ; x <- identifier
              ; ann <- maybe id Coerce <$> optionMaybe type_annotation
              ; reservedOp "="
              ; e1 <- appterm
              ; reserved "in"
              ; e2 <- appterm
              ; return (Let x (ann e1) e2)
              }
        <|> do { reserved "Pair" 
              ; reserved "("
              ; x1 <- identifier
              ; reserved ","
              ; x2 <- identifier
              ; reserved ")"
              ; return (Pair x1 x2)
              }
       <|> do { reserved "letcons"
              ; x <- identifier
              ; ann <- maybe id Coerce <$> optionMaybe type_annotation
              ; reservedOp "="
              ; reserved "Cons"
              ; reserved "("
              ; c1 <- identifier
              ; reserved ","
              ; c2 <- identifier
              ; reserved ")"
              ; reserved "in"
              ; e2 <- appterm
              ; return (Let x (ann $ ConsApp c1 c2) e2)
              }
       <|> do { reserved "match"
              ; e <- appterm
              ; reserved "with"
              ; reserved "Cons"
              ; reserved "("
              ; c1 <- identifier
              ; reserved ","
              ; c2 <- identifier
              ; reserved ")"
              ; reserved "->"
              ; e1 <- appterm
              ; reserved "|"
              ; reserved "Nil ->"
              ; e2 <- appterm
              ; ann <- maybe id Coerce <$> optionMaybe type_annotation
              ; return (Match e (ann $ ConsApp c1 c2) e1 Nil e2) 
              } 
       <|> do { x <- identifier
              ; return (Var x)
              }
       <|> do { n <- integer
              ; return (Const n)
              }
       <|> do { n <- reserved "Nil"
              ; return Nil
              }
       <|> do {reserved "Cons"
              ; reserved "("
              ; c1 <- identifier
              ; reserved ","
              ; c2 <- identifier
              ; reserved ")"
              ; return (ConsApp c1 c2)
              }
       <|> parens appterm
       

-- sequence of applications
appterm = try (do { e <- term
                 ; ys<- many identifier
                 ; return (foldl App e ys)
                 }) 
          <?> "application"
          


type_annotation :: Parser (SrcType, [SrcConstr])
type_annotation = do { colon 
                     ; reset_annotations
                     ; t <- type_expr
                     ; let vs = annotations t
                     ; when (dupl vs) $
                       fail "duplicate annotation variable"
                     ; option (t,[]) $ 
                       do { cs <- braces (constraint `sepBy` comma)
                          ; when (any (`notElem`vs) (vars cs)) $
                            fail "undefined variable in constraint"
                          ; return (t,cs)
                          }
                     }
  where dupl xs = length xs /= length (nub xs)
        vars cs = concat [Map.keys lf | Constr _ lf _ <- cs]

-------------------------------------------------------
-- parser for annotated type expressions
-- right-associated sequence of arrows
type_expr :: Parser SrcType
type_expr = do { t1 <- type_base 
               ; option t1 $
                 do { reservedOp "->"
                    ; p <- opt_ann
                    ; t2 <- type_expr
                    ; return (TyFun p t1 t2)    
                    }
               }

-- basic type expressions
type_base = do { reserved "T"
               ; p <- opt_ann
               ; t <- parens type_expr
               ; return (TyThunk p t)
               }
            <|> do { c <- capitalIdent; return (TyCon c) }
            <|> do { v <- identifier; return (TyVar v) }
            <|> parens type_expr
            

-- optional annotation 
-- generates a fresh name 
opt_ann :: Parser String
opt_ann = do { reservedOp "@"; identifier} <|> new_annotation

reset_annotations :: Parser ()
reset_annotations = setState 0

new_annotation :: Parser String
new_annotation = do { n <- getState
                    ; updateState (+1)
                    ; return ('_':show n)
                    }



-- parser for constraints
constraint :: Parser SrcConstr
constraint = do { e <- lin_func 
                ; r <- rel_op
                ; c <- natural
                ; return (Constr Nothing e (r $ fromIntegral c))
                }
             <?> "linear constraint"
             
rel_op = do { reservedOp "<="; return UBound }             
         <|> do { reservedOp ">="; return LBound }
         <|> do { reservedOp "="; return Equ }
         <?> "relational operator"
         

lin_func :: Parser (LinFunc String Int)
lin_func = do { t <- lin_term
              ; ts <- many lin_term'
              ; return (add (t:ts))
              }

lin_term :: Parser (LinFunc String Int)
lin_term = do { v <- identifier; return (linCombination [(1,v)]) }
           <|> do { c <- natural
                  ; v <- identifier
                  ; return (linCombination [(fromInteger c, v)])
                  }
           <?> "linear term"
           
lin_term' = do { s <- sign; 
                 t <- lin_term; 
                 return (s t) }
            <?> "linear term"
  where sign = do { reservedOp "+"; return id }
               <|> do { reservedOp "-"; return (Map.map negate) } 
           
