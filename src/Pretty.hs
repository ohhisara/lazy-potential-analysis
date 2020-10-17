-- Pretty printers for terms and types
-- pbv, 2012
module Pretty where

import Prelude hiding ((<>))
import Term
import Types
import Text.PrettyPrint.HughesPJ
import Data.List(nub,intersperse)
import qualified Data.Map as Map

-- | typeclass to overload showing of annotations
class ShowA a where
  showA :: a -> String        -- a single annotation 
  showAs :: a -> a -> String  -- a pair (thunks and arrows)

instance ShowA () where
  showA _ = ""
  showAs _ _ = ""  

instance ShowA Ann where
  showA a     = "@" ++ show a
  showAs a a' = "@" ++ show a ++ "/" ++ show a'

-- | typeclass to overload showing of potential
-- class ShowP a where
--   showP :: a -> String        -- a single annotation 
  
-- instance ShowP () where
--   ShowP _ = ""

-- instance ShowP [Ann] where
--   showP p = showPotential p


-- showPotential::[Ann] -> String 
-- showPotential (a1:[]) = (show a1) ++ ")"
-- showPotential (a1:as) = "(" ++ (show a1) ++ "," ++ (ShowP as)

instance ShowA Double where
  showA q = if iszero q then "" else "@" ++ showRound q
  showAs q q'
      | iszero q && iszero q' = ""
      | otherwise =  "@" ++ showRound q ++ "/" ++ showRound q'

-- s

showRound :: Double -> String
showRound x = let r = round x :: Int
              in if iszero (x - fromIntegral r) then
                   show r else show x

iszero :: Double -> Bool
iszero x = abs x < 1e-6


-- | typeclass to overload pretty-printing
class Pretty a where
  prettyPrec :: Int -> a -> Doc
  pretty :: a -> Doc
  pretty = prettyPrec 0
  

instance Pretty a => Pretty (Term a) where
  prettyPrec = prettyTerm
  
instance ShowA a => Pretty (TyExp a) where  
  prettyPrec = prettyType

instance Pretty () where
  prettyPrec n _ = empty

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- | pretty-printing terms
prettyTerm :: Pretty a => Int -> Term a -> Doc
prettyTerm _ (Var x) = text x
prettyTerm _ Nil = text "Nil"
prettyTerm p (Lambda x e)
  = parensIf (p>3) $ 
    fsep [char '\\' <> hsep (map text (x:args e)), text "->", 
          nest 2 (prettyTerm 2 (body e))]
      where args (Lambda y e) = y : args e
            args e            = []
            body (Lambda y e) = body e
            body e            = e


prettyTerm p (App e y) = prettyTerm 4 e <+> text y
prettyTerm p (ConsApp c1 c2) 
  = ppConsApp c1 c2 
prettyTerm p (Pair c1 c2) 
  = ppPair c1 c2 
prettyTerm p (Let x (e1 :@ a) e2)
  = parensIf (p>3) $
    fsep [ text "let", text x, colon, pretty a,
          nest 2 (sep [equals, prettyTerm 0 e1]),
          text "in", prettyTerm 2 e2
        ]
prettyTerm p (Let x e1 e2)
  = parensIf (p>3) $ 
    fsep [ text "let", text x,
          nest 2 (fsep [equals, prettyTerm 0 e1]), 
          text "in", prettyTerm 2 e2
         ]
prettyTerm p (Match e0 (ConsApp c1 c2) e2 e3 e4)    
  = parensIf (p>3) $
    fsep ([text "match", prettyTerm 0 e0, text "with"] 
          ++
          [char '|' <+> (ppConsApp c1 c2) <+> text "->",
                      nest 2 (prettyTerm 2 e2)]
          ++
          --sep (punctuate (char '|') $ map (nest 2 . ppalt) alts),
        [char '|' <+> text "Nil" <+> text "->",
                      nest 2 (prettyTerm 2 e4) ]) 
         
                             
prettyTerm p (Const n) = text (show n)                             

prettyTerm p (Coerce (t,cs) e) -- TODO: fix this!
  = prettyTerm p e
prettyTerm p (e :@ a) 
  = fsep [prettyTerm p e, colon, pretty a]


ppConsApp c1 c2 = text "Cons" <> parens (hcat $ punctuate comma (map text [c1,c2]))
ppPair c1 c2 = text "P" <> parens (hcat $ punctuate comma (map text [c1,c2]))



-- | pretty-printing annotated types
prettyType :: ShowA a => Int -> TyExp a -> Doc
prettyType _ (TyVar v) = text v
prettyType _ (TyCon c) = text c
prettyType _ (TyThunk q t) 
  = text ("T" ++ showA q) <> parens (prettyType 0 t)
    
prettyType p (TyFun q t1 t2)
  = parensIf (p>3) $
    fsep [prettyType 4 t1, 
          nest 2 (ppArrow q), 
          nest 2 (prettyType 3 t2)]
prettyType _ (TyPair t1 t2) = text "P" <> parens  ((prettyType 0 t1) <> comma <> (prettyType 0 t2))
prettyType _ (TyList q p t) = text ("L" ++ showA q ) <> parens (prettyType 0 t)
ppArrow q =  text ("->" ++ showA q)






-- | pretty-print typings
instance ShowA a => Pretty (Typing a) where
  prettyPrec _ (Typing e t p p') 
    -- rename all typevars to A, B, C, ...
    = let tvs = nub (typevars e ++ tyvars t)
          s = Map.fromList $ zip tvs (map TyVar varnames)
          e' = fmap (appsubst s) e
          t' = appsubst s t
      in fsep [text ("|-"  ++ showAs p p'),
               nest 2 (pretty e'), 
               colon, 
               nest 2 (pretty t')]


-- pretty variables names
varnames :: [String]
varnames = let singles = "abc"
           in [[v] | v<-singles] ++ [v:show n | n<-[1..], v<-singles]
                            
instance ShowA a => Show (Typing a) where
  show t = render (pretty t)



