{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
--
-- Abstract syntax for minimal lazy language
-- Pedro Vasconcelos, 2012
-- 
module Term where

import           Types
import           Data.LinearProgram hiding (Var)
-- import           Data.List
import           Data.Set (Set)
import qualified Data.Set as Set

-- | identifiers 
type Ident = String

-- | terms with sub-terms with annotations `a' 
-- used to keep the type information and 
-- avoid the need for "guessing" during constraint collection
data Term a
  = Var Ident
  | Nil
  | Lambda Ident (Term a) 
  | App (Term a) Ident
  | Pair Ident Ident
  | Let Ident (Term a) (Term a)
    -- ^ letcons is a special use case of let
  | Match (Term a) (Term a) (Term a) (Term a) (Term a)
    -- ^ optinal term is the "otherwise" alternative
  | ConsApp Ident Ident       -- ^ constructor application
  | Const !Integer             -- ^ primitive integers
  | Coerce SrcAnn (Term a)     -- ^ source level annotation
  | (Term a) :@ a              -- ^ type checker annotation
  deriving (Show, Functor, Foldable, Traversable)

-- -- | match alternatives
-- type Alt a = (Cons, [Ident], Term a) 

-- | source annotations
type SrcAnn  = (SrcType, [SrcConstr])
type SrcType = TyExp String
type SrcConstr = Constraint String Int

-- | a typing judgment for a closed term
-- parameterized by annotations 'a'
data Typing a
  = Typing { aterm :: Term (TyExp a)
           , atype :: TyExp a
           , ann_in :: a 
           , ann_out :: a 
           }
  deriving (Functor, Foldable, Traversable, Show)


-- | shorthand constructors for simple (i.e. non-annotated) terms 
-- lvar x = Var x
-- lapp e y = App e y
-- lmatch e0 alts other = Match e0 alts other
-- lconsapp c ys = ConsApp c ys
-- llambda x e = Lambda x e
-- llet x e1 e2 = Let x e1 e2
-- lconsalt cons xs e = (cons, xs, e) 
-- lconst n = Const n
-- lprimop op x y = PrimOp op x y


-- | collect free variables from a term
freevars :: Term a -> Set Ident
freevars (Nil)        = Set.empty
freevars (Var x)        = Set.singleton x
freevars (Lambda x e)   = Set.delete x (freevars e)
freevars (App e y)      = Set.insert y (freevars e)
freevars (Pair v1 v2) = (Set.singleton v1) `Set.union` (Set.singleton v2 ) 
freevars (ConsApp v1 v2) = (Set.singleton v1) `Set.union` (Set.singleton v2 ) 
freevars (Let x e1 e2)  = Set.delete x (freevars e1 `Set.union` freevars e2)
freevars (Match e1 e2 e3 e4 e5) = freevars e1 `Set.union` 
                                 freevars e2 `Set.union`
                                 freevars e3 `Set.union` 
                                 freevars e4 `Set.union` 
                                 freevars e5  
freevars (Const _)         = Set.empty
freevars (Coerce _ e)      = freevars e
freevars (e :@ _)          = freevars e

-- | rename an identifier
rename :: Ident -> Ident -> Term a -> Term a
rename _ _ e@(Nil) = Nil
rename x y e@(Var v) | v==x      = Var y
                     | otherwise = e                                 
rename x y e@(Lambda x' e') 
  | x==x'     = e
  | otherwise = Lambda x' (rename x y e')
rename x y (App e' v) = App (rename x y e') v'
  where v' | v==x      = y
           | otherwise = v
rename x y (ConsApp v1 v2) 
  = ConsApp (if x==v1 then y else v1) (if x==v2 then y else v2)
rename x y (Pair v1 v2) 
  = Pair (if x==v1 then y else v1) (if x==v2 then y else v2)
rename x y e@(Let x' e1 e2) 
  | x'==x     = e
  | otherwise = Let x' (rename x y e1) (rename x y e2)
  
rename x y (Match e1 e2 e3 e4 e5) 
  = Match (rename x y e1) (rename x y e2) (rename x y e3) (rename x y e4) (rename x y e5)
    
rename x y e@(Const n) = e                                   

-- annotations
rename x y (Coerce a e) = Coerce a (rename x y e)  
rename x y (e :@ a) = rename x y e :@ a

-- | rename many identifiers 
renames :: [Ident] -> [Ident] -> Term a -> Term a 
renames (x:xs) (y:ys) e = renames xs ys (rename x y e)
renames [] [] e = e
renames _  _  _ = error "renames: variable lists must have equal length"

