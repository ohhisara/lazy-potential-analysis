{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable
#-}
--
-- Type expressions and annotations
--
module Types where

import           Data.Foldable (toList)
import           Data.Map (Map)
import qualified Data.Map as Map

infixr 4 ~>     -- function type constructor

-- | type expressions with annotations 'a' 
data TyExp a
  = TyVar TVar                    -- ^ variables
  | TyThunk a (TyExp a)           -- ^ thunks
  | TyFun a (TyExp a) (TyExp a)   -- ^ functions
  | TyCon TConst                  -- ^ base types (e.g. Int)
  | TyPair (TyExp a) (TyExp a)
  | TyList a [a] (TyExp a)        -- ^ list types 
  deriving (Eq, Show, Functor, Foldable, Traversable)
                          

type TVar = String      -- ^ type variables
type TConst = String    -- ^ basic types
type Cons = String      -- ^ constructor tags


-- | Hindley-Milner types (without annotations)
type HMtype = TyExp ()

-- | annotated types 
type Atype = TyExp Ann

-- | annotation variables
newtype Ann = Ann Int deriving (Eq,Ord,Enum, Num)

instance Show Ann where
  showsPrec _ (Ann n) = ('a':) . shows n



-- | auxiliary functions to make simple types
tycon = TyCon
tyvar  = TyVar
tyfun = TyFun
hmfun = TyFun () 
(~>) = hmfun
thunk   = TyThunk
hmthunk = TyThunk ()
hmalt c t = (c, (), t)

hmint = TyCon "Int"


annotations :: Foldable t => t a -> [a]
annotations = toList

-- | collect all type variables
-- generic foldable and for plain type expressions
typevars :: Foldable f => f (TyExp a) -> [TVar]
typevars = foldMap tyvars 

tyvars :: TyExp a -> [TVar]
tyvars (TyCon _) = []
tyvars (TyVar x) = [x]
tyvars (TyPair t1 t2) = tyvars t1 ++ tyvars t2
tyvars (TyThunk _ t) = tyvars t
tyvars (TyFun _ t1 t2) = tyvars t1 ++ tyvars t2
tyvars (TyList _ _ t) = tyvars t


-- -- | substitute the recursive self-reference in a type
-- recsubst :: TyExp a -> TyExp a -> TyExp a
-- recsubst _ (TyVar x) = TyVar x
-- recsubst _ (TyCon b) = TyCon b
-- recsubst t (TyThunk q t') = TyThunk q (recsubst t t')
-- recsubst t (TyFun q t1 t2) = TyFun q (recsubst t t1) (recsubst t t2)

-- | type substitutions 
type Tysubst a = Map TVar (TyExp a)
type HMsubst = Tysubst ()


-- | apply a substitution to a type
appsubst :: Tysubst a -> TyExp a -> TyExp a 
appsubst _ t@(TyCon _) = t
appsubst s t@(TyVar v) = Map.findWithDefault t v s
appsubst s (TyThunk q t') = TyThunk q (appsubst s t')
appsubst s (TyFun q t1 t2) = TyFun q (appsubst s t1) (appsubst s t2)
appsubst s (TyPair t1 t2) = TyPair(appsubst s t1) (appsubst s t2)
appsubst s (TyList q p t) = TyList q p (appsubst s t)
          


