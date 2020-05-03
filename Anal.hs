{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Anal where
import Prelude hiding (Num(..))
import Algebra.Classes hiding (zero)

import Syntax
import Type_Rules
import Control.Monad.State
import Control.Monad.Reader
import Data.LinearProgram hiding (Var,zero)
import Data.LinearProgram.GLPK.Solver
import Control.Monad.LPMonad hiding (Var)
import Data.Map (Map)
import Control.Monad.Except

data ExprA
  = ValueA Int
  | SizeA ExprA
  | VarA String
  | SumA ExprA ExprA
  | SubA ExprA ExprA
  | ProdA ExprA ExprA
  | MaxA ExprA ExprA

data Constraint
  = Eq ExprA ExprA
  | LTE ExprA ExprA

type Degree = Int
-- | a monad for constructing linear programs
type CLP = LPT Ann Int (StateT Ann (Reader Anal.Constraint))
type AEnv = [(VariableT,AnnType)] 
-- | fixed zero annotation variable
zero_ann :: Ann
zero_ann = Ann 0

zero :: LinFunc Ann Int
zero = linCombination []

-- | singleton annotation variables
var :: Ann -> LinFunc Ann Int
var x = linCombination [(1,x)]

-- | sum a list of annotations
vars :: [Ann] -> LinFunc Ann Int
vars xs = linCombination $ zip (repeat 1) xs

-- | generate a fresh annotation variable
freshAnn :: CLP Ann
freshAnn = do 
    a <- lift (do {modify succ; 
                  get})       
    varGeq a 0  -- impose non-negativity
    return a

freshAnns :: Degree -> [Ann] -> CLP [Ann]
freshAnns k an = do 
    if (k > 0)
        then do
            a <- lift (do {modify succ; 
                get}) 
            freshAnns (k-1) (a:an)
        else (return an) 

decorateType::Degree -> Type a -> CLP AnnType
decorateType _ Prim = return Prim
decorateType _ (VarT x) = return (VarT x)
decorateType k (Thunk t _) 
  = do q <- freshAnn
       t'<- decorateType k t 
       return (Thunk t' q)
                              
decorateType k (Func t1 t2 _) 
  = do p <- freshAnn
       t1' <- decorateType k t1
       t2' <- decorateType k t2
       return (Func t1' t2' p)
       
decorateType k (List t _ _) 
  = do 
      anns <- freshAnns k []
      a <- freshAnn
      t' <- decorateType k t
      return (List t' a anns)


----------------------- Structural type rules
prepay :: AEnv -> AEnv -> AnnType -> AnnType -> Ann -> Ann -> CLP ()
prepay [] env e t' p p' = a_infer env e t' p p'
prepay ((x,(Thunk t q)) : ctx1) ctx2 e t' p p'
  = do q0 <- freshAnn
       q1 <- freshAnn
       p0 <- freshAnn
       var q `equal` (var q0 + var q1)
       var p `equal` (var p0 + var q1)
       prepay ctx1 ((x,(Thunk t q0)):ctx2) e t' p0 p'
prepay ctx _ e t' p p'
  = error ("aa_infer_prepay: invalid context\n " ++ show ctx)

-----------------------Share relation
share::AnnType -> [AnnType] -> CLP ()
share Prim _ = return ()
share (VarT _) _ = return ()
share (Func t1 t2 a) ts =  sequence_ [ do { var qi `geq` var a
                    --; (var qi ^-^ var q) `geq` (var qi' ^-^ var q')
                    ; share ai [t1]
                    ; share t2 [bi]
                    }
               | Func ai bi qi <- ts] -- o que faz isto?? 
share (Thunk t1 a) ts =  sequence_ [ do { var qi `geq` var a
                    --; (var qi ^-^ var q) `geq` (var qi' ^-^ var q')
                    ; share t1 [ti]
                    }
               | Thunk ti qi <- ts] -- o que faz isto?? 
share (List t1 a l) ts =  sequence_ [ do { var i `geq` var a
                    ; (vars l) `geq` (vars li)
                    ; share t1 [ti]
                    }
               | List ti i li <- ts] -- o que faz isto??  -}
share _ _ = error ("type mismatch share")
        
---------------- Inference 
a_infer :: AEnv -> AnnType -> AnnType -> Ann -> Ann -> CLP ()
a_infer a b c d e = return ()