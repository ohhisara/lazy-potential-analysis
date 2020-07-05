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
prepay ::Degree -> AEnv -> AEnv -> Expression -> AnnType -> Ann -> Ann -> CLP ()
prepay k [] env e t' p p' = a_infer k env e t' p p'
prepay k ((x,(Thunk t q)) : ctx1) ctx2 e t' p p'
  = do q0 <- freshAnn
       q1 <- freshAnn
       p0 <- freshAnn
       var q `equal` (var q0 + var q1)
       var p `equal` (var p0 + var q1)
       prepay k ctx1 ((x,(Thunk t q0)):ctx2) e t' p0 p'
prepay k ctx _ e t' p p'
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


lookupEnv::AEnv -> VariableT -> AnnType
lookupEnv [] x = error "variable not in scope" 
lookupEnv ((v,t):xs)  x 
  | v == x = t 
  | otherwise = Anal.lookupEnv xs x

-- as above but enforces sharing and returns remaining context
lookupShare :: Degree -> VariableT -> AEnv -> CLP (AnnType,AEnv)
lookupShare k x env
  = case span (\(x',_) -> x'/=x) env of
    (_, []) -> error ("unbound identifier: "++show x)
    (env', (_,t):env'') -> do t1 <-decorateType k t
                              t2 <- decorateType k t
                              share t [t1,t2]
                              return (t1, env' ++ (x,t2):env'')
---------------- Inference 
a_infer ::Degree -> AEnv -> EnvT -> Expression -> AnnType -> Ann -> Ann -> CLP ()
a_infer k envA envT (NilE) t p p'  = return ()
a_infer k envA envT (ConstE _) t p p'  = return ()

a_infer k envA envT (VarE v) t (Ann p) p' = do
  let t1 = Anal.lookupEnv env v in 
    case t1 of 
      (Thunk tp a) -> do 
        if (t == t1) then do 
          var a `equalTo` p
          var p' `equalTo` 0
        else error "type mismatch"
      _ -> error "type mismatch"

a_infer k envA envT (LambdaE v e) (Func t t' q) p p' = do
  var p `geq` var p'
  var p' `equalTo` 0
  prepay k [(v,t)] env e t' q (Ann 0)

a_infer k envA envT (AppE e x) t p p' = do
  t0 <- Type_Rules.infer env e
  case t0 of 
    (Func t' t'' q) -> do 
      var p `geq` var p'
      (ty, ctx') <- lookupShare k x env 
      pe <- freshAnn
      return ()
    _ -> do 
      var p `geq` var p'
      return ()

  
        {-- pe' <- fresh_ann
        aa_infer ctx' e te pe p'
        -- allow subtyping the argument and result
        ty `subtype` t'
        t `subtype` t0
        k <- askC costApp
        ((var p - var pe) - var q) `equalTo` k
        -- allow relaxing
        -- (var p, var p') `relaxcost` (var pe ^+^ var q, var pe')  -}
  

