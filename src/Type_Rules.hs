module Type_Rules where

import Syntax
import qualified Data.Map as Map
import Control.Monad.Except
import Control.Monad.State
import Debug.Trace


type (Subst a) = Map.Map VariableT (Type a)
type HMSubst = Subst ()

type EnvT = Map.Map VariableT HMType

-- a monad for Hindler-Milner type inference/checking 
-- combination of state and failure 
type TC = StateT TCState (Either String)
    
-- type checking state: fresh var generation and current unifier 
data TCState = TCState { counter :: Int,  unifier :: HMSubst } deriving (Eq, Show)

freshVars:: Int -> TC [VariableT]
freshVars n = do
    i <- gets counter 
    modify $ \s -> s {counter=counter s+n} 
    return ['t':show n | n<-[i..i+n-1]]

freshVar:: TC VariableT
freshVar = liftM head (freshVars 1)

-- lookup type variable in environment  
lookupEnv :: VariableT -> EnvT -> TC HMType
lookupEnv x env = case (Map.lookup x env) of
    Nothing -> do 
      s <- gets unifier
      throwError ("unbound variable: " ++ show x ++ "\n Uni: " ++ show s ++  "\n Env: " ++ show env)
    Just t -> return t


--------------------- Unification
unify::HMType -> HMType -> TC ()
unify t1 t2 | trace ("Unify: T1 - " ++ show t1 ++ " T2 - " ++ show t2) False = undefined
unify t1 t2 = do 
    u <- gets unifier
    case unifyE [(t1, t2)] u of
                   Left err -> throwError err
                   Right u' -> modify $ \s -> s {unifier=u'}

unifyE'::[(HMType,HMType)] -> HMSubst -> Either String HMSubst
unifyE' [] s = return s
unifyE' ((t,t'):xs) s= unifyE (((appsubst s t),(appsubst s t')):xs) s

unifyE::[(HMType,HMType)] -> HMSubst -> Either String HMSubst
unifyE ((t1,t2):xs) s | trace ("Subs - " ++ show s) False = undefined
unifyE ((Prim, Prim):xs) s = return s 
unifyE ((VarT x, VarT y):xs) s = case compare x y of   -- fix bindings from higher to lower variables
    EQ -> unifyE' xs s
    LT -> unifyE' xs (extend y (VarT x) s)
    GT -> unifyE' xs (extend x (VarT y) s)
unifyE (((VarT x),t):xs) s
  | x `notElem` tyvars t = unifyE' xs (extend x t s)
  | otherwise = throwError ("occurs check")
unifyE ((t, (VarT x)):xs) s= Right (extend x t s)
unifyE (((Func t1 t2 _),(Func t1' t2' _)):xs) s = unifyE' ((t1,t1'):(t2,t2'):xs) s
unifyE (((Thunk t ()),(Thunk t' ())):xs) s = unifyE' ((t,t'):xs) s
unifyE ((t1,t2):xs) s = throwError ("Type mismatch: " ++ show t1 ++ " AND " ++ show t2 ++  "!" )

tyvars :: Type a -> [VariableT]
tyvars Prim    = []
tyvars( VarT v) = [v]
tyvars (Thunk t _) = tyvars t
tyvars (Func t1 t2 _) = tyvars t1 ++ tyvars t2
tyvars (List t _ _) = tyvars t

extend :: VariableT -> HMType -> HMSubst -> HMSubst 
extend v t s = Map.insert v t $ Map.map (appsubst s') s
  where s' = Map.singleton v t

-- | apply a substitution to a type
appsubst :: HMSubst -> HMType -> HMType
appsubst s Prim  = Prim 
appsubst s (VarT v) = case Map.lookup v s of 
    Just t -> t 
    Nothing -> (VarT v)
appsubst s (Thunk t an) = Thunk (appsubst s t) an
appsubst s (Func t1 t2 an)= Func (appsubst s t1) (appsubst s t2) an
appsubst s (List t an la) = List (appsubst s t) an la


--------------------- HM type inference
infer :: EnvT -> Expression -> TC HMType
infer env e | trace ("Infer: Env - " ++ show env ++ " Expr - " ++ show e) False = undefined
infer env NilE = do 
    var <- freshVar
    return (List (VarT var) () [()])

infer env (ConstE _) = do 
    var <- freshVar
    return Prim 

infer env (VarE x) = do 
    t <- lookupEnv x env
{-     a <- freshVar
    unify t (Thunk (VarT a) ()) -}
    case t of 
      (Thunk t1 _) -> return t1
      _ -> throwError ("Var " ++ show x ++ " not a thunk.")

infer env (LambdaE x e) = do 
    var <- freshVar
    let env' = Map.insert x (Thunk (VarT var) ()) env
    t <- infer env' e 
    return (Func (Thunk (VarT var) ()) t ()) 

infer env (AppE e x) = do 
  t<- lookupEnv x env 
  t1 <- infer env e 
  c <- freshVar 
  unify t1 (Func t (VarT c) ())
  return (VarT c)

infer env (LetE x e1 e2) = do 
  a <- freshVar
  let env' = Map.insert x (Thunk (VarT a) ()) env 
  t1 <- infer env' e1 
  unify t1 (VarT a)
  t2 <- infer env' e2 
  return t2

infer env (ConsE v1 v2) = do 
  b <- lookupEnv v1 env 
  l <- lookupEnv v2 env 
  unify l (List b () [()])
  return l 

infer env (LetconsE x e1 e2) = do
  a <- freshVar
  b <- freshVar
  unify (VarT a) (List (VarT b) () [()])
  let env' = Map.insert x (Thunk (VarT a) ()) env 
  t1 <- infer env' e1 
  unify t1 (VarT a)
  t2 <- infer env' e2 
  return t2

infer env (MatchE e (ConsE v1 v2) e1 NilE e2) = do
  t1 <- infer env e 
  b <- freshVar
  unify t1 (List (VarT b) () [()])
  let env' = Map.insert v1 (VarT b) env 
  let env'' = Map.insert v2 (List (VarT b) () [()]) env''
  t2 <- infer env'' e1
  t3 <- infer env'' e2 
  unify t2 t3
  return t2

initState = TCState {counter = 0, unifier = Map.empty}
ex3 = (LetE "y" (ConstE 1) (AppE (LambdaE "x" (VarE "x"))"y"))
ex1 = (LetE "f" (LetE "i" (LambdaE "x" (VarE "x")) (AppE (LambdaE "x" (VarE "x")) "i")) 
      (LambdaE "x" (LetE "y" (AppE (VarE "f") "x") (AppE (VarE "f") "y"))))
ex2 = (LetE "f" (LetE "i" (LambdaE "x" (VarE "x")) (AppE (LambdaE "x" (VarE "x")) "i")) 
      (AppE (LambdaE "x" (LetE "y" (AppE (VarE "f") "x") (AppE (VarE "f") "y"))) "a"))
main = runStateT (infer (Map.empty) ex1) initState
  
{-hm_infer ctx (ConsApp c ys)
  = do (TyFun _ t' t) <- lookupTc c ctx
       targs <- sequence [lookupTc y ctx | y<-ys]
       unify t' (tuple targs)
       return (ConsApp c ys :@ t)

hm_infer ctx (Match e0 alts Nothing)
  = do (e0' :@ t0) <- hm_infer ctx e0
       a <- freshvar
       alts' <- hm_infer_alts ctx alts t0 (tyvar a)
       return (Match (e0':@t0) alts' Nothing :@ tyvar a)
           
hm_infer ctx (Match e0 alts (Just e1))
  = do (e0' :@ t0) <- hm_infer ctx e0
       (e1' :@ t1) <- hm_infer ctx e1
       alts' <- hm_infer_alts ctx alts t0 t1       
       return (Match (e0':@t0) alts' (Just e1') :@ t1)
       
-- constants       
hm_infer ctx (Const n)
  = return (Const n :@ hmint)

-- primitive operations
-- looks type in the context as if it were a curried function
hm_infer ctx (PrimOp op x y)
  = do TyThunk _ (TyFun _ tx (TyFun _ ty t)) <- lookupTc op ctx
       tx' <- lookupTc x ctx
       ty' <- lookupTc y ctx
       unify tx tx'
       unify ty ty'
       return (PrimOp op x y :@ t)

hm_infer ctx (Coerce a@(t',_) e) 
  = do (e' :@ t) <- hm_infer ctx e        
       -- ensure the annotated type has the same HM structure       
       let t'' = fmap (\_ -> ()) t'
       unify t t''
       return (Coerce a e' :@ t)
       

hm_infer ctx _ = error "hm_infer: invalid argument" -}


 




