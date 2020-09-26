{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
--
-- Lazy Amortized Analysis
--
module Analysis where

import           Prelude hiding (Num(..))
import           Algebra.Classes hiding (zero)

import           Term
import           Types
import           Control.Monad.State
import           Control.Monad.Reader
import           Data.LinearProgram hiding (Var,zero)
import           Data.LinearProgram.GLPK.Solver
import           Control.Monad.LPMonad hiding (Var)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List (transpose, partition, nubBy)
import           Data.Char (isSymbol)
import           Options
import           Cost (CostModel(..))
import           Debug.Trace  
import           DamasMilner

-- | Degree of polynomial function
type Degree = Int

-- | typing contexts for annotated types
type Context a = [(Ident,TyExp a)]

-- | context for the lazy amortized analysis
type Acontext = Context Ann

-- | a monad for constructing linear programs
type CLP = LPT Ann Int (StateT Ann (Reader Options))

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
fresh_ann :: CLP Ann
fresh_ann = do a <- lift (do {modify succ; get})
               varGeq a 0  -- impose non-negativity
               return a

-- | generate list of fresh annotation variables        
fresh_anns:: Degree -> CLP [Ann]
fresh_anns 0 = return []
fresh_anns k = do
  a <- fresh_ann
  anns <- fresh_anns (k-1)
  return (a:anns)

-- | additive shift of a vector of annotations (second argument is additive shift of first argument)
additive_shift::[Ann] -> [Ann] -> CLP ()
additive_shift an1 an2| trace ("ADDITIVE SHIFT: T1 - " ++ show an1 ++ " T2 - " ++ show an2) False = undefined
additive_shift (t1:t2:ts) (p1:ps)  
  | length (t1:t2:ts) == length (p1:ps) = do 
    (var t1 + var t2 - var p1) `equalTo` 0
    additive_shift (t2:ts) ps
  | otherwise = error "txi"
additive_shift (tn:[]) (pn:[]) = do 
    (var tn - var pn) `equalTo` 0

-- | decorate a type with fresh anotation variables
decorate_type :: Degree -> TyExp a -> CLP Atype
decorate_type k (TyVar x) = return (TyVar x)
decorate_type k (TyThunk _ t) 
  = do q <- fresh_ann
       t'<- decorate_type k t
       return (TyThunk q t')
                              
decorate_type k (TyFun _  t1 t2) 
  = do p <- fresh_ann
       t1' <- decorate_type k t1
       t2' <- decorate_type k t2
       return (TyFun p t1' t2')
            
decorate_type k (TyPair t1 t2) 
  = do p <- fresh_ann
       t1' <- decorate_type k t1
       t2' <- decorate_type k t2
       return (TyPair t1' t2')

decorate_type k (TyCon b) = return (TyCon b)

decorate_type k (TyList _ _ t) 
      = do an <- fresh_ann
           p <- fresh_anns k
           t1 <- decorate_type k t
           return (TyList an p t1)


-- | decorate a term with annotation variables
decorate_term :: Degree -> Term HMtype -> CLP (Term Atype)
decorate_term k Nil = return Nil
decorate_term k (Var x) = return (Var x)

decorate_term k (Lambda x e) 
  = do e' <- decorate_term k e
       return (Lambda x e')
       
decorate_term k (App e y) 
  = do e' <- decorate_term k e
       return (App e' y)
       
decorate_term k (ConsApp x1 x2) 
  = return (ConsApp x1 x2)

decorate_term k (Pair x1 x2) 
  = return (Pair x1 x2)

decorate_term k (Let x e1 e2)    
  = do e1'<- decorate_term k e1
       e2'<- decorate_term k e2
       return (Let x e1' e2')
       
decorate_term k (Match e0 e1 e2 e3 e4)
  = do e0' <- decorate_term k e0
       e1' <- decorate_term k e1
       e2' <- decorate_term k e2
       e3' <- decorate_term k e3
       e4' <- decorate_term k e4
       return (Match e0' e1' e2' e3' e4')

       
-- | primitive operations       
decorate_term k (Const n)       = return (Const n)

decorate_term k (Coerce a e) 
  = do e' <- decorate_term k e
       return (Coerce a e')

-- | annotations  
decorate_term k (e :@ t) 
  = do e' <- decorate_term k e
       t' <- decorate_type k t 
       return (e' :@ t')


decorate_term k e = error ("non exaustive " ++ (show e))


-- | sharing relation between types
-- pre-condition: types have the same Hindley-Milner structure       
share :: Atype -> [Atype] -> CLP ()
share a (l:ls)| trace ("SHARE - " ++ show a ++ " WITH - " ++ show l) False = undefined

share _ [] = return ()

-- thunks
share (TyThunk q t0) ts 
  = do sequence_ [ do { var qi `geq` var q  
                      -- ; (var qi - var q) `geq` (var qi' - var q')
                      }
                 | TyThunk qi ti <- ts]
       share t0 [ ti | TyThunk qi ti <- ts]
       
-- function types
share (TyFun q a b) ts
  =  sequence_ [ do { var qi `geq` var q
                    --; (var qi ^-^ var q) `geq` (var qi' ^-^ var q')
                    ; share ai [a]
                    ; share b [bi]
                    }
               | TyFun qi ai bi <- ts]

share (TyCon b) ts = return ()

share (TyVar x) ts = return ()

share (TyPair t1 t2) ts = sequence_ [ do { share t1 [t1']
                    ; share t2 [t2'] 
                   }
                | TyPair t1' t2' <- ts]

share (TyList a1 l1 t) ts = do
  sequence_ [ do { var ai `geq` var a1 
                    ; share t [ti] 
                   }
                | TyList ai _ ti <- ts]
  share_potential l1 (gather_all ts)
  

-- gather_potential_single:: Atype -> [Ann]
-- gather_potential_single (TyList ai (l1:xsi) ti)= l1:(gather_potential ti)

-- | to collect potential from list of lists
gather_all::[Atype] -> [[Ann]]
gather_all [] = []
gather_all l = (gather_potential l):(gather_all (shift_right l))

gather_potential::[Atype] -> [Ann]
gather_potential []= []
gather_potential ((TyList ai [] ti):ts )= []
gather_potential ((TyList ai (l1:xsi) ti):ts )= l1:(gather_potential ts)

share_potential::[Ann] -> [[Ann]] -> CLP ()
share_potential _ [] = return ()
share_potential [] _ = return ()
share_potential (a:as) (l:ls) = do 
  var a `geq` vars l
  share_potential as ls

share_potential_simple::[Ann] -> [Ann] -> [Ann]-> CLP ()
share_potential_simple an1 an2 an3| trace ("share potential simple - " ++ show an1 ++ " T2 - " ++ show an2 ++ " T3 - " ++ show an3) False = undefined
share_potential_simple _ [] _ = return ()
share_potential_simple [] _ _= return ()
share_potential_simple (a:as) (l:ls) (q:qs) = do 
  var a `geq` (var l + var q)
  share_potential_simple as ls qs

shift_right::[Atype] -> [Atype]
shift_right (l:ls)| trace ("SHIFT RIGHT - " ++ show l) False = undefined
shift_right [] = []
shift_right ((TyList ai [] ti):xs) = []
shift_right ((TyList ai (l1:xsi) ti):xs) = (TyList ai xsi ti):(shift_right xs)

-- -- | to collect potential from list of types
-- gather_all_any::[Atype] -> [[Ann]]
-- gather_all_any (l:ls)| trace ("GATHER ALL ANY - " ++ show l) False = undefined
-- gather_all_any [] = []
-- gather_all_any l = (gather_potential_any l):(gather_all_any (shift_right_any l))

-- gather_potential_any::[Atype] -> [Ann]
-- gather_potential_any (l:ls)| trace ("GATHER POT ANY - " ++ show l) False = undefined
-- gather_potential_any []= []
-- gather_potential_any ((TyList ai [] ti):ts )= []
-- gather_potential_any ((TyList ai (l1:xsi) ti):ts )= l1:(gather_potential_any [ti])++(gather_potential_any ts)
-- gather_potential_any ((TyThunk _ ti): ts) = (gather_potential_any [ti])++(gather_potential_any ts)
-- gather_potential_any ((TyFun _ t1 t2): ts) = (gather_potential_any [t1])++(gather_potential_any [t2])++(gather_potential_any ts)
-- gather_potential_any (TyVar _ : ts) = (gather_potential_any ts)
-- gather_potential_any (TyCon _ : ts) = (gather_potential_any ts)
-- gather_potential_any (TyPair t1 t2 : ts) = (gather_potential_any [t1])++(gather_potential_any [t2])++(gather_potential_any ts)

-- shift_right_single::Atype -> Atype
-- shift_right_single (TyList ai (l1:[]) ti) = (TyList ai [l1] ti) 
-- shift_right_single (TyList ai (l1:xsi) ti) = (TyList ai xsi (shift_right_single ti))
-- shift_right_single t = t

-- shift_right_any::[Atype] -> [Atype]
-- shift_right_any (l:ls)| trace ("SHIFT RIGHT ANY- " ++ show l) False = undefined
-- shift_right_any [] = []
-- --shift_right_any ((TyList ai [] ti):xs) = []
-- shift_right_any (t:xs) = (shift_right_single t):(shift_right_any xs)

-- count_out_potential::Degree -> Atype -> Atype -> CLP Atype
-- count_out_potential k t' t = do 
--   t1 <- decorate_type k t' 
--   share_potential (gather_potential_any [t1]) (gather_all_any [t', t])
--   return t1

-- | subtyping is a special case of sharing
subtype, equaltype :: Atype -> Atype -> CLP ()
t1 `subtype` t2 = share t1 [t2]

-- NB: the following is not needed 
t1 `equaltype` t2 = do t1 `subtype` t2; t2 `subtype` t1

-- | sharing a context against itself
share_self :: Acontext -> CLP ()
share_self ctx = sequence_ [share t [t,t] | (x,t)<-ctx]


-- | split a context for typing a subexpression
split_context :: Degree -> Acontext -> CLP (Acontext, Acontext)
split_context k ctx 
  = let newctx = sequence [do {t'<-decorate_type k t; return (x,t')}
                          | (x,t)<-ctx]
    in do ctx1 <- newctx
          ctx2 <- newctx
          sequence_ [ share t [t1,t2] | 
                      (t,t1,t2)<-zip3 (map snd ctx) (map snd ctx1) (map snd ctx2)]
          return (ctx1, ctx2)


-- | trim context to vars with free occurences in a term
trim_context :: Term b -> Context a -> Context a
trim_context e  
  = filter (\(x,_) -> x`Set.member`vars) . nubBy (\(x,_) (y,_) -> x==y)
  where vars = freevars e
    

-- relax cost annotations
-- if \Gamma |-p0/p0'- e : C then  \Gamma |-p/p'- e : C
relaxcost :: (LinFunc Ann Int, LinFunc Ann Int) ->
             (LinFunc Ann Int, LinFunc Ann Int) -> CLP ()
(p,p') `relaxcost` (p0,p0') = do {p `geq` p0;  (p - p0) `geq` (p' - p0')}



-- | lower recursive thunk costs on a \mu-type
-- identity for other types
-- assumes types have the same structure
lower_thunks :: Atype -> Atype -> CLP ()
-- lower_thunks (TyRec alts) (TyRec alts') 
--     = sequence_ [ do { var q `equal` var q'  -- equal potential
--                    ; zipWithM_ lower ts ts'
--                    }
--               | ((c, q, TyTup ts), 
--                  (c', q', TyTup ts')) <-zip alts alts', 
--                 c ==c'  -- must have same constructors
--               ]
--   where
--     lower (TyThunk p  TySelf) (TyThunk q TySelf) -- lower recursive thunks only
--       = do { var p `leq` var q 
--            -- ; (var p ^-^ var p') `leq` (var q ^-^ var q')
--            }
--     lower t t' = t `equaltype` t'   -- other cases 
-- ---
lower_thunks t t' = t`equaltype`t'

-- lookup a name in a context
lookupId :: Ident -> Context a -> TyExp a      
lookupId x ctx  
  = case lookup x ctx of
    Nothing -> error ("unbound identifier: "++show x)
    Just t -> t
                         
-- as above but enforces sharing and returns remaining context
lookupShare :: Degree -> Ident -> Acontext -> CLP (Atype,Acontext)
lookupShare k x ctx
  = case span (\(x',_) -> x'/=x) ctx of
    (_, []) -> error ("unbound identifier: "++show x)
    (ctx', (_,t):ctx'') -> do t1 <-decorate_type k t
                              t2 <- decorate_type k t
                              share t [t1,t2]
                              return (t1, ctx' ++ (x,t2):ctx'')


-- get a cost model constant
askC :: (CostModel -> Int) -> CLP Int
askC k = fmap k $ asks optCostModel
 
--  Amortised Analysis 
-- collects linear constraints over annotations
aa_infer :: Degree -> Acontext -> Term Atype -> Atype -> Ann -> Ann -> CLP ()
aa_infer k ctx e t p p'| trace ("INFER EXPR " ++ (show e) ++ " WITH"++ (show t) ++"\n") False = undefined
aa_infer k ctx (Nil) (TyList _ _ _) p p' 
  = var p `geq` var p'

-- Var rule
aa_infer k ctx (Var x) t p p' 
  = let TyThunk q t' = lookupId x ctx 
    in do  --pe <- fresh_ann
           ((var p - var p') - var q) `equalTo` 0
           --(var pe, var p') `relaxcost` (var q, zero)  -- allow relaxing 
           t' `subtype` t                          -- allow subtyping

-- Abs rule
-- allow prepaying for the argument
aa_infer k ctx (Lambda x e) (TyFun q t t') p p'
  = do share_self (trim_context e ctx)
       var p `geq` var p' -- allow relaxing
      --  let potential = look_for_potential t'
      --  new_type <- decorate_type k t
      --  t1 <- out_potential k new_type potential
      --  t `subtype` t1
       aa_infer_prepay k [(x,t)] ctx e t' q zero_ann


-- App rule
aa_infer k ctx (App (e :@ te) y) t0 p p'
  | TyFun q t' t <- te
  =  do (ty, ctx') <- lookupShare k y ctx 
        pe <- fresh_ann
        
        let potential = look_for_potential t
        new_type <- decorate_type k ty
        t1 <- out_potential k new_type potential
        t' `subtype` t1
        aa_infer k ctx' e (TyFun q new_type t) pe p'
        -- allow subtyping the argument and result
        ty `subtype` t'
        t `subtype` t0
        ((var p - var pe) - var q) `equalTo` 0
       
        -- allow relaxing
        --(var p, var p') `relaxcost` (var pe + var q, var pe')

-- Letcons rule (SJ's proposal with PBV fix)
aa_infer k ctx (Let x ((ConsApp c ys) :@ (TyList an pot tL)) e2) tC p p'
      = do pe <- fresh_ann
           tL'<- decorate_type k (TyList an pot tL)
           share (TyList an pot tL) [(TyList an pot tL), tL']
           (ctx1,ctx2) <- split_context k ctx
           ((var p - var pe ) - var (head pot)) `equalTo` 1
           aa_infer k ((x,TyThunk zero_ann tL'):ctx1) (ConsApp c ys) (TyList an pot tL) zero_ann zero_ann
           aa_infer k ((x,TyThunk zero_ann (TyList an pot tL)):ctx2) e2 tC pe p'
           
          
-- Let rule 
-- aa_infer k ctx (Let x (e1 :@ tA) e2) (TyFun an t1 t2) p p'
--   = do 
--        let potential = look_for_potential t2 
--        new_type <- decorate_type k t1
--        new_type1 <- out_potential k new_type potential
--        t1 `subtype` new_type1
--        tA' <- decorate_type k tA
--        share tA [tA, tA']
--        q <- fresh_ann
--        pe <- fresh_ann
--        (var p - var pe) `equalTo` 1
--        (ctx1, ctx2) <- split_context k ctx
--        aa_infer k ((x,TyThunk zero_ann tA'):ctx1) e1 tA q zero_ann
--        aa_infer_prepay k [(x,TyThunk q tA)] ctx2 e2 (TyFun an new_type t2) pe p'
       
-- Let rule 
aa_infer k ctx (Let x (e1 :@ tA) e2) tC p p'
  = do 
       tA' <- decorate_type k tA
       share tA [tA, tA']
       q <- fresh_ann
       pe <- fresh_ann
       (var p - var pe) `equalTo` 1
       (ctx1, ctx2) <- split_context k ctx
       aa_infer k ((x,TyThunk zero_ann tA'):ctx1) e1 tA q zero_ann
       aa_infer_prepay k [(x,TyThunk q tA)] ctx2 e2 tC pe p'

aa_infer k ctx (Pair x1 x2) (TyPair t1 t2) z z'
 = do (var z `geq` var z')

-- | TODO: Cons rule
aa_infer k ctx (ConsApp x1 x2) (TyList a p t) z z' 
   = do 
     var z `geq` var z'
     let tx1 = lookupId x1 ctx 
     let tx2 = lookupId x2 ctx
     case tx1 of
       TyThunk q ttype -> do
         case tx2 of 
            TyThunk ta (TyList an po ty) -> do 
              additive_shift p po
              (TyList an po ty) `subtype` (TyList a p t)
              ttype `equaltype` ty
            _ -> error "hmmmmmmmmmm"
       _ -> error "aiai"
              
         
-- | TODO: Cons rule
aa_infer k ctx (ConsApp x1 x2) t z z' = error ("Wrong type for ConsApp: "++ show t)

-- Match rule
aa_infer k ctx (Match (e0 :@ (TyList a p t0)) (ConsApp x1 x2) (e2 :@ t2) Nil  (e4 :@ t4)) t z z''
  = do new_ann <- fresh_ann
       (ctx1,ctx2) <- split_context k ctx
       p1 <- fresh_anns k
       additive_shift p p1
       let ctx' = [(x2, TyThunk a (TyList a p1 t0)),(x1, TyThunk new_ann t0)]
       pt <- fresh_ann
       z' <- fresh_ann
       (var z' + var (head p)) `geq` var pt
       aa_infer k ctx1 e0 (TyList a p t0) z z'
       aa_infer_prepay k ctx' ctx2 e2 t2 pt z''
       aa_infer k ctx2 e4 t4 z' z''
       

-- Constants           
aa_infer k ctx (Const n) t p p'   -- t must be hmint
  = var p `geq` var p' -- allow relaxing

-- user annotations and constraints
-- checking that t and t' match is done during Damas-Milner inference
aa_infer k ctx (Coerce (t,cs) e) t' p p'
  = let s = Map.fromList $ zip (annotations t) (annotations t')
        ren x = Map.findWithDefault undefined x s
    in do sequence_ [ constrain lf' bds 
                    | Constr _ lf bds <- cs, 
                      let lf' = Map.mapKeys ren lf
                    ]
          aa_infer k ctx e t' p p'


aa_infer k ctx e t p p' = error ("aa_infer: undefined for " ++ show e)

-- auxiliary function to choose the recursive type for let/letcons
-- aa_rectype k tA q = do
--   r <- asks optRecRule  -- which recursive typeing rule are we using?
--   case r of
--     0 -> return (tA, zero_ann) -- ICFP'2012 paper
--     1 -> return (tA, q)        -- Hugo's thesis
--     2 -> do t <- decorate_type k tA
--             lower_thunks t tA
--             return (t, zero_ann)  -- ESOP'2015 paper
--     _ -> error "aa_rectype: invalid optRecRule"

------------------------------------------------------------------

-- auxiliary function for match alternatives
-- allow prepaying for pattern variables
-- should improve quality over the original ICFP submission 
-- aa_infer_alts ctx alts t@(TyRec talts) t' p' p'' = mapM_ infer alts
--   where infer (c, xs, e) = do
--           pe' <- fresh_ann
--           pe'' <- fresh_ann
--           aa_infer_prepay (zip xs ts) ctx e t' pe' pe''
--           -- var pe' `equal` (var p' ^+^ var q)
--           -- (var p', var p'') `relaxcost` (var pe' ^+^ var q, var pe'')
--           var pe' `leq` (var p' + var q)
--           var pe'' `geq` var p''
--           where (q,TyTup ts) = head ([ (q, recsubst t t') 
--                                      | (c',q,t')<-talts, c'==c] ++
--                                      error ("wrong match alternative: "++show c))
-- aa_infer_alts ctx alts t t' p' p'' 
--   = error "aa_infer_alts: invalid type"


out_potential::Degree -> Atype -> [Ann] -> CLP Atype
out_potential k t p| trace ("OUT POTENTIAL " ++ (show t) ++ " " ++ (show p) ++ "\n") False = undefined

out_potential k (TyList a1 p1 t1) p2 = do
  new_potential <- fresh_anns k
  share_potential_simple new_potential p1 p2 
  new_type <- out_potential k t1 p2
  return (TyList a1 new_potential new_type)
out_potential k (TyFun a t1 t2) p2 = do
  new_type1 <- out_potential k t1 p2
  new_type2 <- out_potential k t2 p2
  return (TyFun a new_type1 new_type2)
out_potential k (TyPair t1 t2) p2 = do
  new_type1 <- out_potential k t1 p2
  new_type2 <- out_potential k t2 p2
  return (TyPair new_type1 new_type2)
out_potential k (TyThunk a t1) p2 = do
  new_type1 <- out_potential k t1 p2
  return (TyThunk a new_type1)
out_potential k (TyVar a) p2 = do
  return (TyVar a)
out_potential k (TyCon a) p2 = do
  return (TyCon a)

look_for_potential:: Atype -> [Ann]
look_for_potential t | trace ("LOOK FOR POTENTIAL " ++ (show t) ++ "\n") False = undefined
look_for_potential (TyList _ p t1)= p
look_for_potential (TyThunk _ ti) = look_for_potential ti
look_for_potential (TyFun _ t1 t2) = (look_for_potential t2)
look_for_potential (TyVar _ ) = []
look_for_potential (TyCon _ ) = []
look_for_potential (TyPair t1 t2 ) = (look_for_potential t1)++(look_for_potential t2)
--
-- allow the prepay for all variables in the first context
-- followed by type inference
aa_infer_prepay :: Degree -> Acontext -> Acontext -> 
                   Term Atype -> Atype -> Ann -> Ann -> CLP ()
aa_infer_prepay k ((x,t) : ctx1) ctx2 e t' p p'  | trace ("INFER PREPAY " ++ (show t) ++ "\n") False = undefined
aa_infer_prepay k [] ctx e t' p p' = aa_infer k ctx e t' p p'
aa_infer_prepay k ((x,TyThunk q t) : ctx1) ctx2 e t' p p'
  = do q0 <- fresh_ann
       q1 <- fresh_ann
       p0 <- fresh_ann
       var q `equal` (var q0 + var q1)
       var p `equal` (var p0 + var q1)
       aa_infer_prepay k ctx1 ((x,TyThunk q0 t):ctx2) e t' p0 p'
aa_infer_prepay k ctx _ e t' p p'
  = error ("aa_infer_prepay: invalid context\n " ++ show ctx)

               
-- auxiliary Cons-rule used at the Letcons 
-- given both context *and* the result type 
-- turnstile annotations are ommitted (always 0)
-- aa_infer_cons ctx (ConsApp c ys) tB
--   | length ys == length ts'    -- should always hold
--   = do (ts, _) <- lookupMany ys ctx
--        sequence_ [t `subtype` t' | (t,t')<-zip ts ts']
--     where TyRec talts = tB    -- pattern-match result type
--           TyTup ts' = head [recsubst tB t' | (c',_,t')<-talts, c'==c]
-- aa_infer_cons ctx _ tB = error "aa_infer_cons: invalid argument"          
        
-- lookup and share many identifiers in sequence
lookupMany :: Degree -> [Ident] -> Acontext -> CLP ([Atype], Acontext)
lookupMany k [] ctx = return ([],ctx)
lookupMany k (x:xs) ctx 
  = do (t, ctx') <- lookupShare k x ctx
       (ts, ctx'')<- lookupMany k xs ctx'
       return (t:ts, ctx'')


-- leave only type annotations for let-bindings
let_annotations :: Term a -> Term a
let_annotations (Let x (e1 :@ t1) e2)
  = Let x (let_annotations e1 :@ t1) (let_annotations e2)
let_annotations (Let x e1 e2) 
  = Let x (let_annotations e1) (let_annotations e2)
let_annotations (Lambda x e)     
  = Lambda x (let_annotations e)
let_annotations (Match e0 e1 e2 e3 e4)
  = Match (let_annotations e0) (let_annotations e1) (let_annotations e2) (let_annotations e3) (let_annotations e4)
let_annotations (App e y) 
  = App (let_annotations e) y
let_annotations (Var x)          = Var x    
let_annotations (ConsApp x1 x2)   = ConsApp x1 x2    
let_annotations (Pair x1 x2)   = Pair x1 x2 
let_annotations (Const n)        = Const n
let_annotations Nil       = Nil
let_annotations (Coerce a e)     = Coerce a (let_annotations e) 
let_annotations (e :@ a)         = let_annotations e

env = [("app'",(TyThunk 0 (TyFun 0 (TyThunk 0 (TyVar "B")) (TyFun 0 (TyThunk 0 (TyList 0 [1,0] (TyVar "B"))) (TyList 0 [0,0] (TyThunk (0) (TyVar "B"))))))),("attach", (TyThunk 0 (TyFun (0) (TyThunk 0 (TyVar "A")) (TyFun (0) (TyThunk 0 (TyList 0 [1, 0] (TyVar "A"))) (TyList (0) [3, 0] (TyThunk (0) (TyPair (TyThunk (0) (TyVar "A")) (TyThunk (0) (TyVar "A")))))))))]

-- | toplevel inference 
-- generates a typing \Gamma |-p/p'- e : C 
-- and a linear program for constraints over annotations
-- set p'=0 and solves to minimize p (i.e. the whnf cost of the expression)
aa_inference :: Degree -> Options -> Term HMtype -> HMtype -> (Typing Ann, LP Ann Int)
aa_inference degree opts e t
  = flip runReader opts $
    flip evalStateT (Ann 1) $
    runLPT $ 
     do { varEq zero_ann 0
        ; p <- fresh_ann
        ; e'<- decorate_term degree e
        ; t'<- decorate_type degree t
        ; setDirection Min
        ; setObjective  (vars (p:annotations t'))
        ; aa_infer degree [] e' t' p zero_ann
        ; return Typing {aterm = let_annotations e', 
                         atype = t', 
                         ann_in  = p, 
                         ann_out = zero_ann}
        }


-- | solve linear constraints and instantiate annotations
aa_solve :: (Typing Ann, LP Ann Int) -> IO (Typing Double)
aa_solve (typing, lp) 
  = do print typing
       answer <- glpSolveVars simplexDefaults{msgLev=MsgOff} lp 
       case answer of
         (Success, Just (obj, vars)) -> 
           let subst a = Map.findWithDefault 0 a vars
           in return (fmap subst typing)
         (other, _) -> error ("LP solver failed: " ++ show other)
