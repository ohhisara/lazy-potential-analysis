module Evaluation where

    import Syntax 
    import Control.Monad.State
    import Data.Map as Map
    import Debug.Trace

    type Heap = Map Location Expression
    type BoundSet = [VariableT]
  
    data EvalMembers = EvalMembers {
        heap::Heap
        ,location::Location
    } deriving(Show)

    type (EvalState a) = State EvalMembers a 

    freshLocation :: EvalState Location
    freshLocation = do
        thisState <- get
        put thisState{location = (location thisState) + 1}
        return (location thisState)

    addToLocations::Location -> EvalState ()
    addToLocations l | trace ("Add to location"++(show l)) False = undefined
    addToLocations l = do
        state <- get 
        put state{location = l}
        
    addToHeap::Location -> Expression -> EvalState ()
    addToHeap l e | trace ("Add to heap" ++ (show l)++(show e)) False = undefined
    addToHeap l e = do 
        state <- get 
        put state{heap = Map.insert l e (heap state)}

    replaceVar::VariableT -> Location -> Expression -> Expression
    replaceVar s l w | trace ("Replace var "++(show s)++(show l)++(show w)) False = undefined
    replaceVar s l NilE = NilE 
    replaceVar s l (ConstE c) = (ConstE c) 
    replaceVar s l (PairE v1 v2)
        | v1 == s = (PairE (show l) v2)
        | v2 == s = (PairE v1 (show l))
        | otherwise = (PairE v1 v2) 
    replaceVar s l (ConsE v1 v2) 
        | v1 == s = (ConsE (show l) v2)
        | v2 == s = (ConsE v1 (show l))
        | otherwise = (ConsE v1 v2) 
    replaceVar s l (VarE v) 
        | s == v = (VarE  (show l))
        | otherwise = (VarE v)
    replaceVar s l (LambdaE x e)  
        | s == x = LambdaE (show l) (replaceVar s l e)
        | otherwise = LambdaE x (replaceVar s l e)
    replaceVar s l (AppE e1 l1)
        | s == l1 = AppE (replaceVar s l e1) (show l)
        | otherwise = AppE (replaceVar s l e1) l1
    replaceVar s l (LetE x e1 e2) 
        | s == x = LetE (show l) (replaceVar s l e1) (replaceVar s l e2)
        | otherwise = LetE x (replaceVar s l e1) (replaceVar s l e2)
    replaceVar s l (LetconsE x e1 e2)
     | s == x = LetconsE (show l) (replaceVar s l e1) (replaceVar s l e2)
     | otherwise = LetconsE x (replaceVar s l e1) (replaceVar s l e2)    
    replaceVar s l (MatchE e0 e1 e2 e3 e4) = MatchE (replaceVar s l e0) (replaceVar s l e1) (replaceVar s l e2) (replaceVar s l e3) (replaceVar s l e4)
    --replaceVar s l e = error ("Non-exaustive"++(show s)++(show l)++(show e))

    boundVars:: Expression -> BoundSet
    boundVars (LambdaE x lambda) = x:(boundVars lambda)
    boundVars (AppE l1 l) = (boundVars l1)
    boundVars (LetE s e1 e2) = (boundVars e1)++(boundVars e2)
    boundVars (LetconsE s e1 e2) = (boundVars e1)++(boundVars e2)
    boundVars (MatchE e0 e1 e2 e3 e4) = (boundVars e0)++(boundVars e1)++(boundVars e2)++(boundVars e3)++(boundVars e4)
    boundVars _ = []

    varToLoc::VariableT -> Location 
    --varToLoc v | trace ("Var to loc"++(show v)) False = undefined
    varToLoc v 
        | (head v) == 'l' = Location (read (tail v))
        | otherwise = (Location 777)

    eval::Expression -> BoundSet ->EvalState Expression 
    eval e s | trace (show e) False = undefined
    eval NilE _ = return NilE
    eval (ConstE n) _ = return (ConstE n)
    eval (PairE n1 n2) _ = return (PairE n1 n2)
    eval (LambdaE s e) _  = return (LambdaE s e) 
    eval (ConsE v1 v2) _ = return (ConsE v1 v2)
    eval (VarE v) b = do 
        state <- get 
        case Map.lookup (varToLoc v) (heap state) of 
            Just e -> do
                --addToLocations (varToLoc v)
                w <- eval e b
                addToHeap (varToLoc v) w 
                return w
            Nothing -> error "Location not in heap."

    eval (LetE x e1 e2) b = do 
        newL <- freshLocation
        addToHeap newL (replaceVar x newL e1)
        eval (replaceVar x newL e2) b 
        --return w 

    eval (LetconsE x (ConsE xh xt) e1) b = do 
        newL <- freshLocation
        addToHeap newL (replaceVar x newL (ConsE xh xt))
        eval (replaceVar x newL e1) b 
        --return w

    eval (AppE e l) b = do
        w <- eval e b 
        case w of 
            (LambdaE x e1) -> do 
                let newExp = (replaceVar x (varToLoc l) e1)
                eval newExp b
                --return w'
            _ -> error "App body is not a lambda."

    eval (MatchE e0 NilE e1 (ConsE xh xt) e2) b = do 
        let newBound = (boundVars e1)++(boundVars e2)
        cons <- eval e0 newBound
        case cons of 
            (ConsE h t) -> eval (replaceVar xt (varToLoc t) (replaceVar xh (varToLoc h) e2)) b
            NilE -> eval e1 b
            _ -> error ("Unable to match with constructor or nil. "++(show cons))
            
    initState = EvalMembers {heap = Map.empty, location = 0}
    initBound = []

    ex = (LambdaE "x" (VarE "x"))
    ex1 = (LetE "s" (ConstE 1) (AppE (LambdaE "x" (VarE "x")) "s"))
    ex2 = (LetE "um" (ConstE 1) (LetE "dois" (ConstE 2) (LetE "nil" (NilE) (LetconsE "ist" (ConsE "dois" "nil") (LetconsE "ist1" (ConsE "um" "ist") (VarE "ist1"))))))
    

    --PAIRS EXAMPLE
    --Aux function attach
    attach = (LetE "attach" (LambdaE "n" (LambdaE "l" (MatchE (VarE "l") (NilE) (NilE) (ConsE "x" "xs") (LetE "p1" (PairE "n" "x") (AppE (AppE (VarE "attach") "x") "xs"))))) (VarE "attach")) 
    --Apply attach to arguments
    attach1 = (LetE "attach" 
        (LambdaE "n" (LambdaE "pf" 
            (MatchE (VarE "pf") (NilE) (NilE) 
            (ConsE "x" "xs") (LetE "p1" (PairE "x" "n") 
                (LetE "func"  (AppE (AppE (VarE "attach") "x") "xs")
                    ((ConsE "p1" "func"))))))) 
        (LetE "um" (ConstE 1) (LetE "dois" (ConstE 2) 
            (LetE "nil" (NilE) (LetconsE "ist" (ConsE "dois" "nil") 
                (LetconsE "ist1" (ConsE "um" "ist") 
                    (AppE (AppE (VarE"attach") "um") "ist1"))))))) 

    attach2 = (LetE "um"  (ConstE 1) (LetE "dois" (ConstE 2) 
        (LetE "nil" (NilE) (LetconsE "ist" (ConsE "dois" "nil")
            (LetconsE "ist1" (ConsE "um" "ist") 
                (AppE ((LambdaE "n" (LambdaE "pf" 
                    (MatchE (VarE "pf") 
                        (NilE) (NilE) 
                        (ConsE "x" "xs") (LetE "p1" (PairE "x" "n") 
                                (LetE "func"  (AppE (AppE (VarE "attach") "x") "xs")
                                    (LetconsE "final" (ConsE "p1" "func") (VarE "final")))))))) ("ist1")))))))



    main::IO()
    main = print $ runState (eval attach1 initBound) initState   