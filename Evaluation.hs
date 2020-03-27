module Evaluation where

    import Syntax 
    import Control.Monad.State
    import Data.Map as Map

    type Heap = Map Location Expression
    type BoundSet = [Variable]
  
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
    addToLocations l = do
        state <- get 
        put state{location = l}
        
    addToHeap::Location -> Expression -> EvalState ()
    addToHeap l e = do 
        state <- get 
        put state{heap = Map.insert l e (heap state)}

    replaceVar::Variable -> Location -> Expression -> Expression
    replaceVar (Variable s) (Location l ) (VarE v) 
        | (Variable s) == v = (VarE (Variable l))
        | otherwise = (VarE v)
    replaceVar s l (LambdaE x e) = LambdaE x (replaceVar s l e) 
    replaceVar s l (AppE e1 l1) = AppE (replaceVar s l e1) l1
    replaceVar s l (LetE x e1 e2) = LetE x (replaceVar s l e1) (replaceVar s l e2)

    boundVars:: Expression -> BoundSet
    boundVars (LambdaE x lambda) = x:(boundVars lambda)
    boundVars (AppE l1 l) = (boundVars l1)
    boundVars (LetE s e1 e2) = (boundVars e1)++(boundVars e2)
    boundVars (LetconsE s e1 e2) = (boundVars e1)++(boundVars e2)
    boundVars (MatchE e0 e1 e2 e3 e4) = (boundVars e0)++(boundVars e1)++(boundVars e2)++(boundVars e3)++(boundVars e4)
    boundVars _ = []

    eval::Expression -> BoundSet ->EvalState Expression 
    eval (LambdaE s e) _  = return (LambdaE s e) 

    eval (VarE v) b = do 
        state <- get 
        case Map.lookup v (heap state) of 
            Just e -> do
                addToLocations v
                w <- eval e b
                addToHeap v w 
                return w
            Nothing -> error "Location not in heap."

    eval (LetE x e1 e2) b = do 
        newL <- freshLocation
        addToHeap newL (replaceVar x newL e1)
        w <- eval (replaceVar x newL e2) b 
        return w 

    eval (LetconsE x (ConsE xh xt) e1) b = do 
        newL <- freshLocation
        addToHeap newL (ConsE xh xt)
        w <- eval (replaceVar x newL e1) b 
        return w

    eval (AppE e l) b = do
        w <- eval e b 
        state <- get
        case w of 
            (LambdaE x e1) -> do 
                w' <- eval (replaceVar x l e1) b
                return w'
            _ -> error "App body is not a lambda."

    eval (MatchE e0 NilE e1 (ConsE xh xt) e2) b = do 
        let newBound = (boundVars e1)++(boundVars e2)
        cons <- eval e0 newBound
        case cons of 
            (ConsE h t) -> eval (replaceVar xt t (replaceVar xh h e2)) b
            NilE -> eval e1 b
            _ -> error "Unable to match with constructor or nil."