-- 
-- Main module for lazy amortized analysis
-- pbv, 2012--2015
--
module Main where

import           Term
import Types
--import           Parser
import           DamasMilner
import           Analysis
import           Options
import           Data.Set (Set)
import           Cost
import           Text.Parsec
import           System.Exit
import           System.Environment
import           Data.LinearProgram
import qualified Data.Map as Map
 
      
-- main k = do arg0 <- getProgName 
--           argv <- getArgs
--           (opts, argv') <- parseOpts arg0 argv
--           case argv' of
--             [] ->  do txt<-getContents
--                       analyse k opts (runParser toplevel 0 "stdin" txt)
--             (f:_) -> do txt<-readFile f 
--                         analyse k opts (runParser toplevel 0 f txt)
               

-- analyse k opts (Left err) = print err >> exitFailure
-- analyse k opts (Right e') 
--   = case hm_inference e' of
--   Right (e :@ t) -> do 
--           putStrLn ""
--           putStrLn "-- Amortised type analysis " 
--           putStrLn ("-- Cost model: " ++ show (costName $ optCostModel opts))
--           let (typ, lp) = aa_inference k opts e t
--           putStrLn "-- LP metrics follow"
--           putStrLn ("--  # constraints: " ++ show (length $ constraints lp))
--           putStrLn ("--  # variables  : " ++ show (Map.size $ allVars lp))
--           putStrLn ""
--           putStrLn "-- Invoking LP solver"
--           typ' <- aa_solve (typ,lp)
--           putStrLn "\n-- Annotated typing"
--           print typ'
--   Left err -> putStrLn err >> exitFailure
-- (Let "f" (Const 1) (Let "n" Nil (Let "x" (ConsApp "f" "n") (Match (Term.Var "x") (ConsApp "x1" "x2") (Term.Var "x") (Nil) (Nil) ))))
main =
  case hm_inference app' of 
    Right (e :@ t) -> do 
          print e 
          print t
          putStrLn ""
          putStrLn "-- Amortised type analysis " 
          putStrLn ("-- Cost model: " ++ show (costName $ optCostModel Options.defaultOptions))
          let (typ, lp) = aa_inference 2 Options.defaultOptions e t
          print typ
          putStrLn "-- LP metrics follow"
          putStrLn ("--  # constraints: " ++ show (length $ constraints lp))
          putStrLn ("--  # variables  : " ++ show (Map.size $ allVars lp))
          putStrLn ""
          putStrLn "-- Invoking LP solver"
          typ' <- aa_solve (typ,lp)
          putStrLn "\n-- Annotated typing"
          print typ'
    Left err -> putStrLn err >> exitFailure

-- attach = λn. λl . match l k 1 with
-- nil->nil
-- cons(x, xs j 1 )-> let p = (x, n); f = attach n xs n 1
-- in cons(p, f )

attach = (Let "attach" (Lambda "n" (Lambda "l" (Match (Term.Var "l") (ConsApp "x" "xs") (Let "p" (Pair "x" "n") (Let "f" (App (App (Term.Var "attach") "n") "xs") (ConsApp "p" "f"))) (Nil) (Nil) ))) (Term.Var "attach"))

app' = (Let "app'" (Lambda "l1" (Lambda "l2" (Match (Term.Var "l2") (ConsApp "x" "xs") (Let "f" (App (App (Term.Var "app'") "l1") ("xs")) (ConsApp "x" "f")) (Nil) (Term.Var "l1"))) ) (Term.Var "app'"))

--attach_app = (Let "attach" (Lambda "n" (Lambda "l" (Match (Term.Var "l") (ConsApp "x" "xs") (Let "p" (ConsApp "x" "n") (Let "f" (App (Term.Var "n") "xs") (ConsApp "p" "f"))) (Nil) (Nil) ))) (Let "app'" (Lambda "l1" (Lambda "l2" (Match (Term.Var "l2") (ConsApp "x" "xs") (Let "f" (App (App (Term.Var "app'") "l1") ("xs")) (ConsApp "x" "f")) (Nil) (Var "l1"))) ) (Term.Var "app'")))

--(Let "pairs "(Lambda "list" (Match (Term.Var "list") (ConsApp "x2" "xs2" ) (Let "f1" (App (Var "pairs") "xs2") (Let "f2" (App (App (Var "attach") "x2") "xs2") (App (App (Term.Var "f1") "f1") "f2")) (Nil) (Nil))) (Term.Var "pai"))

--(Let "attach" (Lambda "n" (Lambda "l" (Match (Term.Var "l") (ConsApp "x" "xs") (Let "p" (ConsApp "x" "n") (Let "f" (App (Term.Var "n") "xs") (ConsApp "p" "f"))) (Nil) (Nil) ))) (Let "app'" (Lambda "l1" (Lambda "l2" (Match (Term.Var "l2") (ConsApp "x1" "xs1") (Let "fn" (App (App (Term.Var "app'") "l1") ("xs1")) (ConsApp "x1" "fn")) (Nil) (Term.Var "l1"))) ) (Let "pairs "(Lambda "list" (Match (Term.Var "list") (ConsApp "x2" "xs2" ) (Let "f1" (App (Term.Var "pairs") "xs2") (Let "f2" (App (App (Term.Var "attach") "x2") "xs2") (App (App (Term.Var "app'") "f1") "f2"))) (Nil) (Nil))) (Term.Var "pairs"))))

pairs = (Let "attach" (Lambda "n" (Lambda "l" (Match (Term.Var "l") (ConsApp "x" "xs") (Let "p" (Pair "x" "n") (Let "f" (App (App (Term.Var "attach") "n") "xs") (ConsApp "p" "f"))) (Nil) (Nil) ))) (Let "app'" (Lambda "l1" (Lambda "l2" (Match (Term.Var "l2") (ConsApp "x1" "xs1") (Let "fn" (App (App (Term.Var "app'") "l1") ("xs1")) (ConsApp "x1" "fn")) (Nil) (Term.Var "l1"))) ) (Let "pairs" (Lambda "list" (Match (Term.Var "list") (ConsApp "x2" "xs2" ) (Let "f1" (App (Term.Var "pairs") "xs2") (Let "f2" (App (App (Term.Var "attach") "x2") "xs2") (App (App (Term.Var "app'") "f1") "f2"))) (Nil) (Nil))) (Term.Var "pairs"))))

pairs1 = (Let "pairs" (Lambda "list" (Match (Term.Var "list") (ConsApp "x2" "xs2" ) (Let "f1" (App (Term.Var "pairs") "xs2") (Let "f2" (App (App (Term.Var "attach") "x2") "xs2") (App (App (Term.Var "app'") "f1") "f2"))) (Nil) (Nil))) (Term.Var "pairs"))

--(TyTyhunk 0 (TyFun 0 (TyThunk 0 (TyVar "t1")) (TyFun 0 (TyThunk 0 (TyList 0 [1,0] (TyVar "t4"))) (TyList 0 [0,0] (TyThunk (0) (TyVar "t4"))))))

new_pairs = (Coerce Main.constrain (Let "attach" (Lambda "n" (Lambda "l" (Match (Term.Var "l") (ConsApp "x" "xs") (Let "p" (Pair "x" "n") (Let "f" (App (App (Term.Var "attach") "n") "xs") (ConsApp "p" "f"))) (Nil) (Nil) ))) (Let "app'" (Lambda "l1" (Lambda "l2" (Match (Term.Var "l2") (ConsApp "x1" "xs1") (Let "fn" (App (App (Term.Var "app'") "l1") ("xs1")) (ConsApp "x1" "fn")) (Nil) (Term.Var "l1"))) ) (Let "pairs" (Lambda "list" (Match (Term.Var "list") (ConsApp "x2" "xs2" ) (Let "f1" (App (Term.Var "pairs") "xs2") (Let "f2" (App (App (Term.Var "attach") "x2") "xs2") (App (App (Term.Var "app'") "f1") "f2"))) (Nil) (Nil))) (Term.Var "pairs")))))

uau :: LinFunc Ann Int
uau = linCombination []

hm= (Constr Nothing (linCombination [(1, "a304")]) (Equ 1))

constrain = ((Types.TyFun "a302" (Types.TyThunk "a303" (Types.TyList "a304" ["a305","a306"] (Types.TyVar "t1"))) (Types.TyList "a307" ["a308","a309"] (Types.TyThunk "a310" (Types.TyThunk "a311" (Types.TyPair (Types.TyThunk "a313" (Types.TyVar "t1")) (Types.TyThunk "a314" (Types.TyVar "t1"))))))), [hm])