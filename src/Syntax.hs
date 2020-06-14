{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable
#-}

module Syntax where
import qualified Data.Map as Map

newtype Location = Location Int deriving (Eq, Ord, Num)
instance Show Location where
    show (Location n) = 'l' : (show n)

newtype Variable = Variable Int deriving (Eq, Ord, Num)
instance Show Variable where
    show (Variable n) = 'v' : (show n)

newtype Ann = Ann Int deriving (Eq, Ord, Num, Enum)
instance Show Ann where
    show (Ann n) = 'a' : (show n)

type VariableT = String 
data Expression = NilE 
     | ConstE Int
     | VarE VariableT
     | LambdaE VariableT Expression 
     | AppE Expression VariableT
     | LetE VariableT Expression Expression
     | ConsE VariableT VariableT
     | LetconsE VariableT Expression Expression
     | MatchE Expression Expression Expression Expression Expression
     deriving(Show)

data Type a = Prim  
     | VarT VariableT
     | Func (Type a) (Type a) a 
     | Thunk (Type a) a
     | List (Type a) a [a]
     deriving(Eq, Show)

type HMType = Type () -- Hinldey Milner Types without annotations
type AnnType = Type Ann -- Annotated types


    
