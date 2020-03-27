{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards,
             DeriveFunctor, DeriveFoldable, DeriveTraversable
#-}

module Syntax where
    newtype Location = Location Int deriving (Eq, Ord, Num)
    instance Show Location where
        show (Location n) = 'a' : (show n)

    newtype Variable = Variable Int deriving (Eq, Ord, Num)
    instance Show Variable where
        show (Variable n) = 'a' : (show n)

    data Expression = NilE 
     | ConstE Int
     | VarE Variable
     | LambdaE Variable Expression 
     | AppE Expression Location
     | LetE Variable Expression Expression
     | ConsE Variable Variable
     | LetconsE Variable Expression Expression
     | MatchE Expression Expression Expression Expression Expression
     deriving(Show)