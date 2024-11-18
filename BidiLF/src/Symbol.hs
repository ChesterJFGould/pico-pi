module Symbol where

data Symbol = Symbol String
  deriving (Eq, Ord)

instance Show Symbol where
  show (Symbol x) = x
