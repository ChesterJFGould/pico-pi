module TExpr where

data Var = Var String Integer deriving Show

instance Eq Var where
  (Var _ a) == (Var _ b) = a == b

data Check =
    Lam Var Check
  | LZero
  | LSucc Check
  | LMax Check Check
  | Synth Synth
  deriving (Eq, Show)

data Synth =
    VarE Var
  | App Synth Check
  | Pi Var Synth Synth
  | Eq Synth Check Check
  | Level Integer
  | Type Integer Check
  | LetEq Var Var Synth Synth
  | Check Check Synth
  deriving (Eq, Show)

type Expr = Synth
