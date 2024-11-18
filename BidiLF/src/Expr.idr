module Expr

import Data.List.Quantifiers

data Symbol = MkSymbol String

mutual
  -- convert to PHOAS
  data Expr =
      Var Symbol
    | App Symbol (List Binding)
  
  data Binding = BindingArgs (List Symbol) Expr | BindingExpr Expr

data Params a = MkParams (List (Symbol, a))

mutual
  data Kind =
      Constructor ConsType
    | Destructor DestType
    | Sort SortType
    | Meta MetaType
    | VarT Expr

  data ConsType = MkConsT (Params MetaType) (Params MetaType) Expr

  data DestType = MkDestT (Params MetaType) (Params Expr) (Params MetaType) Expr

  data SortType = MkSortT (Params MetaType)

  data MetaType = MkMetaT (Params Expr) Expr

data ExprEq : 

data Check : (V : Symbol -> Kind -> Type) -> Expr -> Expr -> Type where
  ConsVar : v x (Constructor (MkConsT params (MkParams []) pat)) -> Unif pat a res -> Check v (Var x) a

data Synth : (V : Symbol -> Kind -> Type) -> Expr -> Expr -> Type where
  SynthVar : v x (VarT a) -> Synth v (Var x) a
  MetaVar : v x (Meta (MkMetaT (MkParams []) a)) -> Synth v (Var x) a

data DecErr msg a = Yes a | No msg (Not a)

data TypeError = UnboundVariable Symbol

record Env (V : Symbol -> Kind -> Type) where
  constructor MkEnv
  kind : (x : Symbol) -> Dec (k : Kind ** V x k)

total
notVar : {V : Symbol -> Kind -> Type} -> Not (k : Kind ** V x k) -> (a : Expr ** Synth V (Var x) a) -> Void
notVar no (a ** SynthVar v) = no (VarT a ** v)
notVar no (a ** MetaVar v) = no (Meta (MkMetaT (MkParams []) a) ** v)

mutual
  total
  check : {V : Symbol -> Kind -> Type} -> (e : Expr) -> (A : Expr) -> Env V -> DecErr TypeError (Check V e A)
  check = _
  
  total
  synth : {V : Symbol -> Kind -> Type} -> (e : Expr) -> Env V -> DecErr TypeError (A : Expr ** Synth V e A)
  synth (Var x) env with (env.kind x)
    _ | Yes ((VarT a) ** v) = Yes (a ** SynthVar v)
    _ | Yes ((Meta (MkMetaT (MkParams []) a)) ** v) = Yes (a ** MetaVar v)
    _ | No no = No (UnboundVariable x) (notVar no)
  synth (App _ _) env = No (UnboundVariable (MkSymbol "x")) (
