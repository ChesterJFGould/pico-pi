module NbEALaCarte

import ALaCarte

Env : Type -> Type
Env a = List (String, a)

data VarF : Type -> Type where
  Var : String -> VarF e

data FunF : Type -> Type where
  Lam : String -> e -> FunF e
  App : e -> e -> FunF e

data VarEF : Type -> Type where
  NVar : String -> VarNeF a

data FunEF : Type -> Type -> Type where
  NApp : e -> nf -> FunNeF e nf

data FunCF : Type -> Type -> Type where
  NLam : String -> e -> Env v -> FunNfF e v

mutual
  ExpF : Type -> Type
  ExpF = OneOf [VarF, FunF]

  Exp : Type
  Exp = Fix ExpF

  NeF : Type -> Type
  NeF = OneOf [VarNeF, FunNeF Nf]
  
  Ne : Type
  Ne = Fix NeF
  
  NfF : Type -> Type
  NfF = OneOf [FunNfF Exp]

  Nf : Type
  Nf = Fix NfF

interface Functor e => Rf e ne nf v where
  eval : e v -> v
  reify : v -> nf
