module Simple

data Typ : Type where
  NatT : Typ
  FunT : Typ -> Typ -> Typ

data Thinning : List a -> List a -> Type where
  Id : Thinning [] []
  Keep : Thinning (a :: as) (a :: as)
  Disc : Thinning (a :: as) as

Ctxt : Type
Ctxt = List Typ

mutual
  data Synth : Ctxt -> Typ -> Type where
    Var : {Γ : Ctxt} -> Thinning Γ [t] -> Synth Γ t
    App : {Γ : Ctxt} -> Synth Γ (FunT d c) -> Check Γ d -> Synth Γ c
    Rec : {Γ : Ctxt} -> (x : Typ) -> Check Γ x -> Check Γ (FunT x x) -> Check Γ NatT -> Synth Γ x
    Ann : {Γ : Ctxt} -> (x : Typ) -> Check Γ x -> Synth Γ x
  
  data Check : Ctxt -> Typ -> Type where
    Lam : {Γ : Ctxt} -> Check (d :: Γ) c -> Check Γ (FunT d c)
    Zer : {Γ : Ctxt} -> Check Γ NatT
    Suc : {Γ : Ctxt} -> Check Γ (FunT NatT NatT)
    Syn : {Γ : Ctxt} -> Synth Γ x -> Check Γ x

data Ast =
    Var String
  | Lam String Ast
  | App Ast Ast
  | Zer
  | Suc Ast
  | Ann Typ Ast
