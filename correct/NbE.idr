module NbE

data Typ : Type where
  NatT : Typ
  FunT : Typ -> Typ -> Typ

mutual
  data Exp : (0 a : Typ) -> Type where
    NatLit : Nat -> Exp NatT
    Var : (r : Rf a) => String -> Exp a
    Lam : (Exp a -> Exp b) -> Exp (FunT a b)
    App : Rf a => Rf b => Exp (FunT a b) -> Exp a -> Exp b

  data Ne : (0 a : Typ) -> Type where
    NVar : Rf a => String -> Ne a
    NApp : Rf a => Rf b => Ne (FunT a b) -> Nf a -> Ne b

  data Nf : (0 a : Typ) -> Type where
    NLam : (Exp a -> Nf b) -> Nf (FunT a b)
    NNatLit : Nat -> Nf NatT
    NNe : Ne a -> Nf a

  Sem : Typ -> Type
  Sem (NatT) = Either (Ne NatT) Nat
  Sem (FunT d c) = Sem d -> Sem c

  interface Rf (0 a : Typ) where
    eval : Exp a -> Sem a
    reify : Sem a -> Nf a
    reflect : Ne a -> Sem a

mutual
  embNe : Ne a -> Exp a
  embNe (NVar x) = Var x
  embNe (NApp f a) = App (embNe f) (embNf a)

  embNf : Nf a -> Exp a
  embNf (NNatLit n) = NatLit n
  embNf (NLam f) = Lam (embNf . f)
  embNf (NNe n) = embNe n

(Rf a, Rf b) => Rf (FunT a b) where
  eval (Var {r} x) = reflect @{r} (NVar x)
  eval (App f x) = (eval f) (eval x)
  eval (Lam f) = \x => eval (f (embNf (reify x)))

  reflect n = \x => reflect (NApp n (reify x))

  reify f = NLam (reify . f . eval)

Rf NatT where
  eval (NatLit n) = Right n
  eval (Var x) = Left (NVar x)
  eval (App f a) = (eval f) (eval a)

  reflect = Left

  reify (Right n) = NNatLit n
  reify (Left n) = NNe n
