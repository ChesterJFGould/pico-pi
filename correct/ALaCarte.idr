module ALaCarte

import Deriving.Functor

%language ElabReflection

public export
data (:+:) : (0 f : Type -> Type) -> (0 g : Type -> Type) -> (Type -> Type) where
  Inl : f e -> (:+:) f g e
  Inr : g e -> (:+:) f g e

export
infixl 8 :+:

export
Functor f => Functor g => Functor (f :+: g) where
  map fun (Inl d) = Inl (map fun d)
  map fun (Inr d) = Inr (map fun d)

public export
data OneOf : List (Type -> Type) -> Type -> Type where
  Next : OneOf l e -> OneOf (f :: l) e
  This : f e -> OneOf (f :: l) e

public export
data FunctorList : List (Type -> Type) -> Type where
  NilF : FunctorList []
  ConsF : Functor f => FunctorList l -> FunctorList (f :: l)

export
(fl : FunctorList l) => Functor (OneOf l) where
  map f (Next oo) with (fl)
    _ | ConsF _ = Next (map f oo)
  map f (This d) with (fl)
    _ | ConsF _ = This (map f d)

public export
data Fix : (0 f : Type -> Type) -> Type where
  In : f (Fix f) -> Fix f
export
fixFold : Functor f => (f a -> a) -> Fix f -> a
fixFold f (In d) = f (map (fixFold f) d)

export
interface (:<:) (0 f : Type -> Type) (0 g : Type -> Type) where
  inj : f a -> g a

infix 6 :<:

export
(:<:) f (OneOf (f :: l)) where
  inj = This

export
(:<:) f (OneOf l) => (:<:) f (OneOf (g :: l)) where
  inj = Next . inj

export
inject : (g :<: f) => g (Fix f) -> Fix f
inject = In . inj

{-
data NatF : Type -> Type where
  NatLit : Nat -> NatF a
  NatAdd : a -> a -> NatF a

natFunctor : Functor NatF
natFunctor = %runElab derive

data StrF : Type -> Type where
  StrLit : String -> StrF a
  StrAdd : a -> a -> StrF a

strFunctor : Functor StrF
strFunctor = %runElab derive

ExprF : Type -> Type
ExprF = OneOf [NatF, StrF]

Expr : Type
Expr = Fix ExprF
-}
