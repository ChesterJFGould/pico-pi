module Algebra


{- Monoid Algebra:
 - id : a
 - (+) : a -> a -> a
 - id + x = x
 - x + id = x
 - x + (y + z) = (x + y) + z
 -}

record MonoidAlg (0 a : Type) where
  constructor MkMonoidAlg
  id : a
  add : a -> a -> a

data InitialMonoid : Type where
  Id : InitialMonoid
  Add : InitialMonoid -> InitialMonoid -> InitialMonoid

initialMonoidAlg : MonoidAlg InitialMonoid
initialMonoidAlg = MkMonoidAlg Id Add

(alg : MonoidAlg a) => Cast InitialMonoid a where
  cast Id = alg.id
  cast (Add l r) = alg.add (cast l) (cast r)

FinalMonoid : Type
FinalMonoid = Unit

finalMonoidAlg : MonoidAlg FinalMonoid
finalMonoidAlg = MkMonoidAlg () (\_, _ => ())

(alg : MonoidAlg a) => Cast a FinalMonoid where
  cast _ = ()

{-
record FinalMonoid where
  constructor MkFinalMonoid
  0 t : Type
  alg : MonoidAlg t

finalMonoidAlg : MonoidAlg FinalMonoid
finalMonoidAlg = MkMonoidAlg 

(alg : MonoidAlg a) => Cast a FinalMonoid where
  cast _ = MkFinalMonoid a alg.id alg.add

natAddMonoid : MonoidAlg Nat
natAddMonoid = MkMonoidAlg 0 (+)
-}
