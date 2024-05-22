module FAlgebra

data MonoidF : (0 a : Type) -> Type where
  Id : MonoidF a
  Add : a -> a -> MonoidF a

record MonoidAlg (0 t : Type) where
  constructor MkMonoidAlg
  alg : MonoidF t -> t

data InitMonoid : Type where
  IdI : InitMonoid
  AddI : InitMonoid -> InitMonoid -> InitMonoid

initMonoidAlg : MonoidF InitMonoid -> InitMonoid
initMonoidAlg Id = IdI
initMonoidAlg (Add a b) = AddI a b

initMonoid : MonoidAlg InitMonoid
initMonoid = MkMonoidAlg initMonoidAlg

isInit : (alg : MonoidAlg a) -> InitMonoid -> a
isInit (MkMonoidAlg alg) IdI = alg Id
isInit (MkMonoidAlg alg) (AddI a b) = alg (Add (isInit (MkMonoidAlg alg) a) (isInit (MkMonoidAlg alg) b))

FinalMonoid : Type
FinalMonoid = Unit

finalMonoidAlg : MonoidF FinalMonoid -> FinalMonoid
finalMonoidAlg _ = ()

finalMonoid : MonoidAlg FinalMonoid
finalMonoid = MkMonoidAlg finalMonoidAlg

isFinal : (alg : MonoidAlg a) -> FinalMonoid
isFinal _ = ()
