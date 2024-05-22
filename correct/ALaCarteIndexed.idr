module ALaCarteIndexed

import Data.List.Quantifiers

interface IFunctor (0 f : (a -> Type) -> (a -> Type)) where
  imap : {0 g, h : a -> Type} -> {0 i : a} -> ((0 i : a) -> g i -> h i) -> f g i -> f h i

data OneOf : List ((a -> Type) -> (a -> Type)) -> (a -> Type) -> (a -> Type) where
  This : {0 f : (a -> Type) -> (a -> Type)} -> {0 g : a -> Type} -> (0 i : a) -> f g i -> OneOf (f :: l) g i
  Next : OneOf l g i -> OneOf (f :: l) g i

data IFunctorList : List ((a -> Type) -> (a -> Type)) -> Type where
  NilF : IFunctorList []
  ConsF : IFunctor f => IFunctorList l -> IFunctorList (f :: l)

(ifl : IFunctorList l) => IFunctor (OneOf l) where
  imap f (This i d) with (ifl)
    _ | ConsF _ = This i (imap f d)
  imap f (Next oo) with (ifl)
    _ | ConsF _ = Next (imap f oo)

data IFix : (0 f : (a -> Type) -> (a -> Type)) -> (a -> Type) where
 In : f (IFix f) i -> IFix f i

ifixFold : IFunctor f => ((0 i : a) -> f h i -> h i) -> (0 i : a) -> IFix f i -> h i
ifixFold f i (In d) = f i (imap (ifixFold f) d)

interface (:<:) (0 f : (a -> Type) -> (a -> Type)) (0 g : (a -> Type) -> (a -> Type)) where
  inj : {0 i : a} -> {0 h : a -> Type} -> f h i -> g h i

infix 6 :<:

(:<:) f (OneOf (f :: l)) where
  inj d = This _ d

(foo : (:<:) f (OneOf l)) => (:<:) f (OneOf (g :: l)) where
  inj d = Next (inj @{foo} d)

inject : (gf : g :<: f) => g (IFix f) i -> IFix f i
inject d = In (inj @{gf} d)

data Typ : Type where
  NatT : Typ
  StrT : Typ

data NatF : (Typ -> Type) -> (Typ -> Type) where
  NatLit : Nat -> NatF a NatT
  NatAdd : {0 a : Typ -> Type} -> a NatT -> a NatT -> NatF a NatT

natLit : NatF :<: f => Nat -> IFix f NatT
natLit n = inject (NatLit n)

natAdd : NatF :<: f => IFix f NatT -> IFix f NatT -> IFix f NatT
natAdd l r = inject (NatAdd l r)

IFunctor NatF where
  imap f (NatLit n) = NatLit n
  imap f (NatAdd l r) = NatAdd (f NatT l) (f NatT r)

data StrF : (Typ -> Type) -> (Typ -> Type) where
  StrLit : String -> StrF a StrT
  StrAdd : {0 a : Typ -> Type} -> a StrT -> a StrT -> StrF a StrT

strLit : StrF :<: f => String -> IFix f StrT
strLit n = inject (StrLit n)

strAdd : StrF :<: f => IFix f StrT -> IFix f StrT -> IFix f StrT
strAdd l r = inject (StrAdd l r)

IFunctor StrF where
  imap f (StrLit n) = StrLit n
  imap f (StrAdd l r) = StrAdd (f StrT l) (f StrT r)

NatStrF : (Typ -> Type) -> (Typ -> Type)
NatStrF = OneOf [NatF, StrF]

NatStr : Typ -> Type
NatStr = IFix NatStrF

Sem : Typ -> Type
Sem NatT = Nat
Sem StrT = String

interface IFunctor f => Eval (0 f : (Typ -> Type) -> (Typ -> Type)) where
  evalAlg : (0 i : Typ) -> f Sem i -> Sem i

Eval NatF where
  evalAlg NatT (NatLit n) = n
  evalAlg NatT (NatAdd l r) = l + r

Eval StrF where
  evalAlg StrT (StrLit s) = s
  evalAlg StrT (StrAdd l r) = l <+> r

(afl : IFunctorList l) => (ael : All Eval l) => Eval (OneOf l) where
  evalAlg t (This t d) with (afl)
    _ | (ConsF _) with (ael)
      _ | (_ :: _) = evalAlg t d
  evalAlg t (Next oo) with (afl)
    _ | (ConsF _) with (ael)
      _ | (_ :: _) = evalAlg t oo

eval : (0 t : Typ) -> NatStr t -> Sem t
eval = ifixFold evalAlg
