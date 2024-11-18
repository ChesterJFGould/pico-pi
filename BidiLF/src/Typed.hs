module Typed where

import Symbol

data Theory = Theory [Stmt]
  deriving Eq

data Stmt =
    Cons Symbol ConsType
  | Dest Symbol DestType
  | Sort Symbol SortType
  | Let Symbol Sort Check
  deriving Eq

data Params a = Params [(Symbol, a)]
  deriving Eq

data ConsType = ConsType (Params MetaType) (Params MetaType) SortPat
  deriving Eq

data DestType = DestType (Params MetaType) (Params SortPat) (Params MetaType) Sort
  deriving Eq

data SortType = SortType (Params MetaType)
  deriving Eq

data MetaType = MetaType (Params Sort) Sort
  deriving Eq

data Check =
    ConsApp Symbol [Binding]
  | Synth Synth
  deriving Eq

data Synth =
    DestApp Symbol [Synth] [Binding]
  | MetaApp Symbol [Check]
  | Var Symbol
  | Ann Check Sort
  deriving Eq

data Sort = SortApp Symbol [Binding]
  deriving Eq

data Binding = Binding [Symbol] Check
  deriving Eq

data CheckPat =
    ConsAppPat Symbol [BindingPat]
  | SynthPat SynthPat
  deriving Eq

data SynthPat =
    DestAppPat Symbol [SynthPat] [BindingPat]
  | AnnPat CheckPat SortPat
  deriving Eq

data SortPat = SortAppPat Symbol [BindingPat]
  deriving Eq

data BindingPat =
    UnifVar Symbol
  | NoArgs CheckPat
  deriving Eq
