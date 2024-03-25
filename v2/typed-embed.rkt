#lang typed/racket

(require "core2.rkt")

(require/typed "embed.rkt"
  [embed (-> (Env Any) TypedExpr Any)]
  [#:struct Tree ([tag : Any] [child : Any])])

(provide embed (struct-out Tree))
