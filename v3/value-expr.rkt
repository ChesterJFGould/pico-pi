#lang typed/racket

(provide (all-defined-out))

(require
  (prefix-in typ: "typed-expr.rkt")
  "env.rkt")

(struct Glued (s v) ([syn : s] [sem : v]))

(define-type Whnf
  (U ...))
