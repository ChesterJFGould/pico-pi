#lang typed/racket

(provide (all-defined-out))

(require
  (prefix-in typ: "typed-expr.rkt")
  (prefix-in val: "value-expr.rkt")
  "env.rkt")

(: eval/check (-> (Env val:Check) typ:Check val:Check))
(define (eval/check env e)
  (match e
    [(typ:Lam b)
      (let*
        ([x-n (gensym)]
         [env^ (env-set env x-n (val:CheckSynth (val:FreeVar x-n)))])
        (val:abstract (typ:Scope-x b) x-n (eval/check env^ (typ:instantiate (typ:FreeVar x-n) b))))]
    [(typ:Pi D C) (val:Pi (eval/check env D) (eval/check env C))]
    [(typ:Type l) (val:Type l)]
    [(typ:UnitLit) (val:UnitLit)]
    [(typ:UnitT) (val:UnitT)]
    [(typ:CheckSynth e) (eval/synth env e)]))

(: eval/synth (-> (Env val:Check) typ:Synth val:Check))
(define (eval/synth env e)
  (match e
    [(typ:FreeVar x) (env-get env x)]
    [(typ:BoundVar i) (val:BoundVar i)]
    [(
