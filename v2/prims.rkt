#lang racket

(provide (all-defined-out))
(require "core2.rkt")

;; (: add-prims (-> TEnv VEnv (Env Any) (Listof (List Symbol Any Any)) (List TEnv VEnv (Env Any))))
(define (add-prims tenv venv eenv prims)
  ((foldr
     (λ (prim rest)
       (λ (tenv venv eenv)
         (match-let*-values
           ([((list x x-t x-e)) prim]
            [(x-t^ _ _) (synth/expr-type tenv venv (parse/expr x-t))]
            [(x-t-v) (eval/expr venv x-t^)]
            [(tenv^) (env-set tenv x (cons x x-t-v))]
            [(venv^) (env-set venv x (VNeu (NVar x) (delay x-t-v)))]
            [(eenv^) (env-set eenv x x-e)])
           (rest tenv^ venv^ eenv^))))
     (λ (tenv venv eenv)
       (list tenv venv eenv))
     prims)
    tenv venv eenv))
