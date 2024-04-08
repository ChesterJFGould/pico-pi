#lang typed/racket

(provide (all-defined-out))
(require "env.rkt")

(define-type Synth
  (U
    (Typed Var (Type Check))
    (App Synth Check)
    (Let Synth Synth)
    (Typed Check (Type Check))))
(struct Var ([x : Symbol]))
(struct (f a) App ([f : f] [a : a]))

(struct (e) Scope ([name : Symbol] [x : Symbol] [e : e]))

(define-type Check
  (U
    (Lam (Scope Check))
    (Pi (Type Check) (TypeFamily Check))
    TypeT
    UnitLit
    UnitT
    (Let (Typed Synth (Type Check)) Check)
    (CheckSynth Synth)))
(struct (b) Lam ([b : b]))
(struct (dom codom) Pi ([dom : dom] [codom : codom]))
(struct TypeT ([l : Natural]))
(struct UnitLit ())
(struct UnitT ())
(struct (e) CheckSynth ([e : e]))
(struct (v b) Let ([v : v] [b : (Scope b)]))

(struct (t) Type ([t : t]))
(struct (t) TypeFamily ([t : t]))

(struct (e t) Typed ([e : e] [t : t]))

(: check=? (-> (Env Synth) (Type Check) Check Check Boolean))
(: synth=? (-> (Env Synth) Synth Synth Boolean))

#|
(define-type Norm
  (U
    (Lam (Scope Norm))
    (Pi (Type Norm) (TypeFamily Norm))
    TypeT
    UnitLit
    UnitT
    (CheckSynth Neu)))
(define-type Neu
  (U
    (Typed Var (Type Norm))
    (App Neu Norm)))

(: norm/check (-> (Env Norm) (Type Norm) Check Norm))
(define (norm/check env t e)
  (match (cons (Type-t t) e)
    [(cons (Pi D C) (Lam b))
     (Lam (norm/scope-par env D C b))]
    [(cons (TypeT l) (Pi (Type D) (TypeFamily C)))
     (let
       ([D^ (norm/check env (Type (TypeT l)) D)])
       (Pi
         (Type D^)
         (TypeFamily
           (norm/check
             env
             (Pi (Type D^) (TypeFamily (Lam (Scope 't (gensym) D^))))))))]
    [(cons (TypeT _) (TypeT l)) (TypeT l)]
    [(cons (UnitT) (UnitLit) (UnitLit)]
    [(UnitT) (UnitT)]
    [(cons t (Let (Typed v (Type v-t)) b))
     (norm/scope-def
       env 
       (norm/check env (Type (norm/type env v-t)) v)
       (TypeFamily t)
       b)]
    [(Typed e (Type t))
     (Typed (norm/synth env e) (Type (norm/check env t)))]))

(: norm/synth (-> (Env Norm) Synth Norm))
(define (norm/synth env e)
  (match e
    [(Typed (Var x) _)

(: norm/scope-par (-> (Env Norm) (Type Norm) (TypeFamily Norm) (Scope Check) (Scope Norm)))

(: norm/scope-def (-> (Env Norm) Norm (TypeFamily Norm) (Scope Check) (Scope Norm)))

(: app/scope (-> (Env Norm) (Scope Check) Norm Norm))
|#
