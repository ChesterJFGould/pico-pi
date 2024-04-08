#lang typed/racket

(provide (all-defined-out))
(require
  (prefix-in ast: "ast-expr.rkt")
  "typed-expr.rkt"
  "env.rkt")

(define-type TypeError
  (U CannotSynth))
(struct CannotSynth ([e : ast:Expr]))
(struct ConstructorTypeMismatch ([e : ast:Expr] [t : (Type Check)]))
(struct CheckTypeMismatch ([e : ast:Expr] [actual : (Type Check)] [expected : (Type Check)]))

(: TypeError->String (-> TypeError String))
(define (TypeError->String e)
  (match e
    [(CannotSynth e)
      (format "Cannot synthesize type for `~a`" (ast:unparse/expr e))]
    [(ConstructorTypeMismatch e (Type t))
      (format "Expected `~a` to be of type `~a`"
        (ast:unparse/expr e)
        (unparse/check-value t))]
    [(CheckTypeMismatch e (Type actual) (Type expected))
      (format "Expected `~a` to be of type `~a` but is of type `~a`"
        (ast:unparse/expr e)
        (unparse/check-value actual)
        (unparse/check-value expected))]))


(: pure/tc (All (a) (-> a (TC a))))
(: err/tc (All (a) (-> TypeError (TC a))))

(: get-type/tc (-> Symbol (TC (Type CheckValue))))
(: get-def/tc (-> Symbol (TC CheckValue)))

(struct Synthed ([e : Synth] [t : (Type CheckValue)]))
(: synth (-> ast:Expr (TC Synthed)))
(define (synth e)
  (match e
    [(ast:Var x)
      (do/tc
        x-t <- (get-type/tc x)
        x-syn <- (get-def/tc x)
        (pure/tc (Synthed x-syn x-t)))]
    [(ast:App f a)
      (do/tc
        (IsPi f^ dom codom) <- (synth/pi f)
        a^ <- (check a dom)
        (pure/tc
          (Synthed
            (App f^ a^)
            (vAppTypeFamily codom (eval/check a^)))))]
    [(ast:Ann e t)
      (do/tc
        (IsType t^ t-l) <- (type t)
        e^ <- (check e t^)
        (pure/tc (Synthed e^ t^)))]
    [e (err/tc (CannotSynth e))]))

(struct IsPi ([f : Synth] [dom : (Type CheckValue)] [codom : (TypeFamily CheckValue)]))
(: synth/pi (-> ast:expr (TC IsPi)))

(: check (-> ast:Expr Type (TC Check)))
(define (check e t)
  (match (cons e (type-whnf t))
    [(cons (ast:Lam x b) (VPi dom codom))
      (do/tc
        x-n = (gensym x)
        x-v = (vParam x-n)
        b^ <- (with-var/tc x dom x-v (check b (inst-type-family codom (x-v))))
        (Lam (abstract x x-n b^)))]
    [(cons (ast:Pi dom codom) (VTypeT l))
      (do/tc
        dom^ <- (check dom t)
        codom^ <- (check codom (vType (vPi (mkType dom^) (vTypeFamily (vConst t)))))
        (pure/tc (Pi (mkType dom^) (mkTypeFamily codom^))))]
    [(cons (ast:TypeT l) (VTypeT k)) #:when (< l k)
      (pure/tc (TypeT l))]
    [(cons (ast:UnitT) (VTypeT _))
      (pure/tc (UnitT))]
    [(cons (? checkable? e) _)
      (err/tc (ConstructorTypeMismatch e t))]
    [(cons e _)
      (do/tc
        (Synthed e^ e-t) <- (synth e)
        (if (type=? e-t t)
          (pure/tc e^)
          (err/tc (CheckTypeMismatch e e-t t))))]))

(struct IsType ([t : Type] [l : Natural]))
(: type (-> ast:Expr (TC IsType)))
