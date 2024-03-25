#lang racket

(require "core2.rkt")

(provide (all-defined-out))

(struct Tree (tag child))

; (: embed (-> (HashTable Symbol Any) TypedExpr Any))
(define (embed env e)
  (match e
    [(Var x) (hash-ref env x)]
    [(Ann e _) (embed env e)]
    [(Lam (TypedBind x _) b) (λ (val) (embed (hash-set env x val) b))]
    [(App f a) ((embed env f) (embed env a))]
    [(BindT _ _ _) (void)]
    [(Type _ _) (void)]
    [(LevelT _) (void)]
    [(LZero) (void)]
    [(LSucc _) (void)]
    [(LMax _ _) (void)]
    [(EmptyT) (void)]
    [(IndEmpty _ _ _) (void)]
    [(UnitT) (void)]
    [(Unit) '()]
    [(EqT _ _ _) (void)]
    [(Refl) (void)]
    [(IndEq _ t _ _) (embed env t)]
    [(W t d) (Tree (embed env t) (embed env d))]
    [(IndW _ t _ e)
      (let
        ([t-embed (embed env t)]
         [e-embed (embed env e)])
        (let rec ([tree t-embed])
          (e-embed
            (Tree-tag tree)
            (Tree-child tree)
            (λ (index) (rec ((Tree-child tree) index))))))]
    [(BoolT) (void)]
    [(Bool v) v]
    [(IndBool _ t _ true false)
      (if (embed env t)
        (embed env true)
        (embed env false))]
    [(Cons fst snd) (cons (embed env fst) (embed env snd))]
    [(First p) (car (embed env p))]
    [(Second p) (cdr (embed env p))]))
