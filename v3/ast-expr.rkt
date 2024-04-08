#lang typed/racket

(provide (all-defined-out))

(define-type Expr
  (U Var Lam App Pi Type Ann UnitLit UnitT))
(struct Var ([x : Symbol]) #:transparent)
(struct Lam ([x : Var] [b : Expr]) #:transparent)
(struct App ([f : Expr] [a : Expr]) #:transparent)
(struct Pi ([dom : Expr] [codom : Expr]) #:transparent)
(struct Type ([l : Natural]) #:transparent)
(struct Ann ([e : Expr] [t : Expr]) #:transparent)
(struct UnitLit () #:transparent)
(struct UnitT () #:transparent)
(struct Let ([x : Symbol] [v : Expr] [b : Expr]))

(: parse/expr (-> Any Expr))
(define (parse/expr e)
  (match e
    [(? symbol? x) (parse/var x)]
    [`() (UnitLit)]
    [`Unit (UnitT)]
    [`([,(? symbol? xs)] ..1 ,b) (foldr Lam (parse/expr b) (map parse/var xs))]
    [`(-> ,D ,C) (Pi (parse/expr D) (parse/expr C))]
    [`(Type ,(? natural? l)) (Type l)]
    [`(,e : ,t) (Ann (parse/expr e) (parse/expr t))]
    [`(,f ,args ..1) (foldr (λ ([arg : Expr] [f : Expr]) (App f arg)) (parse/expr f) (map parse/expr args))]
    [e (error 'parse/expr "Invalid Expr: ~a" e)]))

(: parse/var (-> Any Var))
(define (parse/var x)
  (if (and (symbol? x) (not (member x '(-> Type Unit))))
    (Var x)
    (error 'parse/var "Invalid Variable: ~a" x)))

(: unparse/expr (-> Expr Any))
(define (unparse/expr e)
  (match e
    [(Var x) x]
    [(Lam x b) (unparse/lam (Lam x b))]
    [(App f a) (unparse/app (App f a))]
    [(Pi D C) `(-> ,(unparse/expr D) ,(unparse/expr C))]
    [(Type l) `(Type ,l)]
    [(Ann e t) `(,(unparse/expr e) : ,(unparse/expr t))]
    [(UnitLit) `()]
    [(UnitT) 'Unit]))

(: unparse/lam (-> Expr (Listof Any)))
(define (unparse/lam e)
  (match e
    [(Lam x b) `([,(Var-x x)] ,@(unparse/lam b))]
    [e (list (unparse/expr e))]))

(: unparse/app (-> Expr (Listof Any)))
(define (unparse/app e)
  (match e
    [(App f a) `(,@(unparse/app f) ,(unparse/expr a))]
    [e (list (unparse/expr e))]))
