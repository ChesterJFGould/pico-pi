#lang typed/racket

(provide (all-defined-out))

(define-type (Env a) (HashTable Symbol a))

(: empty-env (All (a) (-> (Env a))))
(define (empty-env) (hash))

(: env-get (All (a) (-> (Env a) Symbol a)))
(define (env-get env x) (hash-ref env x))

(: env-set (All (a) (-> (Env a) Symbol a (Env a))))
(define (env-set env x v) (hash-set env x v))

(: env-has? (All (a) (-> (Env a) Symbol Boolean)))
(define (env-has? env x) (hash-has-key? env x))

(: env-join-left (All (a) (-> (Env a) (Env a) (Env a))))
(define (env-join-left l r)
  (foldr
    (λ ([kv : (Pairof Symbol a)] [env : (Env a)])
      (env-set env (car kv) (cdr kv)))
    r
    (hash->list l)))

(: env-map (All (a b) (-> (Env a) (-> a b) (Env b))))
(define (env-map env f)
  (foldr
    (λ ([kv : (Pairof Symbol a)] [env : (Env b)])
      (env-set env (car kv) (f (cdr kv))))
    (ann (empty-env) (Env b))
    (hash->list env)))

(define-type (DEnv a) (Listof a))

(: empty-denv (All (a) (-> (DEnv a))))
(define (empty-denv) '())

(: denv-get (All (a) (-> (DEnv a) Natural a)))
(define (denv-get env i) (list-ref env i))

(: denv-push (All (a) (-> (DEnv a) a (DEnv a))))
(define (denv-push env v) (cons v env))
