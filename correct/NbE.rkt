#lang racket

(provide (all-defined-out))

(require racket/generic)

(define-generics evaluable
  ;; Evaluable (Hash Symbol Value) -> Value
  (evalu evaluable env))
(define ^evalu evalu)

;; Symbol
(struct id (x)
  #:transparent
  #:methods gen:evaluable
  [(define/match (evalu e env)
     ([(id x) env] (hash-ref env x)))
  ])

;; Symbol Expr
(struct lam (x b)
  #:transparent
  #:methods gen:evaluable
  [(define/match (evalu e env)
     ([(lam x b) env] (lam-c x b env)))
  ])

;; Expr Expr
(struct app (f a)
  #:transparent
  #:methods gen:evaluable
  [(define/match (evalu e env)
     ([(app f a) env]
        (match (^evalu f env)
          [(lam-c x b b-env) (^evalu b (hash-set b-env x (^evalu a env)))]
          [f-ne (app-e f-ne (^evalu a env))])))
  ])

(define-generics quotable
  (quote-norm quotable scope))
(define ^quote-norm quote-norm)

;; A choice between folding and unfolding a specific variable
(struct glue (x ne v))

;; Symbol
(struct var-e (x)
  #:transparent
  #:methods gen:quotable
  [(define/match (quote-norm e scp)
     ([(var-e x) scp] (id x)))
  ])

;; Symbol Expr Env
(struct lam-c (x b env)
  #:transparent
  #:methods gen:quotable
  [(define/match (quote-norm e scp)
     ([(lam-c x b env) scp]
        (let [(x^ (gensym x))]
          (lam x^ (^quote-norm (evalu b (hash-set env x (var-e x^))) scp)))))
  ])

;; Neutral Value
(struct app-e (f a)
  #:transparent
  #:methods gen:quotable
  [(define/match (quote-norm e scp)
     ([(app-e f a) scp] (app (^quote-norm f scp) (^quote-norm a scp))))
  ])
