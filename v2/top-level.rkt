#lang typed/racket

(provide (all-defined-out))
(require "core2.rkt")

(: parse/top (-> Any AstExpr))
(define (parse/top e)
  (match e
    [`((def ,x* ,v*) ... ,b)
      (foldr
        (λ ([x : AstBind] [v : AstExpr] [b : AstExpr])
          (Let x v b))
        (parse/expr b)
        (map parse/bind x*)
        (map parse/expr v*))]
    [e (error 'parse/top "Invalid Top Level: `~a`" e)]))

(: read-all (-> Input-Port (Listof Any)))
(define (read-all p)
  (let ([e (read p)])
    (if (eof-object? e)
      '()
      (cons e (read-all p)))))
