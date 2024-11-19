#lang racket

(require
  "core2.rkt"
  "prims.rkt"
  "top-level.rkt"
  "embed.rkt"
  racket/hash)

(define (parse-check-eval/type tenv venv e)
  (let-values
    ([(t t-x t-y) (synth/expr-type tenv venv (parse/expr e))])
    (eval/expr venv t)))

(define cons-curried (λ (A) (λ (hd) (λ (tl) (cons hd tl)))))
(define hash-set-curried
  (λ (K) (λ (V) (λ (dict) (λ (k) (λ (v) (hash-set dict k v)))))))

(match-define (list tenv venv eenv)
  (add-prims (empty-env) (empty-env) (empty-env)
    (list
      (list 'Exp '(Type 0 lzero) (void))
      (list 'lame '(-> (-> Exp Exp) Exp) (λ (f) (let ([x (gensym 'x)]) `(λ (,x) ,(f x)))))
      (list '$ '(-> Exp Exp Exp) (λ (f) (λ (a) `(,f ,a))))
      (list 'conse '(-> Exp Exp Exp) (λ (f) (λ (s) `(cons ,f ,s))))
      )))
(define top-type 'Exp)

(with-handlers
  ([exn:fail? (λ (e) (displayln (exn-message e)))])
  (let*-values
    ([(prog) (read-all (current-input-port))]
     [(e) (parse/top prog)]
     [(e-t) (parse-check-eval/type tenv venv top-type)]
     [(e^) (check/expr tenv venv e e-t)]
     [(e-e) (embed eenv e^)])
    (displayln e-e)))
