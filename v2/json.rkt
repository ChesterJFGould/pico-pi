#lang racket

(require
  "core2.rkt"
  "prims.rkt"
  "top-level.rkt"
  "embed.rkt"
  json)

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
      (list 'Nat '(Type 0 lzero) (void))
      (list 'zero 'Nat 0)
      (list 'add1 '(-> Nat Nat) add1)
      (list 'List '(-> (Type 0 lzero) (Type 0 lzero)) (λ (x) x))
      (list 'nil '(-> [A : (Type 0 lzero)] (List A)) (λ (A) '()))
      (list ':: '(-> [A : (Type 0 lzero)] A (List A) (List A)) cons-curried)
      (list 'Dict '(-> [K : (Type 0 lzero)] [V : (Type 0 lzero)] (Type 0 lzero)) (λ (K) (λ (V) (void))))
      (list 'dict-empty '(-> [K : (Type 0 lzero)] [V : (Type 0 lzero)] (Dict K V)) (λ (K) (λ (V) (hash))))
      (list 'dict-add '(-> [K : (Type 0 lzero)] [V : (Type 0 lzero)] (Dict K V) K V (Dict K V)) hash-set-curried)
      (list 'Symbol '(Type 0 lzero) (void))
      (list 'String->Symbol '(-> String Symbol) string->symbol))))
(define top-type '(Dict Symbol String))

(with-handlers
  ([exn:fail? (λ (e) (displayln (exn-message e)))])
  (let*-values
    ([(prog) (read-all (current-input-port))]
     [(e) (parse/top prog)]
     [(e-t) (parse-check-eval/type tenv venv top-type)]
     [(e^) (check/expr tenv venv e e-t)]
     [(e-e) (embed eenv e^)])
    (write-json e-e)
    (displayln "")))
