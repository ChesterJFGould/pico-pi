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
      (list 'String->Symbol '(-> String Symbol) string->symbol)
      (list 'JSON '(Type 0 lzero) (void))
      (list 'Dict->JSON '(-> (Dict Symbol JSON) JSON) (λ (d) d))
      (list 'String->JSON '(-> String JSON) (λ (s) s))
      (list 'List->JSON '(-> (List JSON) JSON) (λ (s) s))
      (list 'So '(-> Bool (Type 0 lzero)) (λ (s) (void)))
      (list 'Oh '(So true) (void))
      (list 'SuchThat '(-> [A : (Type 0 lzero)] (-> A (Type 0 lzero)) (Type 0 lzero)) (λ (A) (λ (F) (void))))
      (list 'An '(-> [A : (Type 0 lzero)] [F : (-> A (Type 0 lzero))] [a : A] (F a) (SuchThat A F)) (λ (A) (λ (F) (λ (a) (λ (prf) a))))))))

(with-handlers
  ([exn:fail? (λ (e) (displayln (exn-message e)))])
  (let*-values
    ([(prog) (read-all (current-input-port))]
     [(e) (parse/top prog)]
     #;
     [(e-t) (parse-check-eval/type tenv venv top-type)]
     [(e^ e-t) (synth/expr tenv venv e)]
     [(e-e) (embed eenv e^)])
    #;
    (displayln (embed eenv e^))
    (if (jsexpr? e-e)
      (begin
        (write-json (embed eenv e^))
        (displayln ""))
      (error 'top-level "Cannot convert `~a` of type `~a` into JSON"
        (unparse/expr e)
        (unparse/texpr (quote/value e-t))))))
