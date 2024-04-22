#lang racket

(require
  "core2.rkt"
  "prims.rkt"
  "top-level.rkt"
  "embed.rkt"
  racket/hash)

(define empty-rules (hash))

(define (add-rule rules key action)
  (hash-set rules key action))

(define (run-rule rules rule)
  ((hash-ref rules rule) rules))

(struct Make (rule rules))

(define (run-make make)
  (run-rule (Make-rules make) (Make-rule make)))

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
      (list 'Maybe '(-> (Type 0 lzero) (Type 0 lzero)) (void))
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
      (list 'An '(-> [A : (Type 0 lzero)] [F : (-> A (Type 0 lzero))] [a : A] (F a) (SuchThat A F)) (λ (A) (λ (F) (λ (a) (λ (prf) a)))))
      (list 'Action '(-> (Type 0 lzero) (Type 0 lzero)) (λ (_) (void)))
      (list 'pure '(-> [A : (Type 0 lzero)] A (Action A))
        (λ (A) (λ (a) (λ (rules) a))))
      (list '>>=
        '(-> [A : (Type 0 lzero)] [B : (Type 0 lzero)] (Action A) (-> A (Action B)) (Action B))
        (λ (A) (λ (B) (λ (mk-a) (λ (f) (λ (rules) ((f (mk-a rules)) rules)))))))
      (list 'sh
        '(-> [cmd : String] [args : (List String)] (Action Unit))
        (λ (cmd) (λ (args) (λ (rules)
          (let ([cmd (string-join (cons cmd args))])
            (displayln cmd)
            (system cmd)
            (void))))))
      (list 'need '(-> String (Action Unit))
        (λ (s)
          (λ (rules)
            (for-each (λ (key) (run-rule rules key)) (string-split s))
            (void))))
      (list 'file-contents '(-> String (Action String))
        (λ (path) (λ (rules) (file->string path))))
      (list 'Rules '(Type 0 lzero) (void))
      (list 'empty-Rules 'Rules empty-rules)
      (list '*>
        '(-> String (Action Unit) Rules)
        (λ (key) (λ (action) (add-rule empty-rules key action))))
      (list '++
        '(-> Rules Rules Rules)
        (λ (a) (λ (b) (hash-union a b))))
      (list 'Make '(Type 0 lzero) (void))
      (list 'make '(-> String Rules Make)
        (λ (rule) (λ (rules) (Make rule rules))))
      )))
(define top-type 'Make)

(with-handlers
  ([exn:fail? (λ (e) (displayln (exn-message e)))])
  (let*-values
    ([(prog) (read-all (current-input-port))]
     [(e) (parse/top prog)]
     [(e-t) (parse-check-eval/type tenv venv top-type)]
     [(e^) (check/expr tenv venv e e-t)]
     [(e-e) (embed eenv e^)])
    (if (> (vector-length (current-command-line-arguments)) 0)
      (run-rule (Make-rules e-e) (vector-ref (current-command-line-arguments) 0))
      (run-make e-e))
    (void)))

