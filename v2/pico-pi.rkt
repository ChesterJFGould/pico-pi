#lang racket

(provide repl)

(require
  "core2.rkt"
  "embed.rkt"
  "prims.rkt"
  racket/pretty)

#; 
(define-type Repl
  (U Def RExpr))

#;
(struct Def ([var : AstBind] [val : AstExpr]))
(struct Def (var val))

#;
(struct RExpr ([expr : AstExpr]))
(struct RExpr (expr))

; (: parse/repl (-> Any Repl))
(define (parse/repl r)
  (match r
    [`(def ,var ,val) (Def (parse/bind var) (parse/expr val))]
    [else (RExpr (parse/expr r))]))

#|
; (: def-tenv TEnv)
(define def-tenv
  (env-set* (empty-env) ; (ann (empty-env) TEnv)
    '(Nat zero add1)
    (list
      (cons 'Nat (VType 0 (VLZero)))
      (cons 'zero (VNeu (NVar 'Nat) (delay (VType 0 (VLZero)))))
      (cons 'add1 (VClos (env-set (empty-env) #; (ann (empty-env) VEnv) 'Nat (VNeu (NVar 'Nat) (delay (VType 0 (VLZero))))) (BindT 'Pi (TypedBind (gensym) (Var 'Nat)) (Var 'Nat)))))))

; (: def-venv VEnv)
(define def-venv
  (env-set* (empty-env) ; (ann (empty-env) VEnv)
    '(Nat zero add1)
    (list
      (VNeu (NVar 'Nat) (delay (cdr (env-get def-tenv 'Nat))))
      (VNeu (NVar 'zero) (delay (cdr (env-get def-tenv 'zero))))
      (VNeu (NVar 'add1) (delay (cdr (env-get def-tenv 'add1)))))))

; (: def-eenv (Env Any))
(define def-eenv
  (env-set* (empty-env)
    '(Nat zero add1)
    (list (void) 0 add1)))
|#
(define envs
  (add-prims (empty-env) (empty-env) (empty-env)
    (list
      (list 'Nat '(Type 0 lzero) (void))
      (list 'zero 'Nat 0)
      (list 'add1 '(-> Nat Nat) add1))))
(define def-tenv (car envs))
(define def-venv (cadr envs))
(define def-eenv (caddr envs))

; (: repl (-> Void))
(define (repl)
  (repl-env def-tenv def-venv def-eenv))

; (: repl-env (-> TEnv VEnv (Env Any) Void))
(define (repl-env tenv venv eenv)
  (display "λ> ")
  (define input (read))
  (unless (eof-object? input)
    (define r (parse/repl input))
    (with-handlers
      ; ([exn:fail? (λ ([e : exn]) (displayln (exn-message e)) (repl-env tenv venv eenv))])
      ([exn:fail? (λ (e) (displayln (exn-message e)) (repl-env tenv venv eenv))])
      (match r
        [(Def x v)
          (match-let*-values
            ([(x-n v^ x-t x-t-v) (check/bind-expr tenv venv x v)]
             [(x-n^) (gensym x-n)]
             [(tenv^)
               (env-set* tenv
                 (list x-n x-n^)
                 (list (cons x-n^ x-t-v) (cons x-n^ x-t-v)))]
             [(x-v)
               (VChoice
                 (lazy (VNeu (NVar x-n^) (lazy x-t-v)))
                 (lazy (eval/expr venv v^)))]
             [(venv^)
               (env-set* venv
                 (list x-n x-n^)
                 (list x-v x-v))]
             [(v-embed) (embed eenv v^)]
             [(eenv^) (env-set eenv x-n v-embed)])
            (pretty-display (unparse/bind (TypedBind x-n^ x-t)))
            (pretty-display (unparse/expr (quote/value (eval/expr venv v^))))
            (pretty-display v-embed)
            (repl-env tenv^ venv^ eenv^))]
        [(RExpr e)
          (match-let*-values
            ([(e^ e-t) (synth/expr tenv venv e)]
             [(e-embed) (embed eenv e^)])
            (pretty-display
              `(,(unparse/expr (quote/value (whnf (eval/expr venv e^)))) :
                ,(unparse/expr (quote/value e-t))))
            (pretty-display e-embed)
            (repl-env tenv venv eenv))]))))

(repl)
