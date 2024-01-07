#lang typed/racket

(provide repl)

(require
  "core2.rkt"
  racket/pretty)

(define-type Repl
  (U Def RExpr))

(struct Def ([var : AstBind] [val : AstExpr]))

(struct RExpr ([expr : AstExpr]))

(: parse/repl (-> Any Repl))
(define (parse/repl r)
  (match r
    [`(def ,var ,val) (Def (parse/bind var) (parse/expr val))]
    [else (RExpr (parse/expr r))]))

(: repl (-> Void))
(define (repl)
  (repl-env empty-env empty-env))

(: repl-env (-> TEnv VEnv Void))
(define (repl-env tenv venv)
  (with-handlers
    ([exn:fail? (λ (e) (displayln e) (repl-env tenv venv))])
    (display "λ> ")
    (define input (read))
    (unless (eof-object? input)
      (define r (parse/repl input))
      (with-handlers
        ([exn:fail? (λ ([e : exn]) (displayln (exn-message e)) (repl-env tenv venv))])
        (match r
          [(Def var val)
            (define-values (var^ val^ type) (check/bind-expr tenv venv var val))
            (pretty-display (unparse/bind var^))
            (pretty-display (unparse/expr (quote/value (eval/expr venv val^))))
            (define tenv^ (env-set tenv (TypedBind-x var^) type))
            (define venv^
              (env-set venv (TypedBind-x var^)
                (VChoice
                  (lazy (VNeu (NVar (TypedBind-x var^)) (lazy type)))
                  (lazy (eval/expr venv val^)))))
            (repl-env tenv^ venv^)]
          [(RExpr e)
            (define-values (e^ e-t) (synth/expr tenv venv e))
            (pretty-display `(,(unparse/expr (quote/value (eval/expr venv e^))) : ,(unparse/expr (quote/value e-t))))
            (repl-env tenv venv)])))))

(repl)
