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
  (repl-env (empty-env) (empty-env)))

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
                   (list x-v x-v))])
              (pretty-display (unparse/bind (TypedBind x-n^ x-t)))
              (pretty-display (unparse/expr (quote/value (eval/expr venv v^))))
              (repl-env tenv^ venv^))]
          [(RExpr e)
            (match-let*-values
              ([(e^ e-t) (synth/expr tenv venv e)])
              (pretty-display
                `(,(unparse/expr (quote/value (eval/expr venv e^))) :
                  ,(unparse/expr (quote/value e-t))))
              (repl-env tenv venv))])))))

(repl)
