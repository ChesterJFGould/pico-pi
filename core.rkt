#lang typed/racket

(provide (all-defined-out))

; Expr functor parameterized by bind type
(define-type (Expr b r)
  (U Var (Ann r) (Lam b r) (App r) (Pi r) (Type r) Level LZero (LSucc r)
    (LMax r) EmptyT (IndEmpty r) UnitT UnitLit (EqT r) Refl (IndEq r)
    (W r) (w r) (IndW r)))

(struct Var ([name : Symbol]) #:transparent)

(struct (r) Ann ([v : r] [t : r]) #:transparent)

(struct (b r) Lam ([var : b] [body : r]) #:transparent)

(struct (r) App ([fun : r] [arg : r]) #:transparent)

(struct (r) Pi ([var : (TypedBind r)] [body : r]) #:transparent)

(struct (r) Type ([y : Natural] [x : r]) #:transparent)

(struct Level ([y : Natural]) #:transparent)

(struct LZero () #:transparent)

(struct (r) LSucc ([l : r]) #:transparent)

(struct (r) LMax ([l : r] [r : r]) #:transparent)

(struct EmptyT () #:transparent)

(struct (r) IndEmpty ([level : r] [t : r] [motive : r]) #:transparent)

(struct UnitT () #:transparent)

(struct UnitLit () #:transparent)

(struct (r) EqT ([type : r] [l : r] [r : r]) #:transparent)

(struct Refl () #:transparent)

(struct (r) IndEq
  ([l : r] [to : r] [t : r] [m : r] [refl : r])
  #:transparent)

(struct (r) W ([tag : (TypedBind r)] [arity : r]) #:transparent)

(struct (r) w ([tag : r] [data : r]) #:transparent)

(struct (r) IndW ([l : r] [t : r] [m : r] [e : r]) #:transparent)

(struct (r) TypedBind ([name : Symbol] [type : r]) #:transparent)

(struct UntypedBind ([name : Symbol]) #:transparent)

(define-type (Bind r)
  (U (TypedBind r) UntypedBind))

; Ast and Typed Expressions

(define-type AstBind (Bind AstExpr))

(define-type AstTypedBind (TypedBind AstExpr))

(define-type AstExpr (Expr AstBind AstExpr))

(define-type TBind (TypedBind TypedExpr))

(define-type TypedExpr (Expr TBind TypedExpr))

; Values

(define-type Value
  (U VNeu VLam VPi VType VLevel VLZero VLSucc VEmptyT VUnitT VUnit VEqT VRefl
    VW Vw))

(struct VNeu ([neu : Neutral] [type : Value]) #:transparent)

(struct VLam ([env : VEnv] [var : VBind] [body : TypedExpr]) #:transparent)

(struct VPi ([env : VEnv] [var : VBind] [body : TypedExpr]) #:transparent)

(struct VType ([y : Natural] [x : Value]) #:transparent)

(struct VLevel ([y : Natural]) #:transparent)

(struct VLZero () #:transparent)

(struct VLSucc ([l : Value]) #:transparent)

(struct VEmptyT () #:transparent)

(struct VUnitT () #:transparent)

(struct VUnit () #:transparent)

(struct VEqT ([type : Value] [l : Value] [r : Value]) #:transparent)

(struct VRefl () #:transparent)

(struct VBind ([name : Symbol] [type : Value]) #:transparent)

(struct VW ([env : VEnv] [tag : VBind] [body : TypedExpr]) #:transparent)

(struct Vw ([tag : Value] [data : Value]) #:transparent)

(define-type Neutral
  (U NVar NApp NIndEmpty NLMaxL NLMaxR NIndEq NIndW))

(struct NVar ([name : Symbol]) #:transparent)

(struct NApp ([fun : Neutral] [arg : Value]) #:transparent)

(struct NIndEmpty ([level : Value] [t : Neutral] [motive : Value]) #:transparent)

(struct NLMaxL ([l : Neutral] [r : Value]) #:transparent)

(struct NLMaxR ([l : Value] [r : Neutral]) #:transparent)

(struct NIndEq
  ([l : Value] [to : Value] [t : Neutral] [m : Value] [refl : Value])
  #:transparent)

(struct NIndW
  ([l : Value] [t : Neutral] [m : Value] [e : Value])
  #:transparent)

; Env

(define-type Env (HashTable Symbol Value))

(define-type VEnv Env)

(define-type TEnv Env)

; Parsing

(: parse/expr (-> Any AstExpr))
(define (parse/expr e)
  (match e
    ['Unit (UnitT)]
    ['Empty (EmptyT)]
    [`lzero (LZero)]
    [`Refl (Refl)]
    [(? symbol?) (parse/variable e)]
    [`(,e : ,t) (Ann (parse/expr e) (parse/expr t))]
    [`(,(or 'λ 'lam) ,v ,b) (Lam (parse/bind v) (parse/expr b))]
    [`(,(or 'Π 'Pi '->) ,v ,b) (Pi (parse/typed-bind v) (parse/expr b))]
    [`(Type ,(? natural? y) ,x) (Type y (parse/expr x))]
    [`(Level ,(? natural? y)) (Level y)]
    [`(lsucc ,l) (LSucc (parse/expr l))]
    [`(lmax ,l ,r) (LMax (parse/expr l) (parse/expr r))]
    [`(ind-Empty ,l ,t ,m)
      (IndEmpty (parse/expr l) (parse/expr t) (parse/expr m))]
    [`() (UnitLit)]
    [`(= ,t ,l ,r) (EqT (parse/expr t) (parse/expr l) (parse/expr r))]
    [`(ind-= ,l ,to ,t ,m ,refl)
      (IndEq (parse/expr l) (parse/expr to) (parse/expr t) (parse/expr m)
        (parse/expr refl))]
    [`(W ,t ,B) (W (parse/typed-bind t) (parse/expr B))]
    [`(w ,t ,d) (w (parse/expr t) (parse/expr d))]
    [`(ind-W ,l ,t ,m ,e)
      (IndW (parse/expr l) (parse/expr t) (parse/expr m) (parse/expr e))]
    [`(,f ,a ...)
      (foldl
        (λ ([a : AstExpr] [f : AstExpr]) (App f a))
        (parse/expr f)
        (map parse/expr a))]
    [else (error 'parse/expr "Invalid Expr: ~a" e)]))

(: variable? (-> Symbol Boolean))
(define (variable? v)
  (not
    (member
      v
      '(λ lam Π Pi -> : let Empty ind-Empty Unit lzero lsucc lmax Level Type
        W w ind-W = ind-= Refl))))

(: parse/variable (-> Symbol Var))
(define (parse/variable v)
  (match v
    [(? variable?) (Var v)]
    [else (error 'parse/variable "Invalid Variable: ~a" v)]))

(: parse/bind (-> Any AstBind))
(define (parse/bind b)
  (match b
    [(? symbol?) #:when (variable? b) (UntypedBind b)]
    [`(,(? symbol? n) : ,t) #:when (variable? n) (TypedBind n (parse/expr t))]
    [else (error 'parse/bind "Invalid Bind: ~a" b)]))

(: parse/typed-bind (-> Any AstTypedBind))
(define (parse/typed-bind b)
  (match b
    [`(,(? symbol? n) : ,t) #:when (variable? n) (TypedBind n (parse/expr t))]
    [else (TypedBind (gensym '_) (parse/expr b))]))

; NbE

(: eval/expr (-> VEnv TypedExpr Value))
(define (eval/expr env expr)
  (match expr
    [(Var name) (env-ref env name)]
    [(Ann v t) (eval/expr env v)]
    [(Lam x b) (VLam env (eval/bind env x) b)]
    [(App f a) (do-app (eval/expr env f) (eval/expr env a))]
    [(Pi x b) (VPi env (eval/bind env x) b)]
    [(Type y x) (VType y (eval/expr env x))]
    [(Level y) (VLevel y)]
    [(LZero) (VLZero)]
    [(LSucc l) (VLSucc (eval/expr env l))]
    [(LMax l r) (do-lmax (eval/expr env l) (eval/expr env r))]
    [(EmptyT) (VEmptyT)]
    [(IndEmpty l t m)
      (do-ind-empty (eval/expr env l) (eval/expr env t) (eval/expr env m))]
    [(UnitT) (VUnitT)]
    [(UnitLit) (VUnit)]
    [(EqT t l r) (VEqT (eval/expr env t) (eval/expr env l) (eval/expr env r))]
    [(Refl) (VRefl)]
    [(IndEq l to t m refl)
      (do-ind-eq (eval/expr env l) (eval/expr env to) (eval/expr env t)
        (eval/expr env m) (eval/expr env refl))]
    [(W t a) (VW env (eval/bind env t) a)]
    [(w t d) (Vw (eval/expr env t) (eval/expr env d))]
    [(IndW l t m e)
      (do-ind-w env (eval/expr env l) (eval/expr env t) (eval/expr env m)
        (eval/expr env e))]))

(: eval/bind (-> VEnv TBind VBind))
(define (eval/bind env b)
  (match b
    [(TypedBind n t) (VBind n (eval/expr env t))]))

(: quote/value (-> Value TypedExpr))
(define (quote/value v)
  (match v
    [(VNeu n _) (quote/neutral n)]
    [(VLam env x b)
      (define x^ (refresh x))
      (Lam
        (quote/bind x^)
        (quote/value
          (eval/expr
            (env-set env x (VNeu (NVar (VBind-name x^)) (VBind-type x^)))
            b)))]
    [(VPi env x b)
      (define x^ (refresh x))
      (Pi
        (quote/bind x^)
        (quote/value
          (eval/expr
            (env-set env x (VNeu (NVar (VBind-name x^)) (VBind-type x^)))
            b)))]
    [(VType y x) (Type y (quote/value x))]
    [(VLevel y) (Level y)]
    [(VLZero) (LZero)]
    [(VLSucc l) (LSucc (quote/value l))]
    [(VEmptyT) (EmptyT)]
    [(VUnitT) (UnitT)]
    [(VUnit) (UnitLit)]
    [(VEqT A from to) (EqT (quote/value A) (quote/value from) (quote/value to))]
    [(VRefl) (Refl)]
    [(VW env t a)
      (define t^ (refresh t))
      (W (quote/bind t^)
        (quote/value
          (eval/expr
            (env-set env t (VNeu (NVar (VBind-name t^)) (VBind-type t^)))
            a)))]
    [(Vw t d) (w (quote/value t) (quote/value d))]))

(: quote/neutral (-> Neutral TypedExpr))
(define (quote/neutral n)
  (match n
    [(NVar n) (Var n)]
    [(NApp f a) (App (quote/neutral f) (quote/value a))]
    [(NIndEmpty l n m) (IndEmpty (quote/value l) (quote/neutral n) (quote/value m))]
    [(NLMaxL l r) (LMax (quote/neutral l) (quote/value r))]
    [(NLMaxR l r) (LMax (quote/value l) (quote/neutral r))]
    [(NIndEq l to t m refl)
      (IndEq (quote/value l) (quote/value to) (quote/neutral t) (quote/value m)
        (quote/value refl))]
    [(NIndW l t m e)
      (IndW (quote/value l) (quote/neutral t) (quote/value m)
        (quote/value e))]))

(: quote/bind (-> VBind TBind))
(define (quote/bind b)
  (TypedBind (VBind-name b) (quote/value (VBind-type b))))

(: refresh (-> VBind VBind))
(define (refresh b)
  (VBind (gensym (VBind-name b)) (VBind-type b)))

(: do-app (-> Value Value Value))
(define (do-app f a)
  (match f
    [(VLam env x b) (eval/expr (env-set env x a) b)]
    [(VNeu n (VPi env x b)) (VNeu (NApp n a) (eval/expr (env-set env x a) b))]))

(: do-ind-empty (-> Value Value Value Value))
(define (do-ind-empty l t m)
  (match t
    [(VNeu n (VEmptyT)) (VNeu (NIndEmpty l n m) (do-app m t))]))

(: do-ind-eq (-> Value Value Value Value Value Value))
(define (do-ind-eq l to t m refl)
  (match t
    [(VRefl) refl]
    [(VNeu n (VEqT _ _ _))
      (VNeu (NIndEq l to n m refl) (do-app (do-app m to) t))]))

(: do-ind-w (-> VEnv Value Value Value Value Value))
(define (do-ind-w env l t m e)
  (match t
    [(Vw tag data)
      (define t (gensym 't))
      (define t-t
        (match data
          [(VLam _ (VBind _ t-t) _) t-t]
          [(VNeu _ (VPi _ (VBind _ t-t) _)) t-t]))
      (do-app (do-app (do-app e tag) data)
        (VLam env (VBind t t-t)
          (IndW (quote/value l) (App (quote/value data) (Var t)) (quote/value m)
            (quote/value e))))]
    [(VNeu n (VW _ _ _)) (VNeu (NIndW l n m e) (do-app m t))]))

(: do-lmax (-> Value Value Value))
(define (do-lmax l r)
  (match (cons l r)
    [(cons (VNeu n t) r) (VNeu (NLMaxL n r) t)]
    [(cons l (VNeu n t)) (VNeu (NLMaxR l n) t)]
    [(cons l r) (max-levels l r)]))

(: max-levels (-> Value Value Value))
(define (max-levels l r)
  (match (cons l r)
    [(cons (VLZero) r) r]
    [(cons l (VLZero)) l]
    [(cons (VLSucc l) (VLSucc r)) (VLSucc (max-levels l r))]))

; Env

(: empty-env Env)
(define empty-env (hash))

(: env-set (-> Env (U TBind VBind) Value Env))
(define (env-set env b v)
  (match b
    [(TypedBind n _) (hash-set env n v)]
    [(VBind n _) (hash-set env n v)]))

(: env-set-neu (-> Env (U TBind VBind) Value Env))
(define (env-set-neu env b t)
  (match b
    [(TypedBind n _) (hash-set env n (VNeu (NVar n) t))]
    [(VBind n _) (hash-set env n (VNeu (NVar n) t))]))

(: swap-bindings (-> VEnv VBind VBind VEnv))
(define (swap-bindings env a b)
  (env-set env a (VNeu (NVar (VBind-name b)) (VBind-type b))))

(: env-ref (case-> (-> Env Symbol Value) (-> Env Symbol (-> Value) Value)))
(define env-ref
  (case-lambda
    [(env n) (hash-ref env n)]
    [(env n def) (hash-ref env n def)]))

; Equality

(: value=? (-> Value Value Boolean))
(define (value=? a b)
  (match (cons a b)
    [(cons (VNeu a _) (VNeu b _))
      ; TODO: Irrelevance check
      (neutral=? a b)]
    [(cons _ (VLam _ var _))
      (define var^ (VNeu (NVar (gensym)) (VBind-type var)))
      (value=? (do-app a var^) (do-app b var^))]
    [(cons (VLam _ var _) _)
      (define var^ (VNeu (NVar (gensym)) (VBind-type var)))
      (value=? (do-app a var^) (do-app b var^))]
    [(cons (VPi env-a x-a b-a) (VPi env-b x-b b-b))
      (define var^ (VNeu (NVar (gensym)) (VBind-type x-a)))
      (and
        (value=? (VBind-type x-a) (VBind-type x-b))
        (value=?
          (eval/expr (env-set env-a x-a var^) b-a)
          (eval/expr (env-set env-b x-b var^) b-b)))]
    [(cons (VType y-a x-a) (VType y-b x-b)) (and (= y-a y-b) (value=? x-a x-b))]
    [(cons (VLevel a) (VLevel b)) (= a b)]
    [(cons (VLZero) (VLZero)) #t]
    [(cons (VLSucc l) (VLSucc r)) (value=? l r)]
    [(cons (VEmptyT) (VEmptyT)) #t]
    [(cons (VUnitT) (VUnitT)) #t]
    [(cons (VUnit) (VUnit)) #t]
    [(cons (VEqT A-a from-a to-a) (VEqT A-b from-b to-b))
      (and (value=? A-a A-b) (value=? from-a from-b) (value=? to-a to-b))]
    [(cons (VRefl) (VRefl)) #t]
    [(cons (VW env-a t-a a-a) (VW env-b t-b a-b))
      (define var^ (VNeu (NVar (gensym)) (VBind-type t-a)))
      (and
        (value=? (VBind-type t-a) (VBind-type t-b))
        (value=?
          (eval/expr (env-set env-a t-a var^) a-a)
          (eval/expr (env-set env-b t-b var^) a-b)))]
    [(cons (Vw t-a d-a) (Vw t-b d-b))
      (and (value=? t-a t-b) (value=? d-a d-b))]
    [_ #f]))

(: neutral=? (-> Neutral Neutral Boolean))
(define (neutral=? a b)
  (match (cons a b)
    [(cons (NVar a) (NVar b)) (symbol=? a b)]
    [(cons (NApp f-a a-a) (NApp f-b a-b))
      (and (neutral=? f-a f-b) (value=? a-a a-b))]
    [(cons (NIndEmpty _ _ _) (NIndEmpty _ _ _)) #t]
    [(cons (NLMaxL l-a r-a) (NLMaxL l-b r-b))
      (and (neutral=? l-a l-b) (value=? r-a r-b))]
    [(cons (NLMaxR l-a r-a) (NLMaxR l-b r-b))
      (and (value=? l-a l-b) (neutral=? r-a r-b))]
    [(cons
      (NIndEq l-a to-a t-a m-a refl-a)
      (NIndEq l-b to-b t-b m-b refl-b))
      (and
        (value=? l-a l-b)
        (value=? to-a to-b)
        (neutral=? t-a t-b)
        (value=? m-a m-b)
        (value=? refl-a refl-b))]
    [(cons (NIndW l-a t-a m-a e-a) (NIndW l-b t-b m-b e-b))
      (and
        (value=? l-a l-b)
        (neutral=? t-a t-b)
        (value=? m-a m-b)
        (value=? e-a e-b))]
    [_ #f]))

; Bidirectional Type Checking

(: synth/expr (-> TEnv VEnv AstExpr (values TypedExpr Value)))
(define (synth/expr tenv venv e)
  (match e
    [(Var n)
      (values
        e
        (env-ref tenv n (λ () (error 'synth/expr "Undefined variable: ~a" n))))]
    [(Ann v t)
      (let*-values
        ([(t^ t-y t-x) (synth/expr-type tenv venv t)]
         [(t-v) (eval/expr venv t^)]
         [(v^) (check/expr tenv venv v t-v)])
        (values (Ann v^ t^) t-v))]
    [(Lam x b)
      (let*-values
        ([(x^ x-t x-t-y x-t-x) (synth/bind tenv venv x)]
         [(b-tenv) (env-set tenv x^ x-t)]
         [(b-venv) (env-set-neu venv x^ x-t)]
         [(b^ b-t) (synth/expr b-tenv b-venv b)])
         (values (Lam x^ b^) (VPi venv (eval/bind venv x^) (quote/value b-t))))]
    [(App f a)
      (define-values (f^ f-t) (synth/expr tenv venv f))
      (match f-t
        [(VPi b-venv x b)
          (define a^ (check/expr tenv venv a (VBind-type x)))
          (values
            (App f^ a^)
            (eval/expr (env-set b-venv x (eval/expr venv a^)) b))]
        [else
          (error 'synth/type "Expected ~a to be a function" (unparse/expr f))])]
    [(Pi x b)
      (let*-values
        ([(x^ x-t x-t-y x-t-x) (synth/bind tenv venv x)]
         [(b-tenv) (env-set tenv x^ x-t)]
         [(b-venv) (env-set-neu venv x^ x-t)]
         [(b^ b-y b-x) (synth/expr-type b-tenv b-venv b)])
        (values (Pi x^ b^) (tmax x-t-y b-y x-t-x b-x)))]
    [(Type y x)
      (let*-values
        ([(x^) (check/expr tenv venv x (VLevel y))]
         [(x-v) (eval/expr venv x^)])
        (values (Type y x^) (VType y (VLSucc x-v))))]
    [(IndEmpty l t m)
      (let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^) (check/expr tenv venv t (VEmptyT))]
         [(m^)
           (check/expr
             tenv
             venv
             m
             (VPi venv (VBind (gensym) (VEmptyT)) (Type l-y l^)))])
        (values (IndEmpty l^ t^ m^) (eval/expr venv (App m^ t^))))]
    [(UnitLit) (values e (VUnitT))]
    [(EqT A from to)
      (let*-values
        ([(A^ A-y A-x) (synth/expr-type tenv venv A)]
         [(A-v) (eval/expr venv A^)]
         [(from^) (check/expr tenv venv from A-v)]
         [(to^) (check/expr tenv venv to A-v)])
        (values (EqT A^ from^ to^) (VType A-y A-x)))]
    [(IndEq l to t m refl)
      (let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(to^ A-v) (synth/expr tenv venv to)]
         [(t^ from-v) (synth/expr-eq tenv venv t (eval/expr venv to^) A-v)]
         [(m-x) (gensym)]
         [(m^)
           (check/expr
             tenv
             venv
             m
             (VPi venv (VBind m-x A-v)
               (Pi (TypedBind (gensym)
                 (EqT (quote/value A-v) (quote/value from-v) (Var m-x))) (Type 0 l^))))]
         [(m-v) (eval/expr venv m^)]
         [(refl^)
           (check/expr
             tenv
             venv
             refl
             (do-app (do-app m-v from-v) (VRefl)))]
         [(to-v) (eval/expr venv to^)]
         [(t-v) (eval/expr venv t^)])
        (values
          (IndEq l^ to^ t^ m^ refl^)
          (do-app (do-app m-v to-v) t-v)))]
    [(W t a)
      (let*-values
        ([(t^ t-t t-t-y t-t-x) (synth/bind tenv venv t)]
         [(a-tenv) (env-set tenv t^ t-t)]
         [(a-venv) (env-set-neu venv t^ t-t)]
         [(a^ a-y a-x) (synth/expr-type a-tenv a-venv a)])
        (values (W t^ a^) (tmax t-t-y a-y t-t-x a-x)))]
    [(IndW l t m e)
      (let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^ t-t arity-env tag arity) (synth/expr-w tenv venv t)]
         [(m^)
           (check/expr tenv venv m
             (VPi venv (VBind (gensym) t-t) (Type l-y l^)))]
         [(tag-x) (VBind-name tag)]
         [(tag-t) (VBind-type tag)]
         [(e-t) (gensym 't)]
         [(e-d) (gensym 'd)]
         [(e-i) (gensym 'i)]
         [(e-B)
           (quote/value
             (eval/expr (env-set venv tag (VNeu (NVar e-t) tag-t)) arity))]
         [(e^)
           (check/expr tenv venv e
             (VPi venv (VBind e-t tag-t)
               (Pi
                 (TypedBind e-d (Pi (TypedBind (gensym) e-B) (quote/value t-t)))
                 (Pi (TypedBind e-i (Pi (TypedBind e-t e-B) (App m^ (App (Var e-d) (Var e-t)))))
                   (App m^ (w (Var e-t) (Var e-d)))))))]
         [(m-v) (eval/expr venv m^)]
         [(t-v) (eval/expr venv t^)])
        (values (IndW l^ t^ m^ e^) (do-app m-v t-v)))]
    [else (error 'synth/expr "Cannot synthesize type for ~a" (unparse/expr e))]))

(: tmax (-> Natural Natural Value Value Value))
(define (tmax a-y b-y a-x b-x)
  (cond
    [(= a-y b-y) (VType a-y (do-lmax a-x b-x))]
    [(> a-y b-y) (VType a-y a-x)]
    [else (VType b-y b-x)]))

(: synth/expr-w
  (-> TEnv VEnv AstExpr (values TypedExpr Value VEnv VBind TypedExpr)))
(define (synth/expr-w tenv venv w)
  (define-values (w^ w-t) (synth/expr tenv venv w))
  (match w-t
    [(VW env t a) (values w^ w-t env t a)]
    [else
      (error 'synth/expr-w "Expected ~a to be a W type, but is a ~a"
        (unparse/expr w)
        (unparse/expr (quote/value w-t)))]))

(: synth/expr-eq (-> TEnv VEnv AstExpr Value Value (values TypedExpr Value)))
(define (synth/expr-eq tenv venv t to-v A-v)
  (define-values (t^ t-t) (synth/expr tenv venv t))
  (match t-t
    [(VEqT A-v^ from-v to-v^)
      (cond
        [(not (value=? A-v^ A-v))
          (error 'synth/expr-eq
            "Expected equality to be at type ~a, but is at type ~a"
            (unparse/expr (quote/value A-v))
            (unparse/expr (quote/value A-v^)))]
        [(not (value=? to-v to-v^))
          (error 'synth/expr-eq
            "Expected right-hand side of equality to be ~a, but is ~a"
            (unparse/expr (quote/value to-v))
            (unparse/expr (quote/value to-v^)))]
        [else (values t^ from-v)])]
    [else
      (error 'synth/expr-eq "Expected ~a to be an equality, but is of type ~a"
        (unparse/expr t)
        (unparse/expr (quote/value t-t)))]))

(: synth/expr-type (-> TEnv VEnv AstExpr (values TypedExpr Natural Value)))
(define (synth/expr-type tenv venv t)
  (define-values (t^ t-t) (synth/expr tenv venv t))
  (match t-t
    [(VType y x) (values t^ y x)]
    [else
      (error 'synth/expr-type "Expected ~a to be a type, but is a ~a"
        (unparse/expr t)
        (unparse/expr (quote/value t-t)))]))

(: synth/expr-level (-> TEnv VEnv AstExpr (values TypedExpr Natural)))
(define (synth/expr-level tenv venv l)
  (define-values (l^ l-t) (synth/expr tenv venv l))
  (match l-t
    [(VLevel y) (values l^ y)]
    [else
      (error 'synth/expr-type "Expected ~a to be a level, but is a ~a"
        (unparse/expr l)
        (unparse/expr (quote/value l-t)))]))

(: synth/bind (-> TEnv VEnv AstBind (values TBind Value Natural Value)))
(define (synth/bind tenv venv b)
  (match b
    [(UntypedBind _)
      (error 'synth/bind "Cannot infer type for bind: ~a" (unparse/bind b))]
    [(TypedBind n t)
      (define-values (t^ t-y t-x) (synth/expr-type tenv venv t))
      (values (TypedBind n t^) (eval/expr venv t^) t-y t-x)]))

(: check/expr (-> TEnv VEnv AstExpr Value TypedExpr))
(define (check/expr tenv venv e t)
  (match (cons e t)
    [(cons (Lam x b) (VPi p-venv p-x p-b))
      (define x^ (check/bind tenv venv x (VBind-type p-x)))
      (define b-tenv (env-set tenv x^ (VBind-type p-x)))
      (define b-venv (env-set-neu venv x^ (VBind-type p-x)))
      (Lam
        x^
        (check/expr
          b-tenv
          b-venv
          b
          (eval/expr (swap-bindings p-venv p-x (eval/bind venv x^)) p-b)))]
    [(cons (Lam _ _) _)
      (error
        'check/expr
        "Expected expression of type ~a, but found ~a"
        (unparse/expr (quote/value t))
        (unparse/expr e))]
    [(cons (LZero) (VLevel _)) (LZero)]
    [(cons (LSucc l) (VLevel _))
      (let*-values
        ([(l^) (check/expr tenv venv l t)])
        (LSucc l^))]
    [(cons (LMax l r) (VLevel _))
      (let*-values
        ([(l^) (check/expr tenv venv l t)]
         [(r^) (check/expr tenv venv r t)])
        (LMax l^ r^))]
    [(cons (Refl) (VEqT A a b))
      (if (value=? a b)
        (Refl)
        (error 'check/expr "Expected ~a and ~a to be the same ~a"
          (unparse/expr (quote/value a))
          (unparse/expr (quote/value b))
          (unparse/expr (quote/value A))))]
    [(cons (EmptyT) (VType _ _)) (EmptyT)]
    [(cons (UnitT) (VType _ _)) (UnitT)]
    [(cons (Level l-y) (VType t-y _))
      (if (= (add1 l-y) t-y)
        (Level l-y)
        (error 'check/expr "Expected ~a to be at level ~a"
          (unparse/expr e)
          (sub1 t-y)))]
    [(cons (w tag-e d) (VW arity-env tag arity))
      (let*-values
        ([(tag-e^) (check/expr tenv venv tag-e (VBind-type tag))]
         [(tag-e-v) (eval/expr venv tag-e^)]
         [(d^)
           (check/expr tenv venv d
             (VPi arity-env (VBind (gensym) (eval/expr (env-set arity-env tag tag-e-v) arity)) (quote/value t)))])
        (w tag-e^ d^))]
    [else
      (define-values (e^ t^) (synth/expr tenv venv e))
      (if (not (value=? t t^))
        (error
          'check/expr
          "Expected ~a to be of type ~a, but is of type ~a"
          (unparse/expr e)
          (unparse/expr (quote/value t))
          (unparse/expr (quote/value t^)))
        e^)]))

(: check/bind (-> TEnv VEnv AstBind Value TBind))
(define (check/bind tenv venv b t)
  (match b
    [(UntypedBind n) (TypedBind n (quote/value t))]
    [(TypedBind n b-t)
      (define-values (b-t^ b-t-y b-t-x) (synth/expr-type tenv venv b-t))
      (if (not (value=? t (eval/expr venv b-t^)))
        (error
          'check/bind
          "Expected bind ~a to be of type ~a, but is of type ~a"
          (unparse/bind b)
          (unparse/expr (quote/value t))
          (unparse/expr b-t))
        (TypedBind n b-t^))]))

(: check/bind-expr (-> TEnv VEnv AstBind AstExpr (values TBind TypedExpr Value)))
(define (check/bind-expr tenv venv b e)
  (match b
    [(UntypedBind n)
      (define-values (e^ e-t) (synth/expr tenv venv e))
      (values (TypedBind n (quote/value e-t)) e^ e-t)]
    [(TypedBind n t)
      (define-values (t^ t-y t-x) (synth/expr-type tenv venv t))
      (define t-v (eval/expr venv t^))
      (define e^ (check/expr tenv venv e t-v))
      (values (TypedBind n t^) e^ t-v)]))

; Unparse

(: unparse/expr (-> AstExpr Any))
(define (unparse/expr e)
  (match e
    [(Var n) n]
    [(Ann v t) `(,(unparse/expr v) : ,(unparse/expr t))]
    [(Lam x b) `(λ ,(unparse/bind x) ,(unparse/expr b))]
    [(App f a) (unparse/app e)]
    [(Pi x b) `(-> ,(unparse/bind x) ,(unparse/expr b))]
    [(Type y x) `(Type ,y ,(unparse/expr x))]
    [(Level y) `(Level ,y)]
    [(LZero) `lzero]
    [(LSucc l) `(lsucc ,(unparse/expr l))]
    [(LMax l r) `(lmax ,(unparse/expr l) ,(unparse/expr r))]
    [(EmptyT) 'Empty]
    [(IndEmpty l t m) `(ind-Empty ,(unparse/expr l) ,(unparse/expr t) ,(unparse/expr m))]
    [(UnitT) 'Unit]
    [(UnitLit) '()]
    [(EqT A from to) `(= ,(unparse/expr A) ,(unparse/expr from) ,(unparse/expr to))]
    [(Refl) `Refl]
    [(IndEq l to t m refl)
      `(ind-= ,(unparse/expr l) ,(unparse/expr to) ,(unparse/expr t)
        ,(unparse/expr m) ,(unparse/expr refl))]
    [(W t a) `(W ,(unparse/bind t) ,(unparse/expr a))]
    [(w t d) `(w ,(unparse/expr t) ,(unparse/expr d))]
    [(IndW l t m e)
      `(ind-W ,(unparse/expr l) ,(unparse/expr t) ,(unparse/expr m)
        ,(unparse/expr e))]))

(: unparse/app (-> AstExpr (Listof Any)))
(define (unparse/app e)
  (match e
    [(App f a) `(,@(unparse/app f) ,(unparse/expr a))]
    [else `(,(unparse/expr e))]))

(: unparse/bind (-> AstBind Any))
(define (unparse/bind b)
  (match b
    [(UntypedBind n) n]
    [(TypedBind n t) `(,n : ,(unparse/expr t))]))
