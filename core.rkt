#lang typed/racket

(provide (all-defined-out))

; Expr functor parameterized by bind type
(define-type (Expr b r)
  (U Var (Lam b r) (App r) (Pi r) (Let b r) (Type r) Level LZero (LSucc r)
    (LMax r) EmptyT (IndEmpty r) UnitT UnitLit (EqT r) (Refl r) (IndEq r)))

(struct Var ([name : Symbol]) #:transparent)

(struct (b r) Lam ([var : b] [body : r]) #:transparent)

(struct (r) App ([fun : r] [arg : r]) #:transparent)

(struct (r) Pi ([var : (TypedBind r)] [body : r]) #:transparent)

(struct (b r) Let ([var : b] [val : r] [body : r]) #:transparent)

(struct (r) Type ([y : Natural] [x : r]) #:transparent)

(struct Level ([y : Natural]) #:transparent)

(struct LZero () #:transparent)

(struct (r) LSucc ([l : r]) #:transparent)

(struct (r) LMax ([l : r] [r : r]) #:transparent)

(struct EmptyT () #:transparent)

(struct (r) IndEmpty ([level : r] [motive : r] [target : r]) #:transparent)

(struct UnitT () #:transparent)

(struct UnitLit () #:transparent)

(struct (r) EqT ([type : r] [l : r] [r : r]) #:transparent)

(struct (r) Refl ([x : r]) #:transparent)

(struct (r) IndEq
  ([l : r] [type : r] [from : r] [to : r] [m : r] [t : r] [refl : r])
  #:transparent)

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
  (U VNeu VLam VPi VType VLevel VLZero VLSucc VEmptyT VUnitT VUnit VEqT VRefl))

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

(struct VRefl ([x : Value]) #:transparent)

(struct VBind ([name : Symbol] [type : Value]) #:transparent)

(define-type Neutral
  (U NVar NApp NIndEmpty NLMaxL NLMaxR NIndEq))

(struct NVar ([name : Symbol]) #:transparent)

(struct NApp ([fun : Neutral] [arg : Value]) #:transparent)

(struct NIndEmpty ([level : Value] [motive : Value] [target : Neutral]) #:transparent)

(struct NLMaxL ([l : Neutral] [r : Value]) #:transparent)

(struct NLMaxR ([l : Value] [r : Neutral]) #:transparent)

(struct NIndEq
  ([l : Value] [type : Value] [from : Value] [to : Value] [m : Value]
    [t : Neutral] [refl : Value])
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
    [(? symbol?) (parse/variable e)]
    [`(,(or 'λ 'lam) ,v ,b) (Lam (parse/bind v) (parse/expr b))]
    [`(,(or 'Π 'Pi '->) ,v ,b) (Pi (parse/typed-bind v) (parse/expr b))]
    [`(let ,x ,v ,b) (Let (parse/bind x) (parse/expr v) (parse/expr b))]
    [`(Type ,(? natural? y) ,x) (Type y (parse/expr x))]
    [`(Level ,(? natural? y)) (Level y)]
    [`(lsucc ,l) (LSucc (parse/expr l))]
    [`(lmax ,l ,r) (LMax (parse/expr l) (parse/expr r))]
    [`(ind-Empty ,l ,m ,t)
      (IndEmpty (parse/expr l) (parse/expr m) (parse/expr t))]
    [`() (UnitLit)]
    [`(= ,t ,l ,r) (EqT (parse/expr t) (parse/expr l) (parse/expr r))]
    [`(Refl ,x) (Refl (parse/expr x))]
    [`(ind-= ,l ,type ,from ,to ,m ,t ,r)
      (IndEq (parse/expr l) (parse/expr type) (parse/expr from) (parse/expr to)
        (parse/expr m) (parse/expr t) (parse/expr r))]
    [`(,f ,a ...)
      (foldl
        (λ ([a : AstExpr] [f : AstExpr]) (App f a))
        (parse/expr f)
        (map parse/expr a))]
    [else (error 'parse/expr "Invalid Expr: ~a" e)]))

(: variable? (-> Symbol Boolean))
(define (variable? v)
  (not (member v '(λ lam Π Pi -> : let Empty ind-Empty Unit lzero lsucc lmax Level Type))))

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
    [(Lam x b) (VLam env (eval/bind env x) b)]
    [(App f a) (do-app (eval/expr env f) (eval/expr env a))]
    [(Pi x b) (VPi env (eval/bind env x) b)]
    [(Let var val body) (eval/expr (env-set env var (eval/expr env val)) body)]
    [(Type y x) (VType y (eval/expr env x))]
    [(Level y) (VLevel y)]
    [(LZero) (VLZero)]
    [(LSucc l) (VLSucc (eval/expr env l))]
    [(LMax l r) (do-lmax (eval/expr env l) (eval/expr env r))]
    [(EmptyT) (VEmptyT)]
    [(IndEmpty l m t)
      (do-ind-empty (eval/expr env l) (eval/expr env m) (eval/expr env t))]
    [(UnitT) (VUnitT)]
    [(UnitLit) (VUnit)]
    [(EqT t l r) (VEqT (eval/expr env t) (eval/expr env l) (eval/expr env r))]
    [(Refl x) (VRefl (eval/expr env x))]
    [(IndEq l type from to m t refl)
      (do-ind-eq (eval/expr env l) (eval/expr env type) (eval/expr env from)
        (eval/expr env to) (eval/expr env m) (eval/expr env t)
        (eval/expr env refl))]))

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
    [(VRefl x) (Refl (quote/value x))]))

(: quote/neutral (-> Neutral TypedExpr))
(define (quote/neutral n)
  (match n
    [(NVar n) (Var n)]
    [(NApp f a) (App (quote/neutral f) (quote/value a))]
    [(NIndEmpty l m n) (IndEmpty (quote/value l) (quote/value m) (quote/neutral n))]
    [(NLMaxL l r) (LMax (quote/neutral l) (quote/value r))]
    [(NLMaxR l r) (LMax (quote/value l) (quote/neutral r))]
    [(NIndEq l A from to m t refl)
      (IndEq (quote/value l) (quote/value A) (quote/value from) (quote/value to)
        (quote/value m) (quote/neutral t) (quote/value refl))]))

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
(define (do-ind-empty l m t)
  (match t
    [(VNeu n (VEmptyT)) (VNeu (NIndEmpty l m n) (do-app m t))]))

(: do-ind-eq (-> Value Value Value Value Value Value Value Value))
(define (do-ind-eq l type from to m t refl)
  (match t
    [(VRefl x) refl]
    [(VNeu n (VEqT _ _ _))
      (VNeu (NIndEq l type from to m n refl) (do-app (do-app m to) t))]))

(: do-lmax (-> Value Value Value))
(define (do-lmax l r)
  (match (cons l r)
    [(cons (VNeu n t) r) (VNeu (NLMaxL n r) t)]
    [(cons l (VNeu n t)) (VNeu (NLMaxR l n) t)]
    [(cons l r) (add-levels l r)]))

(: add-levels (-> Value Value Value))
(define (add-levels l r)
  (match (cons l r)
    [(cons (VLZero) r) r]
    [(cons l (VLZero)) l]
    [(cons (VLSucc l) r) (add-levels l (VLSucc r))]))

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
    [(cons (VRefl a) (VRefl b)) (value=? a b)]
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
      (NIndEq l-a A-a from-a to-a m-a t-a refl-a)
      (NIndEq l-b A-b from-b to-b m-b t-b refl-b))
      (and
        (value=? l-a l-b)
        (value=? A-a A-b)
        (value=? from-a from-b)
        (value=? to-a to-b)
        (value=? m-a m-b)
        (neutral=? t-a t-b)
        (value=? refl-a refl-b))]
    [_ #f]))

; Bidirectional Type Checking

(: synth/expr (-> TEnv VEnv AstExpr (values TypedExpr Value)))
(define (synth/expr tenv venv e)
  (match e
    [(Var n)
      (values
        e
        (env-ref tenv n (λ () (error 'synth/expr "Undefined variable: ~a" n))))]
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
         [(b^ b-y b-x) (synth/expr-type b-tenv b-venv b)]
         [(t-y) (max x-t-y b-y)]
         [(t-x)
           (cond
             [(= x-t-y b-y) (do-lmax x-t-x b-x)]
             [(> x-t-y b-y) x-t-x]
             [else b-x])])
        (values (Pi x^ b^) (VType t-y t-x)))]
    [(Let x v b)
      (let*-values
        ([(x^ v^ v-t) (check/bind-expr tenv venv x v)]
         [(b-tenv) (env-set tenv x^ v-t)]
         [(b-venv) (env-set tenv x^ (eval/expr venv v^))]
         [(b^ b-t) (synth/expr b-tenv b-venv b)])
        (values (Let x^ v^ b^) b-t))]
    [(Type y x)
      (let*-values
        ([(x^) (check/expr tenv venv x (VLevel y))]
         [(x-v) (eval/expr venv x^)])
        (values (Type y x^) (VType y (VLSucc x-v))))]
    [(Level y) (values e (VType (+ y 1) (VLZero)))]
    [(EmptyT) (values e (VType 0 (VLZero)))]
    [(IndEmpty l m t)
      (let*-values
        ([(l^) (check/expr tenv venv l (VLevel 0))]
         [(m^)
           (check/expr
             tenv
             venv
             m
             (VPi venv (VBind (gensym) (VEmptyT)) (Type 0 l^)))]
         [(t^) (check/expr tenv venv t (VEmptyT))])
        (values (IndEmpty l^ m^ t^) (eval/expr venv (App m^ t^))))]
    [(UnitT) (values e (VType 0 (VLZero)))]
    [(UnitLit) (values e (VUnitT))]
    [(EqT A from to)
      (let*-values
        ([(A^ A-y A-x) (synth/expr-type tenv venv A)]
         [(A-v) (eval/expr venv A^)]
         [(from^) (check/expr tenv venv from A-v)]
         [(to^) (check/expr tenv venv to A-v)])
        (values (EqT A^ from^ to^) (VType A-y A-x)))]
    [(Refl x)
      (let*-values
        ([(x^ x-t) (synth/expr tenv venv x)]
         [(x-v) (eval/expr venv x^)])
        (values (Refl x^) (VEqT x-t x-v x-v)))]
    [(IndEq l A from to m t refl)
      (let*-values
        ([(l^) (check/expr tenv venv l (VLevel 0))]
         [(A^ A-y A-x) (synth/expr-type tenv venv A)]
         [(A-v) (eval/expr venv A^)]
         [(from^) (check/expr tenv venv from A-v)]
         [(to^) (check/expr tenv venv to A-v)]
         [(m-x) (gensym)]
         [(m^)
           (check/expr
             tenv
             venv
             m
             (VPi venv (VBind m-x A-v)
               (Pi (TypedBind (gensym)
                 (EqT A^ from^ (Var m-x))) (Type 0 l^))))]
         [(from-v) (eval/expr venv from^)]
         [(to-v) (eval/expr venv to^)]
         [(t^) (check/expr tenv venv t (VEqT A-v from-v to-v))]
         [(m-v) (eval/expr venv m^)]
         [(refl^)
           (check/expr
             tenv
             venv
             refl
             (do-app (do-app m-v from-v) (VRefl from-v)))]
         [(t-v) (eval/expr venv t^)])
        (values
          (IndEq l^ A^ from^ to^ m^ t^ refl^)
          (do-app (do-app m-v to-v) t-v)))]))

(: synth/expr-type (-> TEnv VEnv AstExpr (values TypedExpr Natural Value)))
(define (synth/expr-type tenv venv t)
  (define-values (t^ t-t) (synth/expr tenv venv t))
  (match t-t
    [(VType y x) (values t^ y x)]
    [else
      (error
        'synth/expr-type
        "Expected ~a to be a type, but is a ~a"
        (unparse/expr t)
        (unparse/expr (quote/value t-t)))]))

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
    [(cons (Let x v b) _)
      (let*-values
        ([(x^ v^ v-t) (check/bind-expr tenv venv x v)]
         [(b-tenv) (env-set tenv x^ v-t)]
         [(b-venv) (env-set tenv x^ (eval/expr venv v^))]
         [(b^) (check/expr b-tenv b-venv b t)])
        (Let x^ v^ b^))]
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
    [(Lam x b) `(λ ,(unparse/bind x) ,(unparse/expr b))]
    [(App f a) (unparse/app e)]
    [(Pi x b) `(-> ,(unparse/bind x) ,(unparse/expr b))]
    [(Let x v b) `(let ,(unparse/bind x) ,(unparse/expr v) ,(unparse/expr b))]
    [(Type y x) `(Type ,y ,(unparse/expr x))]
    [(Level y) `(Level ,y)]
    [(LZero) `lzero]
    [(LSucc l) `(lsucc ,(unparse/expr l))]
    [(LMax l r) `(lmax ,(unparse/expr l) ,(unparse/expr r))]
    [(EmptyT) 'Empty]
    [(IndEmpty l m t) `(ind-Empty ,(unparse/expr l) ,(unparse/expr m) ,(unparse/expr t))]
    [(UnitT) 'Unit]
    [(UnitLit) '()]
    [(EqT A from to) `(= ,(unparse/expr A) ,(unparse/expr from) ,(unparse/expr to))]
    [(Refl x) `(Refl ,(unparse/expr x))]
    [(IndEq l A from to m t refl)
      `(ind-= ,(unparse/expr l) ,(unparse/expr A) ,(unparse/expr from)
        ,(unparse/expr to) ,(unparse/expr m) ,(unparse/expr t)
        ,(unparse/expr refl))]))

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
