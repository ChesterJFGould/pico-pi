#lang typed/racket

(provide (all-defined-out))

(define-type (Expr b r)
  (U Var (Ann r) (Lam b r) (App r) (BindT r) (Type r) LevelT LZero (LSucc r)
    (LMax r) EmptyT (IndEmpty r) UnitT Unit (EqT r) Refl (IndEq r) (W r)
    (IndW r) BoolT Bool (IndBool r) (Cons r) (First r) (Second r) TODO))
(struct Var ([name : Symbol]))
(struct (r) Ann ([val : r] [type : r]))
(struct (b r) Lam ([x : b] [body : r]))
(struct (r) App ([f : r] [a : r]))
(struct (r) BindT ([kind : BindKind] [x : (TypedBind r)] [body : r]))
(struct (r) Type ([y : Natural] [x : r]))
(struct LevelT ([y : Natural]))
(struct LZero ())
(struct (r) LSucc ([val : r]))
(struct (r) LMax ([l : r] [r : r]))
(struct EmptyT ())
(struct (r) IndEmpty ([l : r] [t : r] [m : r]))
(struct UnitT ())
(struct Unit ())
(struct (r) EqT ([type : r] [from : r] [to : r]))
(struct Refl ())
(struct (r) IndEq ([l : r] [t : r] [m : r] [refl : r]))
(struct (r) W ([tag : r] [data : r]))
(struct (r) IndW ([l : r] [t : r] [m : r] [e : r]))
(struct BoolT ())
(struct Bool ([val : Boolean]))
(struct (r) IndBool ([l : r] [t : r] [m : r] [true : r] [false : r]))
(struct (r) Cons ([fst : r] [snd : r]))
(struct (r) First ([val : r]))
(struct (r) Second ([val : r]))
(struct TODO ())

(define-type BindKind (U 'Pi 'Sigma 'W))
(struct (r) TypedBind ([x : Symbol] [type : r]))
(struct UntypedBind ([name : Symbol]))
(define-type (Bind r) (U (TypedBind r) UntypedBind))
(define-type AstBind (Bind AstExpr))
(define-type AstTBind (TypedBind AstExpr))
(define-type AstExpr (Expr AstBind AstExpr))
(define-type TBind (TypedBind TypedExpr))
(define-type TypedExpr (Expr TBind TypedExpr))

(define-type Value
  (U VChoice VNeu VClos VType VLevelT VLZero VLSucc VEmptyT VUnitT VUnit VEqT
    VRefl VW VBoolT VBool VCons))
(struct VChoice ([neu : (Promise Value)] [val : (Promise Value)]))
(struct VNeu ([neu : Neutral] [type : (Promise Value)]))
(struct VClos ([env : VEnv] [expr : TypedExpr]))
(struct VType ([y : Natural] [x : Value]))
(struct VLevelT ([y : Natural]))
(struct VLZero ())
(struct VLSucc ([l : Value]))
(struct VEmptyT ())
(struct VUnitT ())
(struct VUnit ())
(struct VEqT ([type : Value] [l : Value] [r : Value]))
(struct VRefl ())
(struct VW ([tag : Value] [data : Value]))
(struct VBoolT ())
(struct VBool ([val : Boolean]))
(struct VCons ([fst : Value] [snd : Value]))

(define-type Neutral
  (U NVar NApp NIndEmpty NLMaxL NLMaxR NIndEq NIndW NIndBool NFirst NSecond))
(struct NVar ([x : Symbol]))
(struct NApp ([f : Neutral] [a : Value]))
(struct NIndEmpty ([l : Value] [t : Neutral] [m : Value]))
(struct NLMaxL ([l : Neutral] [r : Value]))
(struct NLMaxR ([l : Value] [r : Neutral]))
(struct NIndEq ([l : Value] [t : Neutral] [m : Value] [refl : Value]))
(struct NIndW ([l : Value] [t : Neutral] [m : Value] [e : Value]))
(struct NIndBool
  ([l : Value] [t : Neutral] [m : Value] [true : Value] [false : Value]))
(struct NFirst ([e : Neutral]))
(struct NSecond ([e : Neutral]))

(define-type (Env a) (HashTable Symbol a))
(define-type TEnv (Env (Pairof Symbol Value)))
(define-type VEnv (Env Value))

;; Env

(: empty-env (All (a) (-> (Env a))))
(define (empty-env) (hash))

(: env-get (All (a) (-> (Env a) Symbol a)))
(define (env-get env x)
  (hash-ref env x))

(: env-set (All (a) (-> (Env a) Symbol a (Env a))))
(define (env-set env x v)
  (hash-set env x v))

(: env-set* (All (a) (-> (Env a) (Listof Symbol) (Listof a) (Env a))))
(define (env-set* env xs vs)
  (foldr
    (λ ([x : Symbol] [v : a] [env : (Env a)]) (env-set env x v))
    env
    xs
    vs))

(: in-env? (All (a) (-> (Env a) Symbol Boolean)))
(define (in-env? env x)
  (hash-has-key? env x))

;; Parsing

(: parse/expr (-> Any AstExpr))
(define (parse/expr e)
  (match e
    ['Unit (UnitT)]
    ['Empty (EmptyT)]
    [`lzero (LZero)]
    [`Refl (Refl)]
    [`Bool (BoolT)]
    [`true (Bool #t)]
    [`false (Bool #f)]
    ['? (TODO)]
    [(? symbol?) (parse/variable e)]
    [`(,e : ,t) (Ann (parse/expr e) (parse/expr t))]
    [`(,(or 'λ 'lam) ,b ,bs ... ,e)
      (Lam (parse/bind b)
        (foldr
          (ann Lam (-> AstBind AstExpr AstExpr))
          (parse/expr e)
          (map parse/bind bs)))]
    [`(,(or 'Π 'Pi '->) ,b ,bs ... ,e)
      (BindT 'Pi (parse/typed-bind b)
        (foldr
          (curry (ann BindT (-> BindKind AstTBind AstExpr AstExpr)) 'Pi)
          (parse/expr e)
          (map parse/typed-bind bs)))]
    [`(Type ,(? natural? y) ,x) (Type y (parse/expr x))]
    [`(Level ,(? natural? y)) (LevelT y)]
    [`(lsucc ,l) (LSucc (parse/expr l))]
    [`(lmax ,l ,r) (LMax (parse/expr l) (parse/expr r))]
    [`(ind-Empty ,l ,t ,m)
      (IndEmpty (parse/expr l) (parse/expr t) (parse/expr m))]
    [`() (Unit)]
    [`(= ,t ,l ,r) (EqT (parse/expr t) (parse/expr l) (parse/expr r))]
    [`(ind-= ,l ,t ,m ,refl)
      (IndEq (parse/expr l) (parse/expr t) (parse/expr m) (parse/expr refl))]
    [`(W ,t ,a) (BindT 'W (parse/typed-bind t) (parse/expr a))]
    [`(w ,t ,d) (W (parse/expr t) (parse/expr d))]
    [`(ind-W ,l ,t ,m ,e)
      (IndW (parse/expr l) (parse/expr t) (parse/expr m) (parse/expr e))]
    [`(ind-Bool ,l ,t ,m ,true ,false)
      (IndBool (parse/expr l) (parse/expr t) (parse/expr m) (parse/expr true)
        (parse/expr false))]
    [`(,(or 'Σ 'Sigma) ,b ,bs ... ,s)
      (BindT 'Sigma (parse/typed-bind b)
        (foldr
          (curry (ann BindT (-> BindKind AstTBind AstExpr AstExpr)) 'Sigma)
          (parse/expr s)
          (map parse/typed-bind bs)))]
    [`(cons ,f ,s) (Cons (parse/expr f) (parse/expr s))]
    [`(first ,p) (First (parse/expr p))]
    [`(second ,p) (Second (parse/expr p))]
    [`(,f ,a ,as ...)
      (foldl
        (λ ([a : AstExpr] [f : AstExpr]) (App f a))
        (App (parse/expr f) (parse/expr a))
        (map parse/expr as))]
    [else (error 'parse/expr "Invalid Expr: ~a" e)]))

(: variable? (-> Symbol Boolean))
(define (variable? v)
  (not
    (member v '(λ lam Π Pi -> : Empty ind-Empty Unit lzero lsucc lmax Level Type
      W w ind-W = ind-= Refl true false Bool ind-Bool Σ Sigma cons first second
      ?))))

(: parse/variable (-> Symbol AstExpr))
(define (parse/variable x)
  (match x
    [(? variable?) (Var x)]
    [else (error 'parse/variable "Invalid Variable: ~a" x)]))

(: parse/bind (-> Any AstBind))
(define (parse/bind b)
  (match b
    [(? symbol? x) #:when (variable? x) (UntypedBind x)]
    [`(,(? symbol? x) : ,t) #:when (variable? x) (TypedBind x (parse/expr t))]
    [else (error 'parse/bind "Invalid Bind: ~a" b)]))

(: parse/typed-bind (-> Any AstTBind))
(define (parse/typed-bind b)
  (match b
    [`(,(? symbol? x) : ,t) #:when (variable? x) (TypedBind x (parse/expr t))]
    [else (TypedBind (gensym '_) (parse/expr b))]))

;; Evaluation

(: eval/expr (-> VEnv TypedExpr Value))
(define (eval/expr env e)
  (match e
    [(Var x) (env-get env x)]
    [(Ann v _) (eval/expr env v)]
    [(Lam _ _) (VClos env e)]
    [(App f a) (do-app (eval/expr env f) (eval/expr env a))]
    [(BindT _ _ _) (VClos env e)]
    [(Type y x) (VType y (eval/expr env x))]
    [(LevelT y) (VLevelT y)]
    [(LZero) (VLZero)]
    [(LSucc l) (VLSucc (eval/expr env l))]
    [(LMax l r) (do-lmax (eval/expr env l) (eval/expr env r))]
    [(EmptyT) (VEmptyT)]
    [(IndEmpty l t m)
      (do-ind-empty (eval/expr env l) (eval/expr env t) (eval/expr env m))]
    [(UnitT) (VUnitT)]
    [(Unit) (VUnit)]
    [(EqT t l r) (VEqT (eval/expr env t) (eval/expr env l) (eval/expr env r))]
    [(Refl) (VRefl)]
    [(IndEq l t m refl)
      (do-ind-eq (eval/expr env l) (eval/expr env t) (eval/expr env m)
        (eval/expr env refl))]
    [(W t d) (VW (eval/expr env t) (eval/expr env d))]
    [(IndW l t m e)
      (do-ind-w (eval/expr env l) (eval/expr env t) (eval/expr env m)
        (eval/expr env e))]
    [(BoolT) (VBoolT)]
    [(Bool v) (VBool v)]
    [(IndBool l t m true false)
      (do-ind-bool (eval/expr env l) (eval/expr env t) (eval/expr env m)
        (eval/expr env true) (eval/expr env false))]
    [(Cons f s) (VCons (eval/expr env f) (eval/expr env s))]
    [(First e) (do-first (eval/expr env e))]
    [(Second e) (do-second (eval/expr env e))]))

(: whnf (-> Value Value))
(define (whnf v)
  (match v
    [(VChoice _ v) (whnf (force v))]
    [else v]))

(: do-app (-> Value Value Value))
(define (do-app f a)
  (match f
    [(VClos env (Lam (TypedBind x _) b)) (eval/expr (env-set env x a) b)]
    [(VNeu n t)
      (VNeu
        (NApp n a)
        (lazy
          (match-let*
            ([(VClos env (BindT 'Pi (TypedBind x _) b)) (whnf (force t))])
            (eval/expr (env-set env x a) b))))]
    [(VChoice n v)
      (VChoice (lazy (do-app (force n) a)) (lazy (do-app (force v) a)))]))

(: do-lmax (-> Value Value Value))
(define (do-lmax l r)
  (match (cons l r)
    [(cons _ (VLZero)) l]
    [(cons (VLZero) _) r]
    [_ #:when (value=? l r) l]
    [(cons (VNeu n t) r) (VNeu (NLMaxL n r) t)]
    [(cons l (VNeu n t)) (VNeu (NLMaxR l n) t)]
    [(cons (VChoice n v) r)
      (VChoice (lazy (do-lmax (force n) r)) (lazy (do-lmax (force v) r)))]
    [(cons l (VChoice n v))
      (VChoice (lazy (do-lmax l (force n))) (lazy (do-lmax l (force v))))]
    [(cons (VLSucc l) (VLSucc r)) (VLSucc (do-lmax l r))]))

(: do-ind-empty (-> Value Value Value Value))
(define (do-ind-empty l t m)
  (match t
    [(VNeu n _) (VNeu (NIndEmpty l n m) (lazy m))]
    [(VChoice n v)
      (VChoice
        (lazy (do-ind-empty l (force n) m))
        (lazy (do-ind-empty l (force v) m)))]))

(: do-ind-eq (-> Value Value Value Value Value))
(define (do-ind-eq l t m refl)
  (match t
    [(VRefl) refl]
    [(VNeu n n-t)
      (VNeu
        (NIndEq l n m refl)
        (lazy
          (match-let
            ([(VEqT _ to _) (whnf (force n-t))])
            (do-app (do-app m to) t))))]
    [(VChoice n v)
      (VChoice
        (lazy (do-ind-eq l (force n) m refl))
        (lazy (do-ind-eq l (force v) m refl)))]))

(: do-ind-w (-> Value Value Value Value Value))
(define (do-ind-w l t m e)
  (match t
    [(VW t d)
      (define t-n (gensym 't))
      (define-values (t-t env)
        (match (whnf d)
          [(VClos env (Lam (TypedBind _ t) _)) (values t env)]
          [(VNeu _ n-t)
            (match (whnf (force n-t))
              [(VClos env (BindT 'Pi (TypedBind _ t) _))
                (values t env)])]))
      (define l-n (gensym 'l))
      (define d-n (gensym 'd))
      (define m-n (gensym 'm))
      (define e-n (gensym 'e))
      (: env^ VEnv)
      (define env^
        (env-set* env
          (list l-n d-n m-n e-n)
          (list l d m e)))
      (do-app
        (do-app (do-app e t) d)
        (VClos env^
          (Lam (TypedBind t-n t-t)
            (IndW (Var l-n) (App (Var d-n) (Var t-n)) (Var m-n) (Var e-n)))))]
    [(VNeu n _) (VNeu (NIndW l n m e) (lazy (do-app m t)))]
    [(VChoice n v)
      (VChoice
        (lazy (do-ind-w l (force n) m e))
        (lazy (do-ind-w l (force v) m e)))]))

(: do-ind-bool (-> Value Value Value Value Value Value))
(define (do-ind-bool l t m true false)
  (match t
    [(VBool #t) true]
    [(VBool #f) false]
    [(VNeu n _) (VNeu (NIndBool l n m true false) (lazy (do-app m t)))]
    [(VChoice n v)
      (VChoice
        (lazy (do-ind-bool l (force n) m true false))
        (lazy (do-ind-bool l (force v) m true false)))]))

(: do-first (-> Value Value))
(define (do-first c)
  (match c
    [(VCons f _) f]
    [(VNeu n n-t)
      (VNeu
        (NFirst n)
        (lazy
          (match-let
            ([(VClos env (BindT 'Sigma x _)) (whnf (force n-t))])
            (eval/expr env (TypedBind-type x)))))]
    [(VChoice n v)
      (VChoice (lazy (do-first (force n))) (lazy (do-first (force v))))]))

(: do-second (-> Value Value))
(define (do-second c)
  (match c
    [(VCons _ s) s]
    [(VNeu n n-t)
      (VNeu
        (NSecond n)
        (lazy
          (match-let
            ([(VClos env (BindT 'Sigma (TypedBind x _) b)) (whnf (force n-t))])
            (eval/expr (env-set env x (do-first c)) b))))]
    [(VChoice n v)
      (VChoice (lazy (do-second (force n))) (lazy (do-second (force v))))]))

;; Quoting

(: quote/value (-> Value TypedExpr))
(define (quote/value v)
  (match v
    [(VChoice n _) (quote/value (force n))]
    [(VNeu n _) (quote/neutral n)]
    [(VClos env (Lam (TypedBind x x-t) b))
      (define x^ (gensym x))
      (define x-t-v (eval/expr env x-t))
      (Lam (TypedBind x^ (quote/value x-t-v))
        (quote/value (eval/expr (env-set env x (VNeu (NVar x^) (lazy x-t-v))) b)))]
    [(VClos env (BindT kind (TypedBind x x-t) b))
      (define x^ (gensym x))
      (define x-t-v (eval/expr env x-t))
      (BindT kind (TypedBind x^ (quote/value x-t-v))
        (quote/value (eval/expr (env-set env x (VNeu (NVar x^) (lazy x-t-v))) b)))]
    [(VType y x) (Type y (quote/value x))]
    [(VLevelT y) (LevelT y)]
    [(VLZero) (LZero)]
    [(VLSucc l) (LSucc (quote/value l))]
    [(VEmptyT) (EmptyT)]
    [(VUnitT) (UnitT)]
    [(VUnit) (Unit)]
    [(VEqT t l r) (EqT (quote/value t) (quote/value l) (quote/value r))]
    [(VRefl) (Refl)]
    [(VW t d) (W (quote/value t) (quote/value d))]
    [(VBoolT) (BoolT)]
    [(VBool v) (Bool v)]
    [(VCons f s) (Cons (quote/value f) (quote/value s))]))

(: quote/neutral (-> Neutral TypedExpr))
(define (quote/neutral n)
  (match n
    [(NVar x) (Var x)]
    [(NApp f a) (App (quote/neutral f) (quote/value a))]
    [(NIndEmpty l n m)
      (IndEmpty (quote/value l) (quote/neutral n) (quote/value m))]
    [(NLMaxL n r) (LMax (quote/neutral n) (quote/value r))]
    [(NLMaxR l n) (LMax (quote/value l) (quote/neutral n))]
    [(NIndEq l n m refl)
      (IndEq (quote/value l) (quote/neutral n) (quote/value m)
        (quote/value refl))]
    [(NIndW l n m e)
      (IndW (quote/value l) (quote/neutral n) (quote/value m)
        (quote/value e))]
    [(NIndBool l n m true false)
      (IndBool (quote/value l) (quote/neutral n) (quote/value m)
        (quote/value true) (quote/value false))]
    [(NFirst e) (First (quote/neutral e))]
    [(NSecond e) (Second (quote/neutral e))]))

(: quote/value/norm (-> Value TypedExpr))
(define (quote/value/norm v)
  (match v
    [(VChoice _ v) (quote/value/norm (force v))]
    [(VNeu n _) (quote/neutral/norm n)]
    [(VClos env (Lam (TypedBind x x-t) b))
      (define x^ (gensym x))
      (define x-t-v (eval/expr env x-t))
      (Lam (TypedBind x^ (quote/value/norm x-t-v))
        (quote/value/norm (eval/expr (env-set env x (VNeu (NVar x^) (lazy x-t-v))) b)))]
    [(VClos env (BindT kind (TypedBind x x-t) b))
      (define x^ (gensym x))
      (define x-t-v (eval/expr env x-t))
      (BindT kind (TypedBind x^ (quote/value/norm x-t-v))
        (quote/value/norm (eval/expr (env-set env x (VNeu (NVar x^) (lazy x-t-v))) b)))]
    [(VType y x) (Type y (quote/value/norm x))]
    [(VLevelT y) (LevelT y)]
    [(VLZero) (LZero)]
    [(VLSucc l) (LSucc (quote/value/norm l))]
    [(VEmptyT) (EmptyT)]
    [(VUnitT) (UnitT)]
    [(VUnit) (Unit)]
    [(VEqT t l r) (EqT (quote/value/norm t) (quote/value/norm l) (quote/value/norm r))]
    [(VRefl) (Refl)]
    [(VW t d) (W (quote/value/norm t) (quote/value/norm d))]
    [(VBoolT) (BoolT)]
    [(VBool v) (Bool v)]
    [(VCons f s) (Cons (quote/value/norm f) (quote/value/norm s))]))

(: quote/neutral/norm (-> Neutral TypedExpr))
(define (quote/neutral/norm n)
  (match n
    [(NVar x) (Var x)]
    [(NApp f a) (App (quote/neutral/norm f) (quote/value/norm a))]
    [(NIndEmpty l n m)
      (IndEmpty (quote/value/norm l) (quote/neutral/norm n) (quote/value/norm m))]
    [(NLMaxL n r) (LMax (quote/neutral/norm n) (quote/value/norm r))]
    [(NLMaxR l n) (LMax (quote/value/norm l) (quote/neutral/norm n))]
    [(NIndEq l n m refl)
      (IndEq (quote/value/norm l) (quote/neutral/norm n) (quote/value/norm m)
        (quote/value/norm refl))]
    [(NIndW l n m e)
      (IndW (quote/value/norm l) (quote/neutral/norm n) (quote/value/norm m)
        (quote/value/norm e))]
    [(NIndBool l n m true false)
      (IndBool (quote/value/norm l) (quote/neutral/norm n) (quote/value/norm m)
        (quote/value/norm true) (quote/value/norm false))]
    [(NFirst e) (First (quote/neutral/norm e))]
    [(NSecond e) (Second (quote/neutral/norm e))]))

;; Equality

(: value=? (-> Value Value Boolean))
(define (value=? a b)
  (match (cons a b)
    [(cons (VChoice n-a v-a) (VChoice n-b v-b))
      (or
        ;; TODO: This causes an issue where one of the terms is actually only
        ;; well typed if we know it's value. For example, the stored type of a
        ;; neutral which should be a function won't actually reduce to a Pi
        ;; since we forget about its value. This causes some of the do-*
        ;; operations to error because they expect the type of the target to be
        ;; correct but it isn't, e.g. do-app expects the type to reduce to a Pi,
        ;; but because we're in the neutral branch it doesn't, even though it
        ;; would if we didn't forget the actual value of the neutral.
        ;; The solution is to acknowledge that values also exist in an
        ;; environment and pass that environment around, then modify whnf to
        ;; also try and reduce neutrals by looking up the variable in the
        ;; environment. Then all gensymed neutrals should be added to the
        ;; environment such that they evaluate to themselves (e.g. when doing
        ;; eta equality on functions). Although this may cause issues because
        ;; in whnf we may want to iteratively lookup neutrals, but if the
        ;; neutral evaluates to itself this would cause a loop. An alternative
        ;; would be to be able to distinguish between neutrals which we actually
        ;; know the value of (e.g. top level variables), and neutrals which we
        ;; actually don't know (e.g. function parameters). Finally, this check
        ;; is actually important since it prevents a lot of useless computation
        ;; from happening during type checking (e.g. a-million = a-million would
        ;; actually have to compute a-million without the check, instead of just
        ;; realizing that a variable is equal to iself).
        ; (value=? (force n-a) (force n-b))
        (value=? (force v-a) (force v-b)))]
    [(cons (VChoice _ a) b) (value=? (force a) b)]
    [(cons a (VChoice _ b)) (value=? a (force b))]
    [(cons (VNeu a t) (VNeu b _))
      (or
        (neutral=? a b)
        (irrelevant? (force t)))]
    [(cons (VClos env (Lam (TypedBind _ x-t) _)) _)
      (define x (VNeu (NVar (gensym)) (lazy (eval/expr env x-t))))
      (value=? (do-app a x) (do-app b x))]
    [(cons _ (VClos env (Lam (TypedBind _ x-t) _)))
      (define x (VNeu (NVar (gensym)) (lazy (eval/expr env x-t))))
      (value=? (do-app a x) (do-app b x))]
    [(cons
      (VClos env-a (BindT k-a (TypedBind x-a t-a) b-a))
      (VClos env-b (BindT k-b (TypedBind x-b t-b) b-b)))
      (and
        (symbol=? k-a k-b)
        (let
          ([t (eval/expr env-a t-a)])
          (and
            (value=? t (eval/expr env-b t-b))
            (let*
              ([x (VNeu (NVar (gensym)) (lazy t))]
               [env-a^ (env-set env-a x-a x)]
               [env-b^ (env-set env-b x-b x)])
              (value=? (eval/expr env-a^ b-a) (eval/expr env-b^ b-b))))))]
    [(cons (VType y-a x-a) (VType y-b x-b))
      (and (= y-a y-b) (value=? x-a x-b))]
    [(cons (VLevelT y-a) (VLevelT y-b)) (= y-a y-b)]
    [(cons (VLZero) (VLZero)) #t]
    [(cons (VLSucc l-a) (VLSucc l-b)) (value=? l-a l-b)]
    [(cons (VEmptyT) (VEmptyT)) #t]
    [(cons (VUnitT) (VUnitT)) #t]
    [(cons (VUnit) _) #t]
    [(cons _ (VUnit)) #t]
    [(cons (VEqT _ l-a r-a) (VEqT _ l-b r-b))
      (and (value=? l-a l-b) (value=? r-a r-b))]
    [(cons (VRefl) (VRefl)) #t]
    [(cons (VW t-a d-a) (VW t-b d-b))
      (and (value=? t-a t-b) (value=? d-a d-b))]
    [(cons (VBoolT) (VBoolT)) #t]
    [(cons (VBool v-a) (VBool v-b)) (boolean=? v-a v-b)]
    [(or (cons (VCons _ _) _) (cons _ (VCons _ _)))
      (and
        (value=? (do-first a) (do-first b))
        (value=? (do-second a) (do-second b)))]
    [(cons a b) (display!= #f a b)]))

(: display!= (-> Boolean Value Value Boolean))
(define (display!= p a b)
  (unless p
    (displayln (unparse/expr (quote/value a)))
    (displayln '!=)
    (displayln (unparse/expr (quote/value b))))
  p)

(: display!=-neu (-> Boolean Neutral Neutral Boolean))
(define (display!=-neu p a b)
  (unless p
    (displayln (unparse/expr (quote/neutral a)))
    (displayln '!=)
    (displayln (unparse/expr (quote/neutral b))))
  p)

(: neutral=? (-> Neutral Neutral Boolean))
(define (neutral=? a b)
  (match (cons a b)
    [(cons (NVar x-a) (NVar x-b)) (display!=-neu (symbol=? x-a x-b) a b)]
    [(cons (NApp f-a a-a) (NApp f-b a-b))
      (and (neutral=? f-a f-b) (value=? a-a a-b))]
    [(cons (NIndEmpty _ t-a _) (NIndEmpty _ t-b _)) (neutral=? t-a t-b)]
    [(cons (NLMaxL l-a r-a) (NLMaxL l-b r-b))
      (and (neutral=? l-a l-b) (value=? r-a r-b))]
    [(cons (NLMaxR l-a r-a) (NLMaxR l-b r-b))
      (and (value=? l-a l-b) (neutral=? r-a r-b))]
    [(cons (NIndEq _ t-a _ refl-a) (NIndEq _ t-b _ refl-b))
      (and (neutral=? t-a t-b) (value=? refl-a refl-b))]
    [(cons (NIndW _ t-a _ e-a) (NIndW _ t-b _ e-b))
      (and (neutral=? t-a t-b) (value=? e-a e-b))]
    [(cons (NIndBool _ t-a _ true-a false-a) (NIndBool _ t-b _ true-b false-b))
      (and
        (neutral=? t-a t-b)
        (value=? true-a true-b)
        (value=? false-a false-b))]
    [(cons (NFirst e-a) (NFirst e-b)) (neutral=? e-a e-b)]
    [(cons (NSecond e-a) (NSecond e-b)) (neutral=? e-a e-b)]
    [(cons a b) (display!=-neu #f a b)]))

(: irrelevant? (-> Value Boolean))
(define (irrelevant? v)
  (match (whnf v)
    [(VUnitT) #t]
    [(VClos env (BindT 'Pi (TypedBind x t) b))
      (irrelevant?
        (eval/expr
          (env-set env x (VNeu (NVar (gensym)) (lazy (eval/expr env t))))
          b))]
    [_ #f]))

;; Type Checking

(: synth/expr (-> TEnv VEnv AstExpr (values TypedExpr Value)))
(define (synth/expr tenv venv e)
  (match e
    [(Var x) #:when (in-env? tenv x)
      (match-let*-values
        ([((cons x^ x-t)) (env-get tenv x)])
        (values (Var x^) x-t))]
    [(Var x) (error 'synth/expr "Undefined variable: ~a" x)]
    [(Ann e t)
      (let*-values
        ([(t^ t-y t-x) (synth/expr-type tenv venv t)]
         [(t-v) (eval/expr venv t^)])
        (values (Ann (check/expr tenv venv e t-v) t^) t-v))]
    [(Lam x b)
      (let*-values
        ([(x-n x-t x-t-y x-t-x) (synth/bind tenv venv x)]
         [(x-t-v) (eval/expr venv x-t)]
         [(x-n^) (gensym x-n)]
         [(tenv-b)
           (env-set* tenv
             (list x-n x-n^)
             (list (cons x-n^ x-t-v) (cons x-n^ x-t-v)))]
         [(venv-b)
           (env-set* venv
             (list x-n x-n^)
             (list (VNeu (NVar x-n^) (lazy x-t-v)) (VNeu (NVar x-n^) (lazy x-t-v))))]
         [(b^ b-t) (synth/expr tenv-b venv-b b)])
        ;; TODO: The quote here really pains me, and I'm not sure it's correct
        ;; Update: I think it should be alright since it's not actually mixing
        ;;   any environments, but should think about it more to be sure
        (values (Lam (TypedBind x-n^ x-t) b^)
          (VClos venv
            (BindT 'Pi (TypedBind x-n^ x-t) (quote/value b-t)))))]
    [(App f a)
      (match-let*-values
        ([(f^ (app whnf (VClos venv-b (BindT 'Pi (TypedBind x x-t) b))))
          (synth/expr-bind 'Pi tenv venv f)]
         [(x-t-v) (eval/expr venv-b x-t)]
         [(a^) (check/expr tenv venv a x-t-v)]
         [(a-v) (eval/expr venv a^)])
        (values (App f^ a^) (eval/expr (env-set venv-b x a-v) b)))]
    [(BindT k x b)
      (match-let*-values
        ([(x-n x-t x-t-y x-t-x) (synth/bind tenv venv x)]
         [(x-t-v) (eval/expr venv x-t)]
         [(x-n^) (gensym x-n)]
         [(tenv-b)
           (env-set* tenv
             (list x-n x-n^)
             (list (cons x-n^ x-t-v) (cons x-n^ x-t-v)))]
         [(x-v) (VNeu (NVar x-n^) (lazy x-t-v))]
         [(venv-b) 
           (env-set* venv
             (list x-n x-n^)
             (list x-v x-v))]
         [(b^ b-y b-x) (synth/expr-type tenv-b venv-b b)])
        (values (BindT k (TypedBind x-n^ x-t) b^) (tmax x-t-y b-y x-t-x b-x)))]
    [(Type y x)
      (match-let*-values
        ([(x^) (check/expr tenv venv x (VLevelT y))])
        (values (Type y x^) (VType y (VLSucc (eval/expr venv x^)))))]
    [(LevelT y) (values e (VType (add1 y) (VLZero)))]
    [(LZero) (values e (VLevelT 0))]
    [(LSucc l)
      (match-let*-values
        ([(l^ l-t) (synth/expr tenv venv l)])
        (values (LSucc l^) l-t))]
    [(LMax l r)
      (match-let*-values
        ([(l^ l-t) (synth/expr tenv venv l)]
         [(r^) (check/expr tenv venv r l-t)])
        (values (LMax l^ r^) l-t))]
    [(EmptyT) (values e (VType 0 (VLZero)))]
    [(IndEmpty l t m)
      (match-let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^) (check/expr tenv venv t (VEmptyT))]
         [(m^) (check/expr tenv venv m (VType l-y (eval/expr venv l^)))])
        (values (IndEmpty l^ t^ m^) (eval/expr venv m^)))]
    [(UnitT) (values e (VType 0 (VLZero)))]
    [(Unit) (values e (VUnitT))]
    [(EqT t from to)
      (match-let*-values
        ([(t^ t-y t-x) (synth/expr-type tenv venv t)]
         [(t-v) (eval/expr venv t^)]
         [(from^) (check/expr tenv venv from t-v)]
         [(to^) (check/expr tenv venv to t-v)])
        (values (EqT t^ from^ to^) (VType t-y t-x)))]
    [(IndEq l t m refl)
      (match-let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^ (app whnf (VEqT t-t t-l t-r))) (synth/expr-eq tenv venv t)]
         [(t-t-n) (gensym 't-t)]
         [(t-l-n) (gensym 't-l)]
         [(m-r-n) (gensym 'm-r)]
         [(m-prf-n) (gensym 'm-prf)]
         [(m^)
           (check/expr tenv venv m
             (VClos (env-set* venv (list t-t-n t-l-n) (list t-t t-l))
               (BindT 'Pi (TypedBind m-r-n (Var t-t-n))
                 (BindT 'Pi
                   (TypedBind m-prf-n (EqT (Var t-t-n) (Var t-l-n) (Var m-r-n)))
                   (Type l-y l^)))))]
         [(m-v) (eval/expr venv m^)]
         [(refl^) (check/expr tenv venv refl (do-app (do-app m-v t-l) (VRefl)))]
         [(t-v) (eval/expr venv t^)])
        (values (IndEq l^ t^ m^ refl^) (do-app (do-app m-v t-r) t-v)))]
    [(IndW l t m e)
      (match-let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^ (and w-t (app whnf (VClos env-a (BindT 'W (TypedBind x x-t) a)))))
           (synth/expr-bind 'W tenv venv t)]
         [(w-t-n) (gensym 'w-t)]
         [(m^)
           (check/expr tenv venv m
             (VClos (env-set venv w-t-n w-t)
               (BindT 'Pi (TypedBind (gensym '_) (Var w-t-n))
                 (Type l-y l^))))]
         [(tag-n) (gensym 'tag)]
         [(tag-t) (eval/expr env-a x-t)]
         [(tag-t-n) (gensym 'tag-t)]
         [(arity-t) (eval/expr (env-set env-a x (VNeu (NVar tag-n) (lazy tag-t))) a)]
         [(arity-t-n) (gensym 'n)]
         [(data-n) (gensym 'data)]
         [(w-t-n) (gensym 'w-t)]
         [(ih-n) (gensym 'ih)]
         [(ih-t-n) (gensym 'ih-t)]
         [(m-v) (eval/expr venv m^)]
         [(m-n) (gensym 'm)]
         [(e^)
           (check/expr tenv venv e
             (VClos
               (env-set* env-a
                 (list tag-t-n arity-t-n w-t-n m-n)
                 (list tag-t arity-t w-t m-v))
               (BindT 'Pi (TypedBind x x-t)
                 (BindT 'Pi
                   (TypedBind data-n
                     (BindT 'Pi (TypedBind (gensym '_) a)
                       (Var w-t-n)))
                   (BindT 'Pi
                     (TypedBind ih-n
                       (BindT 'Pi (TypedBind ih-t-n a)
                         (App (Var m-n) (App (Var data-n) (Var ih-t-n)))))
                     (App (Var m-n) (W (Var x) (Var data-n))))))))]
         [(t-v) (eval/expr venv t^)])
        (values (IndW l^ t^ m^ e^) (do-app m-v t-v)))]
    [(BoolT) (values e (VType 0 (VLZero)))]
    [(Bool _) (values e (VBoolT))]
    [(IndBool l t m true false)
      (match-let*-values
        ([(l^ l-y) (synth/expr-level tenv venv l)]
         [(t^) (check/expr tenv venv t (VBoolT))]
         [(m^)
           (check/expr tenv venv m
             (VClos venv
               (BindT 'Pi (TypedBind (gensym '_) (BoolT)) (Type l-y l^))))]
         [(m-v) (eval/expr venv m^)]
         [(true^) (check/expr tenv venv true (do-app m-v (VBool #t)))]
         [(false^) (check/expr tenv venv false (do-app m-v (VBool #f)))]
         [(t-v) (eval/expr venv t^)])
        (values (IndBool l^ t^ m^ true^ false^) (do-app m-v t-v)))]
    [(First e)
      (match-let*-values
        ([(e^ (app whnf (VClos env-e (BindT 'Sigma (TypedBind _ f-t) _))))
           (synth/expr-bind 'Sigma tenv venv e)]
         [(f-t-v) (eval/expr env-e f-t)])
        (values (First e^) f-t-v))]
    [(Second e)
      (match-let*-values
        ([(e^ (app whnf (VClos env-e (BindT 'Sigma (TypedBind f-n _) s))))
           (synth/expr-bind 'Sigma tenv venv e)]
         [(e-v) (eval/expr venv e^)]
         [(s-t) (eval/expr (env-set env-e f-n (do-first e-v)) s)])
        (values (Second e^) s-t))]
    [(TODO)
      (error 'synth/expr
        (string-join
          (append
            (list "")
            (ann
              (for/list ([(x p) tenv] #:when (symbol-interned? x))
                (format "~a : ~a" x (unparse/expr (quote/value (cdr p)))))
              (Listof String))
            (list "--------------------" "?"))
          "\n"))]))

(: synth/bind (-> TEnv VEnv AstBind (values Symbol TypedExpr Natural Value)))
(define (synth/bind tenv venv b)
  (match b
    [(TypedBind x type)
      (match-let*-values
        ([(type^ type-y type-x) (synth/expr-type tenv venv type)])
        (values
          x
          type^
          type-y
          type-x))]
    [(UntypedBind _)
      (error 'synth/bind "Cannot infer type for bind: ~a" (unparse/bind b))]))

(: synth/expr-type (-> TEnv VEnv AstExpr (values TypedExpr Natural Value)))
(define (synth/expr-type tenv venv e)
  (match-let*-values
    ([(e^ e-t) (synth/expr tenv venv e)])
    (match (whnf e-t)
      [(VType y x) (values e^ y x)]
      [else
        (error 'synth/expr-type "Expected ~a to be a type, but is a ~a"
          (unparse/expr e)
          (unparse/expr (quote/value e-t)))])))

(: synth/expr-bind (-> BindKind TEnv VEnv AstExpr (values TypedExpr Value)))
(define (synth/expr-bind k tenv venv e)
  (match-let*-values
    ([(e^ e-t) (synth/expr tenv venv e)])
    (match (whnf e-t)
      [(VClos _ (BindT k^ _ _)) #:when (symbol=? k k^)
        (values e^ e-t)]
      [else
        (error 'synth/expr-bind "Expected ~a to be a ~a type, but is a ~a"
          (unparse/expr e)
          k
          (unparse/expr (quote/value e-t)))])))

(: synth/expr-level (-> TEnv VEnv AstExpr (values TypedExpr Natural)))
(define (synth/expr-level tenv venv e)
  (match-let*-values
    ([(e^ e-t) (synth/expr tenv venv e)])
    (match (whnf e-t)
      [(VLevelT y) (values e^ y)]
      [else
        (error 'synth/expr-level
          "Expected ~a to be a universe level, but is a ~a"
          (unparse/expr e)
          (unparse/expr (quote/value e-t)))])))

(: synth/expr-eq (-> TEnv VEnv AstExpr (values TypedExpr Value)))
(define (synth/expr-eq tenv venv e)
  (match-let*-values
    ([(e^ e-t) (synth/expr tenv venv e)])
    (match (whnf e-t)
      [(VEqT _ _ _) (values e^ e-t)]
      [else
        (error 'synth/expr-eq "Expected ~a to be an equality type, but is a ~a"
          (unparse/expr e)
          (unparse/expr (quote/value e-t)))])))

(: check/expr (-> TEnv VEnv AstExpr Value TypedExpr))
(define (check/expr tenv venv e e-t)
  (match (cons e (whnf e-t))
    [(cons (Lam x b) (VClos venv-t (BindT 'Pi (TypedBind x-t-n x-t-t) b-t)))
      (match-let*-values
        ([(x-t-t-v) (eval/expr venv-t x-t-t)]
         [(x-n) (check/bind tenv venv x x-t-t-v)]
         [(x-n^) (gensym x-n)]
         [(tenv-b)
           (env-set* tenv
             (list x-n x-n^)
             (list (cons x-n^ x-t-t-v) (cons x-n^ x-t-t-v)))]
         [(x-v) (VNeu (NVar x-n^) (lazy x-t-t-v))]
         [(venv-b)
           (env-set* venv
             (list x-n x-n^)
             (list x-v x-v))]
         [(b-t-v)
           (eval/expr
             (env-set venv-t x-t-n (VNeu (NVar x-n^) (lazy x-t-t-v)))
             b-t)]
         [(b^) (check/expr tenv-b venv-b b b-t-v)])
        ;; TODO: This quote doesn't make a lot of sense
        (Lam (TypedBind x-n^ (quote/value x-t-t-v)) b^))]
    [(cons (Lam _ _) _) (check-mismatch e e-t)]
    [(cons (LevelT y) (VType y-t x-t)) #:when (= (add1 y) y-t) (LevelT y)]
    [(cons (LevelT _) _) (check-mismatch e e-t)]
    [(cons (LZero) (VLevelT _)) (LZero)]
    [(cons (LZero) _) (check-mismatch e e-t)]
    [(cons (LSucc l) (VLevelT y)) (LSucc (check/expr tenv venv l (VLevelT y)))]
    [(cons (LSucc _) _) (check-mismatch e e-t)]
    [(cons (LMax l r) (VLevelT y))
      (LMax
        (check/expr tenv venv l (VLevelT y))
        (check/expr tenv venv r (VLevelT y)))]
    [(cons (LMax _ _) _) (check-mismatch e e-t)]
    [(cons (EmptyT) (VType _ _)) (EmptyT)]
    [(cons (EmptyT) _) (check-mismatch e e-t)]
    [(cons (UnitT) (VType _ _)) (UnitT)]
    [(cons (UnitT) _) (check-mismatch e e-t)]
    [(cons (Refl) (VEqT _ l r)) #:when (value=? l r) (Refl)]
    [(cons (Refl) (VEqT t l r))
      (error 'check/expr "Expected ~a and ~a to be the same ~a"
        (unparse/expr (quote/value l))
        (unparse/expr (quote/value r))
        (unparse/expr (quote/value t)))]
    [(cons (Refl) _) (check-mismatch e e-t)]
    [(cons
      (W tag data)
      (and w-t-v (VClos venv-t (BindT 'W (TypedBind x-t-n x-t-t) a-t))))
      (match-let*-values
        ([(x-t-t-v) (eval/expr venv-t x-t-t)]
         [(tag^) (check/expr tenv venv tag x-t-t-v)]
         [(tag-v) (eval/expr venv tag^)]
         [(a-t-v) (eval/expr (env-set venv-t x-t-n tag-v) a-t)]
         [(a-t-n) (gensym 'a-t)]
         [(w-t-n) (gensym 'w-t)]
         [(data^)
           (check/expr tenv venv data
             (VClos (env-set* (ann (empty-env) VEnv) (list a-t-n w-t-n) (list a-t-v w-t-v))
               (BindT 'Pi (TypedBind (gensym '_) (Var a-t-n))
                 (Var w-t-n))))])
        (W tag^ data^))]
    [(cons (W _ _) _) (check-mismatch e e-t)]
    [(cons (BoolT) (VType _ _)) (BoolT)]
    [(cons (BoolT) _) (check-mismatch e e-t)]
    [(cons (Cons f s) (VClos venv-t (BindT 'Sigma (TypedBind x-t-n x-t-t) s-t)))
      (match-let*-values
        ([(x-t-t-v) (eval/expr venv-t x-t-t)]
         [(f^) (check/expr tenv venv f x-t-t-v)]
         [(f-v) (eval/expr venv f^)]
         [(s-t-v) (eval/expr (env-set venv-t x-t-n f-v) s-t)]
         [(s^) (check/expr tenv venv s s-t-v)])
        (Cons f^ s^))]
    [(cons (Cons _ _) _) (check-mismatch e e-t)]
    [(cons (TODO) _)
      (error 'check/expr
        (string-join
          (append
            (list "")
            (ann
              (for/list ([(x p) tenv] #:when (symbol-interned? x))
                (format "~a : ~a" x (unparse/expr (quote/value (cdr p)))))
              (Listof String))
            (list
              "--------------------"
              (format "? : ~a~n" (unparse/expr (quote/value e-t)))))
          "\n"))]
    [else
      (match-let*-values
        ([(e^ e-t^) (synth/expr tenv venv e)])
        (unless (value=? e-t^ e-t)
          (error 'check/expr "Expected ~a to be of type ~a, but is of type ~a"
            (unparse/expr e)
            (unparse/expr (quote/value e-t))
            (unparse/expr (quote/value e-t^))))
        e^)]))

(: check-mismatch (-> AstExpr Value TypedExpr))
(define (check-mismatch e t)
  (error 'check-mismatch "Expected ~a to be of type ~a"
    (unparse/expr e) (unparse/expr (quote/value t))))

(: check/bind (-> TEnv VEnv AstBind Value Symbol))
(define (check/bind tenv venv b b-t)
  (match b
    [(TypedBind x x-t)
      (match-let*-values
        ([(x-t^ x-t-y x-t-x) (synth/expr-type tenv venv x-t)])
        (unless (value=? (eval/expr venv x-t^) b-t)
          (error 'check/bind "Expected binding ~a to be of type ~a"
            (unparse/bind b)
            (unparse/expr (quote/value b-t))))
        x)]
    [(UntypedBind x) x]))

(: check/bind-expr (-> TEnv VEnv AstBind AstExpr (values Symbol TypedExpr TypedExpr Value)))
(define (check/bind-expr tenv venv b e)
  (match b
    [(TypedBind x x-t)
      (match-let*-values
        ([(x-t^ x-t-y x-t-x) (synth/expr-type tenv venv x-t)]
         [(x-t-v) (eval/expr venv x-t^)]
         [(e^) (check/expr tenv venv e x-t-v)])
        (values x e^ x-t^ x-t-v))]
    [(UntypedBind x)
      (match-let*-values
        ([(e^ e-t) (synth/expr tenv venv e)])
        (values x e^ (quote/value e-t) e-t))]))

(: tmax (-> Natural Natural Value Value Value))
(define (tmax y-a y-b x-a x-b)
  (cond
    [(> y-a y-b) (VType y-a x-a)]
    [(< y-a y-b) (VType y-b x-b)]
    [else (VType y-a (do-lmax x-a x-b))]))

(: unparse/app (-> AstExpr (Listof Any)))
(define (unparse/app f)
  (match f
    [(App f a) `(,@(unparse/app f) ,(unparse/expr a))]
    [_ `(,(unparse/expr f))]))

(: unparse/expr (-> AstExpr Any))
(define (unparse/expr e)
  (match e
    [(Var x) x]
    [(Ann v t) `(,(unparse/expr v) : ,(unparse/expr t))]
    [(Lam x b) `(λ ,(unparse/bind x) ,(unparse/expr b))]
    [(App f a) `(,@(unparse/app f) ,(unparse/expr a))]
    [(BindT k x b)
      `(,(unparse/bind-kind k) ,(unparse/bind x) ,(unparse/expr b))]
    [(Type y x) `(Type ,y ,(unparse/expr x))]
    [(LevelT y) `(Level ,y)]
    [(LZero) 'lzero]
    [(LSucc l) `(lsucc ,(unparse/expr l))]
    [(LMax l r) `(lmax ,(unparse/expr l) ,(unparse/expr r))]
    [(EmptyT) 'Empty]
    [(IndEmpty l t m) `(ind-Empty ,@(map unparse/expr (list l t m)))]
    [(UnitT) 'Unit]
    [(Unit) '()]
    [(EqT t l r) `(= ,(unparse/expr t) ,(unparse/expr l) ,(unparse/expr r))]
    [(Refl) 'Refl]
    [(IndEq l t m refl) `(ind-= ,@(map unparse/expr (list l t m refl)))]
    [(W tag data) `(w ,(unparse/expr tag) ,(unparse/expr data))]
    [(IndW l t m e) `(ind-W ,@(map unparse/expr (list l t m e)))]
    [(BoolT) 'Bool]
    [(Bool #t) 'true]
    [(Bool #f) 'false]
    [(IndBool l t m true false)
      `(ind-Bool ,@(map unparse/expr (list l t m true false)))]
    [(Cons f s) `(cons ,(unparse/expr f) ,(unparse/expr s))]
    [(First e) `(first ,(unparse/expr e))]
    [(Second e) `(second ,(unparse/expr e))]
    [(TODO) '?]))


(: unparse/bind (-> AstBind Any))
(define (unparse/bind b)
  (match b
    [(TypedBind x x-t) `(,x : ,(unparse/expr x-t))]
    [(UntypedBind x) x]))

(: unparse/bind-kind (-> BindKind Any))
(define (unparse/bind-kind k)
  (match k
    ['Pi '->]
    ['Sigma 'Σ]
    ['W 'W]))