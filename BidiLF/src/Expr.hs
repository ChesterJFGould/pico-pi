{-# LANGUAGE DuplicateRecordFields, OverloadedRecordDot #-}
module Expr where

import GHC.Num
import GHC.Stack
import Data.List qualified
import Data.Function
import Symbol
import Syntax qualified as S
import Typed qualified as T

{-
data Symbol = Symbol String
  deriving Eq

data Expr =
    Var Symbol
  | App Symbol [Binding]

data Binding = Binding [Symbol] Expr | BindingExpr Expr

data Kind =
    Constructor ConsType
  | Destructor DestType
  | Sort SortType
  | Meta MetaType
  | Expr Expr

data Params a = Params [(Symbol, a)]

data ConsType = ConsType (Params MetaType) (Params MetaType) Expr

data DestType = DestType (Params MetaType) (Params Expr) (Params MetaType) Expr

data SortType = SortType (Params MetaType)

data MetaType = MetaType (Params Expr) Expr
-}

data Map k v = Map [(k, v)]

mapEmpty :: Map k v
mapEmpty = Map []

mapInsert :: Eq k => k -> v -> Map k v -> Map k v
mapInsert k v (Map m) = Map ((k, v) : m)

mapLookup :: Eq k => k -> Map k v -> Maybe v
mapLookup k (Map m) = lookup k m

mapRemove :: Eq k => k -> Map k v -> Map k v
mapRemove k (Map m) = Map (Data.List.deleteBy ((==) `on` fst) (k, undefined) (Data.List.nubBy ((==) `on` fst) m))

type Set a = Map a ()

map2List :: Ord k => Map k v -> [(k, v)]
map2List m = let (Map l) = thinMap m in Data.List.sortBy (\(k, _) (k', _) -> compare k k') l

thinMap :: Eq k => Map k v -> Map k v
thinMap (Map l) = thinMap' mapEmpty l
  where
    thinMap' :: Eq k => Map k v -> [(k, v)] -> Map k v
    thinMap' m [] = m
    thinMap' m ((k, v) : l')
      | Nothing <- mapLookup k m = thinMap' (mapInsert k v m) l'
      | otherwise = thinMap' m l'


setEmpty :: Set a
setEmpty = mapEmpty

setInsert :: Eq a => a -> Set a -> Set a
setInsert a s = mapInsert a () s

setContains :: Eq a => a -> Set a -> Bool
setContains a s
  | Just () <- mapLookup a s = True
  | otherwise = False

setRemove :: Eq a => a -> Set a -> Set a
setRemove a s = mapRemove a s

set2List :: Ord a => Set a -> [a]
set2List s = map fst (map2List s)

setDiff :: Ord a => Set a -> Set a -> Set a
setDiff a b = foldr setRemove a (set2List b)

setUnion :: Ord a => Set a -> Set a -> Set a
setUnion a b = foldr setInsert a (set2List b)

setSingleton :: Eq a => a -> Set a
setSingleton x = setInsert x setEmpty

type Env a = Map Symbol a

envEmpty :: Env a
envEmpty = mapEmpty

envInsert :: Symbol -> a -> Env a -> Env a
envInsert = mapInsert

envLookup :: Symbol -> Env a -> Maybe a
envLookup = mapLookup

data VCheck =
    VConsApp Integer [MVal]
  | VSynth VSynth
  deriving Show

data VSynth =
    VDestApp Integer [VSynth] [MVal]
  | VMetaApp Integer [VCheck]
  | VVar Integer
  | VAnn VCheck VSort
  deriving Show

data VSort = VSortApp Integer [MVal]
  deriving Show

data MVal = MVal { arity :: Integer, deMVal :: [VSynth] -> VCheck }

instance Show MVal where
  show (MVal 0 deMVal) = show (deMVal [])
  show (MVal _ _) = "<MVal>"

mValApp :: MVal -> [VSynth] -> VCheck
mValApp mv args = mv.deMVal args

data VCheckPat =
    VConsAppPat Integer [VBindingPat]
  | VSynthPat VSynthPat
  deriving Show

data VSynthPat =
    VDestAppPat Integer [VSynthPat] [VBindingPat]
  | VAnnPat VCheckPat VSortPat
  deriving Show

data VSortPat = VSortAppPat Integer [VBindingPat]
  deriving Show

data VBindingPat =
    VUnifVar Integer
  | VNoArgs VCheckPat
  deriving Show

data Scope t v a = Scope t (v -> (Scope t v a)) | Body a

-- Inclusive bounds
data UnifVarSet = UnifVarSet Integer Integer

inUnifVarSet :: UnifVarSet -> Integer -> Bool
inUnifVarSet (UnifVarSet l h) x = l <= x && x <= h

type UnifSolu = Map Integer MVal

emptyUnifSolu :: UnifSolu
emptyUnifSolu = mapEmpty

unifSoluLookup :: Integer -> UnifSolu -> Maybe MVal
unifSoluLookup = mapLookup

unifSoluInsert :: Integer -> MVal -> UnifSolu -> UnifSolu
unifSoluInsert = mapInsert

-- Unification variable range, argument types
data VConsType = VConsType VSortPat (UnifSolu -> Scope VMetaType MVal ())

data VDestType = VDestType (Scope VSortPat (UnifSolu, VSynth) (UnifSolu -> Scope VMetaType MVal VSort))

data VSortType = VSortType (Scope VMetaType MVal ())

data VMetaType = VMetaType (Scope VSort VCheck VSort)

data VKind =
    VCons VConsType
  | VDest VDestType
  | VSort VSortType
  | VMeta VMetaType
  | VExpr VSort

data TypeError =
    UnboundVariable Symbol
  | BadSortApp Symbol VSortType
  | NotASort Symbol VKind
  | BadSort S.Expr
  | BindingMismatch S.Binding VMetaType
  | CheckMismatch Symbol VSort VSortPat
  | BadConsApp Symbol VConsType
  | TypeMismatch S.Expr VSort VSort
  | BadDestApp Symbol VDestType
  | CantInfer S.Expr
  | BadMetaApp Symbol VMetaType
  | SortNotTerm S.Expr
  | PatMismatch S.Expr VSortPat VSort
  | ExpectedExpression S.Binding
  | AppExpr Symbol VSort
  | InvalidBindingPat [Symbol] T.Check
  | InvalidSynthPat T.Synth
  | PatDuplicateImpls [Symbol]
  | UnusedImpls [Symbol]

instance Show TypeError where
  show (UnboundVariable x) = "Unbound variable: " ++ show x
  show (BadSortApp x _) = "Bad sort app: " ++ show x
  show (NotASort x _) = "Not a sort: " ++ show x
  show (BadSort _) = "Bad sort"
  show (BindingMismatch _ _) = "Binding mismatch"
  show (CheckMismatch x expected actual) = "Check mismatch, expected `" ++ show x ++"` to be of type `" ++ show expected ++ "` but is of type `" ++ show actual ++ "`"
  show (BadConsApp x _) = "Bad constructor app: " ++ show x
  show (TypeMismatch _ _ _) = "Type mismatch"
  show (BadDestApp x _) = "Bad destructor app: " ++ show x
  show (CantInfer _) = "Can't infer type"
  show (BadMetaApp x _) = "Bad meta app: " ++ show x
  show (SortNotTerm _) = "Expected term, received sort"
  show (PatMismatch _ _ _) = "Pattern mismatch"
  show (ExpectedExpression _) = "Expected expression, received binding"
  show (AppExpr x _) = "Applied expression term: " ++ show x
  show (InvalidBindingPat _ _) = "Invalid binding pattern"
  show (InvalidSynthPat _) = "Invalid synth pattern"
  show (PatDuplicateImpls _) = "Duplicate identifiers in implicit parameter list"
  show (UnusedImpls _) = "Unused identifiers in implicit parameter list"

-- Ops are just renamed
-- Metas are instantiated with MVals
-- Variables may need to be renamed (Π(Nat, x. Eq(Nat, x, x)) = Π(Nat, y. Eq(Nat, y, y))), or substituted (f{x : Nat, isZ : Eq(Nat, x, Z)} : Nat ⊢ f{Z, Refl} : Nat)
data ValEnv = ValEnv { op :: Env Integer, meta :: Env MVal, var :: Env VSynth }

valEnvEmpty :: ValEnv
valEnvEmpty = ValEnv mapEmpty mapEmpty mapEmpty

data TCEnv = TCEnv { deBruijn :: Integer, val :: ValEnv, kind :: Env VKind }

tcEnvEmpty :: TCEnv
tcEnvEmpty = TCEnv 0 valEnvEmpty mapEmpty

data Eval a = Eval { deEval :: TCEnv -> a }

runEval :: TCEnv -> Eval a -> a
runEval env e = deEval e env

instance Functor Eval where
  fmap f a = Eval (\env -> f (deEval a env))

instance Applicative Eval where
  pure a = Eval (\_ -> a)
  f <*> a = Eval (\env -> (deEval f env) (deEval a env))

instance Monad Eval where
  a >>= f = Eval (\env -> deEval (f (deEval a env)) env)

evalGetEnv :: HasCallStack => Eval TCEnv
evalGetEnv = Eval (\env -> env)

evalGetOp :: HasCallStack => Symbol -> Eval Integer
evalGetOp x = do
  env <- evalGetEnv
  case envLookup x env.val.op of
    Nothing -> error ("unbound variable: " ++ show x)
    Just i -> pure i

evalGetMVal :: HasCallStack => Symbol -> Eval MVal
evalGetMVal x = do
  env <- evalGetEnv
  case envLookup x env.val.meta of
    Nothing -> error ("unbound variable: " ++ show x)
    Just mv -> pure mv

evalWithMVal :: HasCallStack => Symbol -> MVal -> Eval a -> Eval a
evalWithMVal x mv e = Eval (\env -> deEval e (env {val = env.val {meta = envInsert x mv env.val.meta}}))

evalWithVal :: HasCallStack => Symbol -> VSynth -> Eval a -> Eval a
evalWithVal x v e = Eval (\env -> deEval e (env {val = env.val {var = envInsert x v env.val.var}}))

evalWithSolu :: HasCallStack => T.Params T.MetaType -> UnifSolu -> Eval b -> Eval b
evalWithSolu (T.Params l) solu e = foldr (\((x, t), (_, mv)) e' -> evalMetaType t >>= \tv -> evalWithMVal x mv (evalWithKind x (VMeta tv) e')) e (zip l (map2List solu))

evalGetVal :: HasCallStack => Symbol -> Eval VSynth
evalGetVal x = do
  env <- evalGetEnv
  case envLookup x env.val.var of
    Nothing -> error ("unbound variable: " ++ show x)
    Just v -> pure v

evalGetKind :: HasCallStack => Symbol -> Eval VKind
evalGetKind x = do
  env <- evalGetEnv
  case envLookup x env.kind of
    Nothing -> error ("unbound variable: " ++ show x)
    Just v -> pure v

evalWithKind :: HasCallStack => Symbol -> VKind -> Eval a -> Eval a
evalWithKind x k e = Eval (\env -> deEval e (env {kind = envInsert x k env.kind}))

evalClos :: (a -> Eval b) -> Eval (a -> b)
evalClos f = do
  env <- evalGetEnv
  pure (\a -> runEval env (f a))

evalConsType :: HasCallStack => T.ConsType -> Eval VConsType
evalConsType (T.ConsType impl args codom) =
  VConsType
    <$> evalSortPat (evalImpls impl) codom
    <*> evalClos (\solu -> evalWithSolu impl solu (evalParams args evalMetaType (const VMeta) (\_ -> evalWithMVal) (pure ())))

evalDestType :: HasCallStack => T.DestType -> Eval VDestType
evalDestType (T.DestType impl subjs args codom) =
  VDestType
    <$> evalParams subjs (evalSortPat (evalImpls impl)) (\(solu, _) s -> VExpr (instVSortPat solu s)) (\_ x (_, v) -> evalWithVal x v)
          (evalClos (\solu -> evalWithSolu impl solu (evalParams args evalMetaType (const VMeta) (const evalWithMVal) (evalSort codom))))

instVSortPat :: UnifSolu -> VSortPat -> VSort
instVSortPat = _

evalSortType :: HasCallStack => T.SortType -> Eval VSortType
evalSortType (T.SortType args) = VSortType <$> evalParams args evalMetaType (const VMeta) (const evalWithMVal) (pure ())

evalMetaType :: HasCallStack => T.MetaType -> Eval VMetaType
evalMetaType (T.MetaType args codomain) = VMetaType <$> evalParams args evalSort (const VExpr) (\d x v e -> evalWithVal x (doVAnn v d) e) (evalSort codomain)

evalParams :: HasCallStack => T.Params a -> (a -> Eval b) -> (v -> b -> VKind) -> (forall d. b -> Symbol -> v -> Eval d -> Eval d) -> Eval c -> Eval (Scope b v c)
evalParams (T.Params []) _ _ _ e = Body <$> e
evalParams (T.Params ((x, t) : ps)) ev k wi e = do
  t' <- ev t
  Scope t' <$> evalClos (\v -> evalWithKind x (k v t') (wi t' x v (evalParams (T.Params ps) ev k wi e)))

evalImpls :: HasCallStack => T.Params T.MetaType -> Map Symbol Integer
evalImpls (T.Params p) = foldr (\((x, _), i) m -> mapInsert x i m) mapEmpty (zip p [0..])

evalSortPat :: HasCallStack => Map Symbol Integer -> T.SortPat -> Eval VSortPat
evalSortPat m (T.SortAppPat x args) = do
  x' <- evalGetOp x
  VSortAppPat x' <$> traverse (evalBindingPat m) args

evalBindingPat :: HasCallStack => Map Symbol Integer -> T.BindingPat -> Eval VBindingPat
evalBindingPat m (T.UnifVar x) = maybe (error "Unbound pattern variable") (pure . VUnifVar) (mapLookup x m)
evalBindingPat m (T.NoArgs e) = VNoArgs <$> evalCheckPat m e

evalCheckPat :: HasCallStack => Map Symbol Integer -> T.CheckPat -> Eval VCheckPat
evalCheckPat m (T.ConsAppPat x args) = do
  x' <- evalGetOp x
  VConsAppPat x' <$> traverse (evalBindingPat m) args
evalCheckPat m (T.SynthPat s) = VSynthPat <$> evalSynthPat m s

evalSynthPat :: HasCallStack => Map Symbol Integer -> T.SynthPat -> Eval VSynthPat
evalSynthPat m (T.DestAppPat x subjs args) = do
  x' <- evalGetOp x
  VDestAppPat x' <$> traverse (evalSynthPat m) subjs <*> traverse (evalBindingPat m) args
evalSynthPat m (T.AnnPat c t) = VAnnPat <$> evalCheckPat m c <*> evalSortPat m t

evalCheck :: HasCallStack => T.Check -> Eval VCheck
evalCheck (T.ConsApp x args) = do
  x' <- evalGetOp x
  VConsApp x' <$> traverse evalBinding args
evalCheck (T.Synth s) = doVSynth <$> evalSynth s

evalSynth :: HasCallStack => T.Synth -> Eval VSynth
evalSynth (T.DestApp x subjs args) = do
  x' <- evalGetOp x
  VDestApp x' <$> traverse evalSynth subjs <*> traverse evalBinding args
evalSynth (T.MetaApp x args) = do
  k <- evalGetKind x
  let mt = case k of
             (VMeta t) -> t
             _ -> error "bad meta app"
  mv <- evalGetMVal x
  argVs <- traverse evalCheck args
  (argVs', codomain) <- appMetaType argVs mt
  pure (doVAnn (mValApp mv argVs') codomain)
evalSynth (T.Var x) = evalGetVal x
evalSynth (T.Ann e t) = doVAnn <$> evalCheck e <*> evalSort t

evalSort :: HasCallStack => T.Sort -> Eval VSort
evalSort (T.SortApp x args) = do
  x' <- evalGetOp x
  VSortApp x' <$> traverse evalBinding args

evalBinding :: HasCallStack => T.Binding -> Eval MVal
evalBinding (T.Binding xs body) = do
  env <- evalGetEnv
  pure (MVal (integerFromInt (length xs)) (\vs -> runEval (foldl (\env' (x, v) -> env' {val = env'.val {var = envInsert x v env'.val.var}}) env (zip xs vs)) (evalCheck body)))

appMetaType :: HasCallStack => [VCheck] -> VMetaType -> Eval ([VSynth], VSort)
appMetaType args (VMetaType t) = appMetaType' [] args t

appMetaType' :: HasCallStack => [VSynth] -> [VCheck] -> Scope VSort VCheck VSort -> Eval ([VSynth], VSort)
appMetaType' args' [] (Body codomain) = pure (reverse args', codomain)
appMetaType' args' (arg : args) (Scope d f) = appMetaType' ((doVAnn arg d) : args') args (f arg)
appMetaType' _ _ _ = error "bad meta app"

doVAnn :: VCheck -> VSort -> VSynth
doVAnn (VConsApp x args) t = VAnn (VConsApp x args) t
doVAnn (VSynth s) _ = s

doVSynth :: VSynth -> VCheck
doVSynth (VAnn c _) = c
doVSynth s = VSynth s

data TC a = TC {runTC :: TCEnv -> Either TypeError a}

instance Functor TC where
  fmap f tc = TC (\env -> f <$> runTC tc env)

instance Applicative TC where
  pure a = TC (\_ -> pure a)
  f <*> a = TC (\env -> runTC f env <*> runTC a env)

instance Monad TC where
  a >>= f = TC (\env -> runTC a env >>= (\a' -> runTC (f a') env))

checkTheory :: S.Theory -> Either String T.Theory
checkTheory t = either (Left . show) Right (runTC (theory t) tcEnvEmpty)

tcEval :: Eval a -> TC a
tcEval e = TC (\env -> pure (deEval e env))

typeError :: TypeError -> TC a
typeError e = TC (\_ -> Left e)

tcGetKind :: Symbol -> TC (Maybe VKind)
tcGetKind x = TC (\env -> pure (envLookup x env.kind))

tcWithKind :: Symbol -> VKind -> TC a -> TC a
tcWithKind x x_k body = TC(\env -> runTC body (env{kind = envInsert x x_k env.kind}))

tcWithLevel :: (Integer -> TC a) -> TC a
tcWithLevel f = TC (\env -> runTC (f env.deBruijn) (env {deBruijn = env.deBruijn + 1}))

tcWithVal :: Symbol -> VSynth -> TC a -> TC a
tcWithVal x v e = TC (\env -> runTC e (env {val = env.val {var = envInsert x v env.val.var}}))

tcWithOpVal :: Symbol -> Integer -> TC a -> TC a
tcWithOpVal x v e = TC (\env -> runTC e (env {val = env.val {op = envInsert x v env.val.op}}))

tcWithMVal :: Symbol -> MVal -> TC a -> TC a
tcWithMVal x v e = TC (\env -> runTC e (env {val = env.val {meta = envInsert x v env.val.meta}}))

theory :: S.Theory -> TC T.Theory
theory (S.Theory s) = foldr (\s' t -> stmt s' >>= \s'' -> theoryWithStmt s'' t) (pure (T.Theory [])) s

stmt :: S.Stmt -> TC T.Stmt
stmt (S.Cons x t) = T.Cons x <$> consType t
stmt (S.Dest x t) = T.Dest x <$> destType t
stmt (S.Sort x t) = T.Sort x <$> sortType t
stmt (S.Let x t e) = do
  t' <- sort t
  tv <- tcEval (evalSort t')
  e' <- check e tv
  pure (T.Let x t' e')

consType :: S.ConsType -> TC T.ConsType
consType (S.ConsType impls args codomain) =
  checkParams impls
    ( \impls' -> do
      codomain' <- sortPatWrt impls' codomain
      checkParams args (\args' -> pure (T.ConsType impls' args' codomain'))
    )

destType :: S.DestType -> TC T.DestType
destType (S.DestType impls subjs args codomain) =
  checkParams impls ( \impls' ->
    sortPatsWrt impls' subjs ( \subjs' ->
      checkParams args ( \args' ->
        T.DestType impls' subjs' args' <$> sort codomain
      )
    )
  )

sortType :: S.SortType -> TC T.SortType
sortType (S.SortType args) = checkParams args (\args' -> pure (T.SortType args'))

metaType :: S.MetaType -> TC T.MetaType
metaType (S.MetaType args codomain) = checkSortParams args (\args' -> T.MetaType args' <$> sort codomain)

theoryWithStmt :: T.Stmt -> TC T.Theory -> TC T.Theory
theoryWithStmt (T.Cons x ct) a = do
  ctv <- tcEval (evalConsType ct)
  tcWithKind x (VCons ctv) (tcWithLevel (\l -> tcWithOpVal x l a))
theoryWithStmt (T.Dest x dt) a = do
  dtv <- tcEval (evalDestType dt)
  tcWithKind x (VDest dtv) (tcWithLevel (\l -> tcWithOpVal x l a))
theoryWithStmt (T.Sort x st) a = do
  stv <- tcEval (evalSortType st)
  tcWithKind x (VSort stv) (tcWithLevel (\l -> tcWithOpVal x l a))
theoryWithStmt (T.Let x s _) a = do
  sv <- tcEval (evalSort s)
  tcWithKind x (VExpr sv) (tcWithLevel (\l -> tcWithVal x (VVar l) a))

checkParams :: S.Params S.MetaType -> (T.Params T.MetaType -> TC a) -> TC a
checkParams (S.Params l) f =
  foldr
    (\(x, mt) f' l' -> do
      mt' <- metaType mt
      mv <- tcEval (evalMetaType mt')
      tcWithKind x (VMeta mv)
        (tcWithLevel (\mx ->
          tcWithMVal x (neuMVal mx mt') (f' ((x, mt') : l'))
          )
        )
    )
    (\l' -> f (T.Params (reverse l')))
    l
    []

neuMVal :: Integer -> T.MetaType -> MVal
neuMVal x (T.MetaType (T.Params l) _) = MVal (integerFromInt (length l)) (\vals -> VSynth (VMetaApp x (map doVSynth vals)))

checkSortParams :: S.Params S.Expr -> (T.Params T.Sort -> TC a) -> TC a
checkSortParams (S.Params l) f =
  foldr
    (\(x, s) f' l' -> do
      s' <- sort s
      sv <- tcEval (evalSort s')
      tcWithKind x (VExpr sv)
        (tcWithLevel (\x' ->
          tcWithVal x (VVar x') (f' ((x, s') : l'))
        ))
    )
    (\l' -> f (T.Params (reverse l')))
    l
    []

checkNoDuplicates :: T.Params T.MetaType -> TC ()
checkNoDuplicates (T.Params l)
  | [] <- duplicates [] (Data.List.sort (map fst l)) = pure ()
  | dups <- duplicates [] (Data.List.sort (map fst l)) = typeError (PatDuplicateImpls dups)
  where
    duplicates :: [Symbol] -> [Symbol] -> [Symbol]
    duplicates dups (x : x' : xs)
      | x == x' = duplicates (x : dups) xs
      | otherwise = duplicates dups (x' : xs)
    duplicates dups _ = Data.List.nub dups

-- no duplicate parameters, this first because it will be first when checking dest subj pats
-- expr is a valid sort
-- expr is a valid sort pattern
-- every parameter is used at least once
sortPatWrt :: T.Params T.MetaType -> S.Expr -> TC T.SortPat
sortPatWrt (T.Params l) e = do
  checkNoDuplicates (T.Params l)
  e' <- sort e
  let implSet = foldr setInsert setEmpty (map fst l)
  e'' <- sortPat implSet e'
  case set2List (setDiff implSet (sortPatUVs e'')) of
    [] -> pure e''
    l' -> typeError (UnusedImpls l')

sortPatsWrt :: T.Params T.MetaType -> S.Params S.Expr -> (T.Params T.SortPat -> TC a) -> TC a
sortPatsWrt (T.Params l) args f = do
  checkNoDuplicates (T.Params l)
  checkSortParams args
    (\(T.Params argl) -> do
      let implSet = foldr setInsert setEmpty (map fst l)
      argl' <- traverse (\(x, s) -> sortPat implSet s >>= \s' -> pure (x, s')) argl
      case set2List (setDiff implSet (foldr setUnion setEmpty (map (sortPatUVs . snd) argl'))) of
        [] -> f (T.Params argl')
        l' -> typeError (UnusedImpls l')
    )

sortPat :: Set Symbol -> T.Sort -> TC T.SortPat
sortPat impls (T.SortApp x args) = T.SortAppPat x <$> traverse (bindingPat impls) args

bindingPat :: Set Symbol -> T.Binding -> TC T.BindingPat
bindingPat impls (T.Binding args (T.Synth (T.MetaApp x args')))
  | (True, True) <- (setContains x impls, map (T.Synth . T.Var) args == args') = pure (T.UnifVar x)
  | True <- setContains x impls = typeError (InvalidBindingPat args (T.Synth (T.MetaApp x args')))
bindingPat impls (T.Binding [] e) = T.NoArgs <$> checkPat impls e
bindingPat _ (T.Binding args e) = typeError (InvalidBindingPat args e)

checkPat :: Set Symbol -> T.Check -> TC T.CheckPat
checkPat impls (T.ConsApp x args) = T.ConsAppPat x <$> traverse (bindingPat impls) args
checkPat impls (T.Synth s) = T.SynthPat <$> synthPat impls s

synthPat :: Set Symbol -> T.Synth -> TC T.SynthPat
synthPat impls (T.DestApp x subjs args) = T.DestAppPat x <$> traverse (synthPat impls) subjs <*> traverse (bindingPat impls) args
synthPat impls (T.Ann e t) = T.AnnPat <$> checkPat impls e <*> sortPat impls t
synthPat _ s = typeError (InvalidSynthPat s)

sortPatUVs :: T.SortPat -> Set Symbol
sortPatUVs (T.SortAppPat _ args) = foldr setUnion setEmpty (map bindingPatUVs args)

bindingPatUVs :: T.BindingPat -> Set Symbol
bindingPatUVs (T.UnifVar x) = setSingleton x
bindingPatUVs (T.NoArgs c) = checkPatUVs c

checkPatUVs :: T.CheckPat -> Set Symbol
checkPatUVs (T.ConsAppPat _ args) = foldr setUnion setEmpty (map bindingPatUVs args)
checkPatUVs (T.SynthPat s) = synthPatUVs s

synthPatUVs :: T.SynthPat -> Set Symbol
synthPatUVs (T.DestAppPat _ subjs args) =
  setUnion
    (foldr setUnion setEmpty (map synthPatUVs subjs))
    (foldr setUnion setEmpty (map bindingPatUVs args))
synthPatUVs (T.AnnPat c t) = setUnion (checkPatUVs c) (sortPatUVs t)

sort :: S.Expr -> TC T.Sort
sort (S.Var x) = do
  k <- tcGetKind x
  case k of
    (Just (VSort (VSortType (Body ())))) -> pure (T.SortApp x [])
    (Just (VSort t)) -> typeError (BadSortApp x t)
    (Just k') -> typeError (NotASort x k')
    Nothing -> typeError (UnboundVariable x)
sort (S.App x args) = do
  k <- tcGetKind x
  case k of
    (Just (VSort (VSortType t))) -> do
      (args', ()) <- checkBindings (BadSortApp x (VSortType t)) args t
      pure (T.SortApp x args')
    (Just k') -> typeError (NotASort x k')
    Nothing -> typeError (UnboundVariable x)
sort (S.Ann e t) = typeError (BadSort (S.Ann e t))

checkBindings :: TypeError -> [S.Binding] -> Scope VMetaType MVal a -> TC ([T.Binding], a)
checkBindings err bindings scope = checkBindings' [] bindings scope
  where
    checkBindings' :: [T.Binding] -> [S.Binding] -> Scope VMetaType MVal a -> TC ([T.Binding], a)
    checkBindings' bs' [] (Body a) = pure (reverse bs', a)
    checkBindings' bs' (b : bs) (Scope (VMetaType d) c) = do
      b' <- checkBinding b d
      bv <- tcEval (evalBinding b')
      checkBindings' (b' : bs') bs (c bv)
    checkBindings' _ _ _ = typeError err

checkBinding :: S.Binding -> Scope VSort VCheck VSort -> TC T.Binding
checkBinding (S.Binding params body) scope = checkBinding' [] params scope
  where
    checkBinding' :: [Symbol] -> [Symbol] -> Scope VSort VCheck VSort -> TC T.Binding
    checkBinding' ps' [] (Body codomain) = T.Binding (reverse ps') <$> check body codomain
    checkBinding' ps' (p : ps) (Scope d c) =
      tcWithLevel (\l ->
        tcWithKind p (VExpr d) (
          tcWithVal p (VVar l) (
            checkBinding' (p : ps') ps (c (VSynth (VVar l)))
          )
        )
      )
    checkBinding' _ _ _ = typeError (BindingMismatch (S.Binding params body) (VMetaType scope))
checkBinding (S.BindingExpr e) (Body t) = T.Binding [] <$> check e t
checkBinding b s = typeError (BindingMismatch b (VMetaType s))

check :: S.Expr -> VSort -> TC T.Check
check (S.Var x) s = do
  k <- tcGetKind x
  case k of
    (Just (VCons (VConsType cPat scope))) -> do
      res <- tcRunUnif (unifSort cPat s) emptyUnifSolu
      solu <- case res of
                Just (solu, ()) -> pure solu
                Nothing -> typeError (CheckMismatch x s cPat)
      case scope solu of
        (Body ()) -> pure (T.ConsApp x [])
        _ -> typeError (BadConsApp x (VConsType cPat scope))
    _ -> checkInfer (S.Var x) s
check (S.App x args) s = do
  k <- tcGetKind x
  case k of
    (Just (VCons (VConsType cPat scope))) -> do
      res <- tcRunUnif (unifSort cPat s) emptyUnifSolu
      solu <- case res of
                Just (solu, ()) -> pure solu
                Nothing -> typeError (CheckMismatch x s cPat)
      (args', ()) <- checkBindings (BadConsApp x (VConsType cPat scope)) args (scope solu)
      pure (T.ConsApp x args')
    _ -> checkInfer (S.App x args) s
check e s = checkInfer e s

checkInfer :: S.Expr -> VSort -> TC T.Check
checkInfer e s = do
  (e', s') <- infer e
  isEq <- tcSortEq s s'
  case isEq of
    True -> pure (T.Synth e')
    False -> typeError (TypeMismatch e s s')

tcSortEq :: VSort -> VSort -> TC Bool
tcSortEq a b = TC (\env -> pure (sortEq a b env.deBruijn))

infer :: S.Expr -> TC (T.Synth, VSort)
infer (S.Var x) = do
  k <- tcGetKind x
  case k of
    (Just (VDest (VDestType (Body s)))) ->
      case s emptyUnifSolu of
        (Body t) -> pure (T.DestApp x [] [], t)
        _ -> typeError (BadDestApp x (VDestType (Body s)))
    (Just (VMeta (VMetaType (Body t)))) -> pure (T.MetaApp x [], t)
    (Just (VExpr t)) -> pure (T.Var x, t)
    (Just (VDest t)) -> typeError (BadDestApp x t)
    (Just (VMeta t)) -> typeError (BadMetaApp x t)
    (Just (VCons _)) -> typeError (CantInfer (S.Var x))
    (Just (VSort _)) -> typeError (SortNotTerm (S.Var x))
    Nothing -> typeError (UnboundVariable x)
infer (S.App x args) = do
  k <- tcGetKind x
  case k of
    (Just (VDest (VDestType s))) -> do
      (args', subjs, solu, scp) <- inferArgs (BadDestApp x (VDestType s)) args s emptyUnifSolu
      (args'', codomain) <- checkBindings (BadDestApp x (VDestType s)) args' (scp solu)
      pure (T.DestApp x subjs args'', codomain)
    (Just (VMeta (VMetaType s))) -> do
      (args', codomain) <- checkArgs (BadMetaApp x (VMetaType s)) args s
      pure (T.MetaApp x args', codomain)
    (Just (VExpr t)) -> typeError (AppExpr x t)
    (Just (VCons _)) -> typeError (CantInfer (S.App x args))
    (Just (VSort _)) -> typeError (SortNotTerm (S.App x args))
    Nothing -> typeError (UnboundVariable x)
infer (S.Ann e s) = do
  s' <- sort s
  sV <- tcEval (evalSort s')
  e' <- check e sV
  pure (T.Ann e' s', sV)

inferArgs :: TypeError -> [S.Binding] -> Scope VSortPat (UnifSolu, VSynth) a -> UnifSolu -> TC ([S.Binding], [T.Synth], UnifSolu, a)
inferArgs err arguments scope solution = inferArgs' [] arguments scope solution
  where
    inferArgs' :: [T.Synth] -> [S.Binding] -> Scope VSortPat (UnifSolu, VSynth) a -> UnifSolu -> TC ([S.Binding], [T.Synth], UnifSolu, a)
    inferArgs' args' args (Body a) s = pure (args, reverse args', s, a)
    inferArgs' args' (S.BindingExpr arg : args) (Scope dPat c) s = do
      (arg', argS) <- infer arg
      res <- tcRunUnif (unifSort dPat argS) s
      s' <- case res of
              Just (s', ()) -> pure s'
              Nothing -> typeError (PatMismatch arg dPat argS)
      argV <- tcEval (evalSynth arg')
      inferArgs' (arg' : args') args (c (s', argV)) s'
    inferArgs' _ (arg : _) (Scope _ _) _ = typeError (ExpectedExpression arg)
    inferArgs' _ _ _ _ = typeError err

checkArgs :: TypeError -> [S.Binding] -> Scope VSort VCheck a -> TC ([T.Check], a)
checkArgs err bindings scope = checkArgs' [] bindings scope
  where
    checkArgs' :: [T.Check] -> [S.Binding] -> Scope VSort VCheck a -> TC ([T.Check], a)
    checkArgs' args' [] (Body a) = pure (reverse args', a)
    checkArgs' args' (S.BindingExpr arg : bs) (Scope argS s) = do
      arg' <- check arg argS
      argV <- tcEval (evalCheck arg')
      checkArgs' (arg' : args') bs (s argV)
    checkArgs' _ (b : _) _ = typeError (ExpectedExpression b)
    checkArgs' _ _ _ = typeError err

data UnifEnv = UnifEnv { uDeBruijn :: Integer, solu :: UnifSolu }

data Unif a = Unif { runUnif :: UnifEnv -> Maybe (UnifSolu, a) }

instance Functor Unif where
  fmap f a = Unif (\env -> (fmap f) <$> runUnif a env)

instance Applicative Unif where
  pure a = Unif (\env -> pure (env.solu, a))
  f <*> a = Unif (\env -> (runUnif f env) >>= (\(solu', f') -> fmap f' <$> runUnif a (env {solu = solu'})))

instance Monad Unif where
  a >>= f = Unif (\env -> (runUnif a env) >>= (\(solu', a') -> runUnif (f a') (env {solu = solu'})))

unifFail :: Unif a
unifFail = Unif (\_ -> Nothing)

tcRunUnif :: Unif a -> UnifSolu -> TC (Maybe (UnifSolu, a))
tcRunUnif u s = TC (\env -> pure (runUnif u (UnifEnv env.deBruijn s)))

unifGetMVal :: Integer -> Unif (Maybe MVal)
unifGetMVal x = Unif (\env -> pure (env.solu, unifSoluLookup x env.solu))

unifPutMVal :: Integer -> MVal -> Unif ()
unifPutMVal x mv = Unif (\env -> pure (unifSoluInsert x mv env.solu, ()))

unifMValEq :: MVal -> MVal -> Unif Bool
unifMValEq a b = Unif (\env -> pure (env.solu, metaEq a b env.uDeBruijn))

unifSort :: VSortPat -> VSort -> Unif ()
unifSort (VSortAppPat x args) (VSortApp x' args')
  | x == x' = unifBindings args args'
  | otherwise = unifFail

unifBindings :: HasCallStack => [VBindingPat] -> [MVal] -> Unif ()
unifBindings [] [] = pure ()
unifBindings (b : bs) (mv : mvs) = unifBinding b mv >> unifBindings bs mvs
unifBindings _ _ = error "Unified binding lists of unequal length"

unifBinding :: VBindingPat -> MVal -> Unif ()
unifBinding (VUnifVar x) mv = unifVar x mv
unifBinding (VNoArgs p) mv
  | mv.arity == 0 = unifCheck p (deMVal mv [])
  | otherwise = unifFail

unifVar :: Integer -> MVal -> Unif ()
unifVar x mv = do
  maybeMv' <- unifGetMVal x
  case maybeMv' of
    Just mv'-> do
      eq <- unifMValEq mv mv'
      case eq of
        True -> pure ()
        False -> unifFail
    Nothing -> unifPutMVal x mv

unifCheck :: VCheckPat -> VCheck -> Unif ()
unifCheck (VConsAppPat x args) (VConsApp x' args')
  | x == x' = unifBindings args args'
  | otherwise = unifFail
unifCheck (VSynthPat s) (VSynth s') = unifSynth s s'
unifCheck _ _ = unifFail

unifSynth :: VSynthPat -> VSynth -> Unif ()
unifSynth (VDestAppPat x subjs args) (VDestApp x' subjs' args')
  | x == x' = do
    unifSynths subjs subjs'
    unifBindings args args'
  | otherwise = unifFail
unifSynth (VAnnPat c t) (VAnn c' t') = do
  unifSort t t'
  unifCheck c c'
unifSynth _ _ = unifFail

unifChecks :: HasCallStack => [VCheckPat] -> [VCheck] -> Unif ()
unifChecks [] [] = pure ()
unifChecks (c : cs) (c' : cs') = unifCheck c c' >> unifChecks cs cs'
unifChecks _ _ = unifFail

unifSynths :: HasCallStack => [VSynthPat] -> [VSynth] -> Unif ()
unifSynths [] [] = pure ()
unifSynths (s : ss) (s' : ss') = unifSynth s s' >> unifSynths ss ss'
unifSynths _ _  = error "Unified subject lists of unequal length"

sortEq :: VSort -> VSort -> Integer -> Bool
sortEq (VSortApp x args) (VSortApp x' args') l = x == x' && metasEq args args' l

metasEq :: [MVal] -> [MVal] -> Integer -> Bool
metasEq [] [] _ = True
metasEq (b : bs) (b' : bs') l = metaEq b b' l && metasEq bs bs' l
metasEq _ _ _ = error "Equated binding lists of unequal length"

metaEq :: MVal -> MVal -> Integer -> Bool
metaEq (MVal arity f) (MVal arity' f') l
  | arity == arity' = let args = map VVar [l .. l + arity - 1] in checkEq (f args) (f' args) (l + arity)
  | otherwise = error "Equated mvals of unqual arity"

checkEq :: VCheck -> VCheck -> Integer -> Bool
checkEq (VConsApp x args) (VConsApp x' args') l = x == x' && metasEq args args' l
checkEq (VSynth s) (VSynth s') l = synthEq s s' l
checkEq _ _ _ = False

synthEq :: VSynth -> VSynth -> Integer -> Bool
synthEq (VDestApp x subjs args) (VDestApp x' subjs' args') l = x == x' && synthsEq subjs subjs' l && metasEq args args' l
synthEq (VMetaApp x args) (VMetaApp x' args') l = x == x' && checksEq args args' l
synthEq (VVar x) (VVar x') _ = x == x'
synthEq (VAnn c t) (VAnn c' t') l = sortEq t t' l && checkEq c c' l
synthEq _ _ _ = False

checksEq :: [VCheck] -> [VCheck] -> Integer -> Bool
checksEq [] [] _ = True
checksEq (c : cs) (c' : cs') l = checkEq c c' l && checksEq cs cs' l
checksEq _ _ _ = error "Equated check lists of unequal length"

synthsEq :: [VSynth] -> [VSynth] -> Integer -> Bool
synthsEq [] [] _ = True
synthsEq (c : cs) (c' : cs') l = synthEq c c' l && synthsEq cs cs' l
synthsEq _ _ _ = error "Equated synth lists of unequal length"
