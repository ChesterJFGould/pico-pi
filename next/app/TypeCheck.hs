{-# LANGUAGE ApplicativeDo, EmptyDataDeriving, TupleSections, BlockArguments #-}

module TypeCheck (
  typeCheck,
  typeSynth
) where

import AstExpr as A
import TExpr as T

import Data.Bifunctor

typeCheck :: Env -> Counter -> A.Expr -> T.Expr -> Either String (T.Expr, Counter)
typeCheck env c e t = bimap show (\(e, c) -> (T.Check e t, c)) (runTC (typeCheck' e t) env c)

typeSynth :: Env -> Counter -> A.Expr -> Either String ((T.Expr, T.Expr), Counter)
typeSynth env c e = first show (runTC (typeSynth' e) env c)

data TypeError =
    UndefinedVar String
  | ExpectedType A.Expr T.Expr T.Expr -- Expected e to be of type t but is of type t'
  | LamButNotPi A.Expr T.Expr -- Expected e to be of type t but is a lambda
  | LevelButNotLevel A.Expr T.Expr -- Expected e to of type t but is a level literal
  | CannotSynth A.Expr
  deriving Show

data Env = Env {getEnv :: [(String, (T.Var, T.Expr))]}

data Counter = Counter {getCount :: Integer}

data Value =
    Var T.Var
  | LZero
  | LSucc Value
  | LMax Value Value

incCount :: Counter -> Counter
incCount = Counter . (+ 1) . getCount

envLookup :: String -> Env -> Maybe (T.Var, T.Expr)
envLookup s = lookup s . getEnv

envAdd :: String -> T.Var -> T.Expr -> Env -> Env
envAdd s v t = Env . ((s, (v, t)) :) . getEnv

data TC a = TC {runTC :: Env -> Counter -> Either TypeError (a, Counter)}

instance Functor TC where
  fmap f tc = TC (\env n -> fmap (first f) (runTC tc env n))

instance Applicative TC where
  pure a = TC (\_ n -> (pure (a, n)))
  fTC <*> aTC =
    TC (\env n -> do
      (f, n') <- runTC fTC env n
      (a, n'') <- runTC aTC env n'
      pure (f a, n''))

instance Monad TC where
  a >>= f =
    TC \env n -> do
      (a', n') <- runTC a env n
      runTC (f a') env n'

gensym :: String -> TC T.Var
gensym s = TC (\env n -> pure (T.Var s (getCount n), incCount n))

inCtxt :: String -> T.Var -> T.Expr -> TC a -> TC a
inCtxt s v t tca = TC (\env -> runTC tca (envAdd s v t env))

fromCtxt :: String -> TC (T.Var, T.Expr)
fromCtxt s = TC (\env n -> maybe (Left (UndefinedVar s)) (pure . (,n)) (envLookup s env))

raise :: TypeError -> TC a
raise e = TC (\_ _ -> Left e)

-- Expression, expected type, and actual type
expectSameType :: A.Expr -> T.Expr -> T.Expr -> TC ()
expectSameType e t t' | t == t' = pure ()
expectSameType e t t' = raise (ExpectedType e t t')

typeCheck' :: A.Expr -> T.Expr -> TC T.Check
typeCheck' (A.Lam x b) (T.Pi x' dom codom) = do
  b' <- inCtxt x x' dom (typeCheck' b codom)
  pure (T.Lam x' b')
typeCheck' (A.Lam x b) t = raise (LamButNotPi (A.Lam x b) t)
typeCheck' (A.LZero) (T.Level y) = pure T.LZero
typeCheck' (A.LZero) t = raise (LevelButNotLevel A.LZero t)
typeCheck' (A.LSucc l) (T.Level y) = do
  l' <- typeCheck' l (T.Level y)
  pure (T.LSucc l')
typeCheck' (A.LMax l r) (T.Level y) = do
  l' <- typeCheck' l (T.Level y)
  r' <- typeCheck' r (T.Level y)
  pure (T.LMax l' r')
typeCheck' (A.LSucc l) t = raise (LevelButNotLevel (A.LSucc l) t)
typeCheck' e t = do
  (e', t') <- typeSynth' e
  expectSameType e t t'
  pure (T.Synth e')

typeSynth' :: A.Expr -> TC (T.Synth, T.Expr)
typeSynth' (A.Var x) = do
  (x', t) <- fromCtxt x
  pure (T.VarE x', t)
typeSynth' (A.App f a) = do
  (f', x, dom, codom) <- typeSynthPi f
  a' <- typeCheck' a dom
  pure (T.App f' a', subst x (T.Check a' dom) codom)
typeSynth' (A.Pi x dom codom) = do
  (dom', domy, domx) <- typeSynthType dom
  x' <- gensym x
  (codom', codomy, codomx) <- inCtxt x x' dom' (typeSynthType codom)
  pure (T.Pi x' dom' codom', tMax domy codomy domx codomx)
typeSynth' (A.BetaEq x b a) = do
  (a', dom) <- typeSynth' a
  x' <- gensym x
  (b', codom) <- inCtxt x x' dom (typeSynth' b)
  pure
    (T.BetaEq x' b' a'
    , (T.Eq (subst x' a' codom) (T.Synth (T.App (T.Check (T.Lam x' (T.Synth b')) (T.Pi x' dom codom)) (T.Synth a'))) (T.Synth (subst x' a' b')))
    )
typeSynth' (A.Eq t a b) = do
  (t', ty, tx) <- typeSynthType t
  a' <- typeCheck' a t'
  b' <- typeCheck' b t'
  pure (T.Eq t' a' b', T.Type ty tx)
typeSynth' (A.Level y) = pure (T.Level y, T.Type (y + 1) T.LZero)
typeSynth' (A.Type y x) = do
  x' <- typeCheck' x (T.Level y)
  pure (T.Type y x', T.Type y (T.LSucc x'))
typeSynth' (A.Ann e t) = do
  (t', _, _) <- typeSynthType t
  e' <- typeCheck' e t'
  pure (T.Check e' t', t')
typeSynth' e = raise (CannotSynth e)

typeSynthType :: A.Expr -> TC (T.Synth, Integer, T.Check)
typeSynthType = _

typeSynthPi :: A.Expr -> TC (T.Synth, T.Var, T.Synth, T.Synth)
typeSynthPi = _

tMax :: Integer -> Integer -> T.Check -> T.Check -> T.Expr
tMax = _

-- substitute x for e in e'
subst :: T.Var -> T.Expr -> T.Expr -> T.Expr
subst = _
