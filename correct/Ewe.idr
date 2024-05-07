module Ewe

import Data.String

public export
interface Parsable stream tok where
  next : stream -> Maybe (tok, stream)

export
Parsable String Char where
  next s with (strM s)
    next "" | StrNil = Nothing
    next (strCons c s) | StrCons _ _ = Just (c, s)

export
data Parser : (0 stream : Type) -> (0 tok : Type) -> Type -> Type where
  Pur : a -> Parser s t a
  App : Inf (Parser s t (a -> b)) -> Inf (Parser s t a) -> Parser s t b
  The : (t -> Bool) -> Parser s t t
  Alt : Inf (Parser s t a) -> Inf (Parser s t a) -> Parser s t a
  Ann : String -> Inf (Parser s t a) -> Parser s t a
  Err : Parser s t a
  Eof : Parser s t Unit

export
Functor (Parser s t) where
  map f a = App (Pur f) a

export
Applicative (Parser s t) where
  pure = Pur
  f <*> a = App f a

export
Alternative (Parser s t) where
  empty = Err
  a <|> b = Alt a b

export
char : Char -> Parser String Char Char
char c = The (== c)

export total
is : (t -> Bool) -> Parser s t t
is = The

export total
(<*>) : Lazy (Parser s t (a -> b)) -> Lazy (Parser s t a) -> Parser s t b
(<*>) = App

export
infixl 3 <*>

export total
(<$>) : (a -> b) -> Lazy (Parser s t a) -> Parser s t b
f <$> a = App (Pur f) a

export
many : Parser s t a -> Parser s t (List a)
many p = ((::) <$> p <*> many p) <|> pure []

export
some : Parser s t a -> Parser s t (List a)
some p = (::) <$> p <*> many p

export total
eof : Parser s t Unit
eof = Eof

export total
ann : String -> Parser s t a -> Parser s t a
ann s p = Ann s p

export
whitespace : Parser s Char Unit
whitespace = many (is isSpace) *> pure ()

total
parseError : String -> Either String _
parseError s = Left ("Parsing error while parsing " <+> s)

parse : (Parsable stream tok) => String -> stream -> Parser stream tok v -> Either String (v, stream)
parse l s p with (the (Maybe (tok, stream)) (next s))
  parse l t (Pur a) | _ = pure (a, t)
  parse l t (App f a) | _ = do
    (f, t') <- parse l t f
    (a, t'') <- parse l t' a
    pure (f a, t'')
  parse l t (The p) | (Just (hd, tl)) =
    if p hd
    then pure (hd, tl)
    else parseError l
  parse l t (Alt a b) | _ =
    either
      (const (parse l t b))
      Right
      (parse l t a)
  parse l t (Ann l' p) | _ = parse l' t p
  parse l t (Err) | _ = parseError l
  parse l t (Eof) | Nothing = pure ((), t)
  parse l t _ | _ = parseError l

export
runParser : Parsable stream tok => String -> stream -> Parser stream tok v -> Either String v
runParser l t p = do
  (a, _) <- parse l t p
  pure a
