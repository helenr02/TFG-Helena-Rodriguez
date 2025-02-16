module Mislitas where

import qualified Prelude

data Lista a =
   Nil
 | Cons a (Lista a)

lista_rect :: a2 -> (a1 -> (Lista a1) -> a2 -> a2) -> (Lista a1) -> a2
lista_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (lista_rect f f0 l0)}

lista_rec :: a2 -> (a1 -> (Lista a1) -> a2 -> a2) -> (Lista a1) -> a2
lista_rec =
  lista_rect

head :: a1 -> (Lista a1) -> a1
head default0 l =
  case l of {
   Nil -> default0;
   Cons x _ -> x}

tail :: (Lista a1) -> Lista a1
tail l =
  case l of {
   Nil -> Nil;
   Cons _ xs -> xs}

concatenar :: (Lista a1) -> (Lista a1) -> Lista a1
concatenar l m =
  case l of {
   Nil -> m;
   Cons x xs -> Cons x (concatenar xs m)}

len :: (Lista a1) -> Int
len l =
  case l of {
   Nil -> 0;
   Cons _ xs -> succ (len xs)}

inversa :: (Lista a1) -> Lista a1
inversa l =
  case l of {
   Nil -> Nil;
   Cons x xs -> concatenar (inversa xs) (Cons x Nil)}

nthOpcional :: Int -> (Lista a1) -> Maybe a1
nthOpcional n l =
  (\\fO fS n -> if n == 0 then fO () else fS (n - 1))
    (\_ -> case l of {
            Nil -> Nothing;
            Cons x _ -> Just x})
    (\n' -> case l of {
             Nil -> Nothing;
             Cons _ xs -> nthOpcional n' xs})
    n

nthOpcional' :: Int -> (Lista a1) -> Maybe a1
nthOpcional' n l =
  case l of {
   Nil -> Nothing;
   Cons x xs ->
    (\\fO fS n -> if n == 0 then fO () else fS (n - 1))
      (\_ -> Just x)
      (\n' -> nthOpcional' n' xs)
      n}

map :: (a1 -> a2) -> (Lista a1) -> Lista a2
map f l =
  case l of {
   Nil -> Nil;
   Cons x xs -> Cons (f x) (map f xs)}

