module Foo where

import qualified Prelude

data Nat =
   O
 | S Nat

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

mult :: Nat -> Nat -> Nat
mult n m =
  case n of {
   O -> O;
   S p -> plus m (mult p m)}

foo :: Nat -> Nat -> Nat
foo x y =
  plus (mult x x) y

