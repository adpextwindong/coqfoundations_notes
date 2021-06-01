module Peano where

import qualified Prelude

data N =
   Z
 | S N

psum :: N -> N -> N
psum x y =
  case x of {
   Z -> y;
   S l -> case y of {
           Z -> x;
           S r -> psum (S (S l)) r}}

