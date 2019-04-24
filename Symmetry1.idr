module Symmetry1

import Interfaces.Verified
import Control.Isomorphism
import Control.Isomorphism.Vect
import Data.Fin
import Data.Vect

-- A much simpler representation of a permutation, which builds on preexisting machinery
Permutation : Nat -> Type
Permutation n = Iso (Fin n) (Fin n)

-- This proof is nowhere near done. I probably need to learn more to complete it
VerifiedSemigroup (Permutation n) where
  semigroupOpIsAssociative l c r with (l <+> (c <+> r))
    semigroupOpIsAssociative l c r | (MkIso to from toFrom fromTo) with ((l <+> c) <+> r)
      semigroupOpIsAssociative (MkIso tol froml toFroml fromTol) (MkIso toc fromc toFromc fromToc) (MkIso tor fromr toFromr fromTor) | (MkIso to from toFrom fromTo) | (MkIso f g x y) = ?what_1
    
