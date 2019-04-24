{- NOTE: I defined a notion of permutation here in two ways, but as it turns out,
         there is already a similar notion defined in contrib/Control/Isomorphism/Vect,
         so I may just end up using this
-}

module Control.Algebra.Symmetry

import Interfaces.Verified
import Data.Vect

import Distinct

data Permutation : Nat -> Type where
  PermFromVects : (xs,ys : Vect n (Fin n)) -> {prf : Distinct xs} -> {prf1 : Distinct ys} -> Permutation n
  PermFromFunc : (f : Fin n -> Fin n) -> (f' : Fin n -> Fin n) -> {prf : f' (f x) = x} -> {prf1 : f (f' x) = x} -> Permutation n

-- The permutation from [0,1,2,3] -> [3,1,0,2], and proof that this is indeed a permutation
foo : Permutation 4
foo = PermFromVects xs ys {prf = prf} {prf1 = prf1}
  where 
    xs : Vect 4 (Fin 4)
    xs = [0,1,2,3]
    ys : Vect 4 (Fin 4)
    ys = [3,1,0,2]
    prf = getYes (isDistinct xs)
    prf1 = getYes (isDistinct ys)

bar : Permutation 4
bar = PermFromVects xs ys {prf = prf} {prf1 = prf1}
  where 
    xs : Vect 4 (Fin 4)
    xs = [3,2,1,0]
    ys : Vect 4 (Fin 4)
    ys = [2,0,3,1]
    prf = getYes (isDistinct xs)
    prf1 = getYes (isDistinct ys)

-- Apply a permutation to an element in the set being permuted
apPerm : Permutation n -> Fin n -> Fin n
apPerm (PermFromVects xs ys) = \n => index (index n xs) ys
apPerm (PermFromFunc f f') = f

-- Inverse of apPerm
apPermInv : Permutation n -> Fin n -> Fin n
apPermInv (PermFromVects xs ys) {n} = \m => index (index (last - m) ys) xs
apPermInv (PermFromFunc f f') = f'


-- Given a Permutation, the function you get from applying this permutation is surjective 
-- (and hence can be made into another permutation via PermFromFunc)
apPermSurjective : (perm : Permutation n) -> (apPermInv perm (apPerm perm x) = x, apPerm perm (apPermInv perm y) = y)
apPermSurjective perm = ?apPermSurjective_rhs

{-
apPermSurjective (PermFromVects [] []) = NilDistinct
apPermSurjective (PermFromVects (x :: xs) ys) {n = (S len)} with (index x ys)
  apPermSurjective (PermFromVects (x :: xs) ys) {n = (S len)} | FZ = ?whatnow
  apPermSurjective (PermFromVects (x :: xs) ys) {n = (S len)} | (FS y) = ?apPermSurjective_rhs_2
apPermSurjective (PermFromFunc f {prf}) = ?what
-}

{-
Semigroup (Permutation n) where
  f <+> g = PermFromFunc fg {prf = prf}
    where 
      fg : Fin n -> Fin n
      fg = apPerm f . apPerm g
      prf = getYes (isDistinct (map fg range))
      -}
