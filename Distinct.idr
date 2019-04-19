module Data.Vect.Distinct

import Data.Vect

%access public export
%default total

-- A proof that all elements of a vector are distinct
data Distinct : Vect n a -> Type where
  NilDistinct : Distinct Nil
  ConsDistinct : Not (Elem x xs) -> Distinct xs -> Distinct (x :: xs)

-- Can we show that this vector is distinct?
myVect : Num a => Vect 2 a
myVect = [1,2]

-- If we were to prove every vector distinct manually, we would have to provide
-- a lot of very specific proofs of inequality like this - not ideal
twoNotOne : 1 = 2 -> Void
twoNotOne Refl impossible

-- Manually proving a vector is distinct - not fun
myVectDistinct : Distinct Data.Vect.Distinct.myVect
myVectDistinct = ConsDistinct (neitherHereNorThere twoNotOne noEmptyElem) (ConsDistinct noEmptyElem NilDistinct)

------ Can we somehow automate the process of proving that a specific vector is distinct? ------

-- If the first item in the vector can be found elsewhere in the vector, then it is not distinct
headNotInTail : Elem x xs -> Not (Distinct (x :: xs))
headNotInTail headInTail (ConsDistinct notElem _) = notElem headInTail

-- If the tail of a vector is not distinct, then the whole vector is not distinct
tailDistinct : Not (Distinct xs) -> Not (Distinct (x :: xs))
tailDistinct tailNotDistinct (ConsDistinct _ tailDist) = tailNotDistinct tailDist

-- Decision procedure for Distinct, kind of like isElem
isDistinct : DecEq a => (vect : Vect n a) -> Dec (Distinct vect)
isDistinct [] = Yes NilDistinct
isDistinct (x :: xs) with (isElem x xs)
  isDistinct (x :: xs) | (Yes headInTail) = No (headNotInTail headInTail)
  isDistinct (x :: xs) | (No headDistinct) with (isDistinct xs)
    isDistinct (x :: xs) | (No headDistinct) | (Yes tailDistinct) = Yes (ConsDistinct headDistinct tailDistinct)
    isDistinct (x :: xs) | (No headDistinct) | (No tailNotDistinct) = No (tailDistinct tailNotDistinct)



-- Cool little trick to get the compiler to assert that our proof is valid for some value
-- at compile time
getYes : (res : Dec p) -> case res of { Yes _ => p; No _ => () }
getYes (Yes prf) = prf
getYes (No contra) = ()

private
xs : Vect 4 (Fin 4)
xs = [1,0,2,3]

-- Now, proving a vector is distinct is much easier:
private
distinctVect : Distinct Data.Vect.Distinct.xs
distinctVect = getYes (isDistinct xs)
