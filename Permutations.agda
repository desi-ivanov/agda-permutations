open import Data.List using (List; _∷_;[]; [_]; map; concatMap)

private
  variable
    A : Set

data Permutation : List A → List A → Set where
  base : Permutation {A} [] []
  swap : (x y : A) → (l : List A) → Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  skip :  ∀{ l l' }  → (x : A) → Permutation l l' → Permutation (x ∷ l) (x ∷ l')
  trans : ∀ {l l' l''} → Permutation {A} l l' → Permutation {A} l' l'' → Permutation {A} l l''  

distr : A → List A → List (List A)
distr a [] = (a ∷ []) ∷ []
distr a (x ∷ xs) = (a ∷ x ∷ xs) ∷ map (x ∷_) (distr a xs)

perm : List A → List (List A)
perm [] = [] ∷ []
perm (x ∷ xs) = concatMap (distr x) (perm xs)
