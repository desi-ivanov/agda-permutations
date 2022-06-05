# agda-permutations
Formally verified permutations generation.

## Permutation definition
```agda
data Permutation : List A → List A → Set where
  base : Permutation {A} [] []
  swap : (x y : A) → (l : List A) → Permutation (x ∷ y ∷ l) (y ∷ x ∷ l)
  skip :  ∀{ l l' }  → (x : A) → Permutation l l' → Permutation (x ∷ l) (x ∷ l')
  trans : ∀ {l l' l''} → Permutation {A} l l' → Permutation {A} l' l'' → Permutation {A} l l''  
```

## Permutations generation
```agda
distr : A → List A → List (List A)
distr a [] = (a ∷ []) ∷ []
distr a (x ∷ xs) = (a ∷ x ∷ xs) ∷ map (x ∷_) (distr a xs)

perm : List A → List (List A)
perm [] = [] ∷ []
perm (x ∷ xs) = concatMap (distr x) (perm xs)
```

## Soundness and completeness
Available in [Soundness.agda](Soundness.agda) and [Completeness.agda](Completeness.agda)
```agda
sound : ∀{xs ys : List A} 
  → ys ∈ perm xs
    -----------------
  → Permutation xs ys

complete : ∀{xs ys : List A} 
  → Permutation xs ys 
    -----------------
  → ys ∈ perm xs 
```

## Credits
Co-authored by [@iwilare](https://github.com/iwilare)