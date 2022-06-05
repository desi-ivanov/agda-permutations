open import Data.Product using (_×_; ∃; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; _∷_;[]; [_]; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Permutations
open import Completeness

private
  variable
    A : Set

map-forces-head : ∀ {A : Set} {x : A} {ys : List A} {xs : List (List A)}
      → ys ∈ map (x ∷_) xs
      → ∃[ l ] (ys ≡ x ∷ l)
map-forces-head {xs = []} ()
map-forces-head {xs = xs ∷ xs₁} (here px) = xs , px
map-forces-head {xs = xs ∷ xs₁} (there x) = map-forces-head x

cons-in-map : ∀ {A : Set} {x : A} {ys : List A} {xs : List (List A)}
      → x ∷ ys ∈ map (x ∷_) xs
      →     ys ∈ xs
cons-in-map {xs = xs ∷ xs₁} (here refl) = here refl
cons-in-map {xs = xs ∷ xs₁} (there x) = there (cons-in-map x)

distribute-perm : ∀ {ys : List A} {a : A} (l : List A)
                → ys ∈ distr a l
                → Permutation (a ∷ l) ys
distribute-perm [] (here refl) = skip _ base
distribute-perm {a = a} (x ∷ xs) (here refl) = trans (swap a x xs) (swap x a xs)
distribute-perm (x ∷ xs) (there t) with map-forces-head t
... | _ , refl with distribute-perm _ (cons-in-map t)
... | r = trans (swap _ x xs) (skip x r)

sound : ∀ l {ys : List A}
      → ys ∈ perm l
      → Permutation l ys
sound [] (here refl) = base
sound (x₁ ∷ l) x with concat-map-lemma x
... | fst , fst₁ , snd = trans (skip x₁ (sound l snd)) (distribute-perm _ fst₁)
