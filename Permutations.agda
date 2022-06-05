open import Data.Nat using (ℕ; _≟_; zero; suc; _*_; _+_; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties using (+-comm; +-assoc; +-suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; _∷_;[]; [_]; map; _++_; foldr; concatMap; concat; foldl; length)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (sym; subst) renaming (trans to transeq)
open import Relation.Nullary using (¬_; _because_)
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.Empty using (⊥-elim)
open import Function using (const)
open import Induction.Nat
open import Induction.WellFounded

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
