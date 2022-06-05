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
  
map-prop : (x : A) (xs : List A) (yss : List (List A)) → xs ∈ yss → x ∷ xs ∈ map (_∷_ x) yss
map-prop x xs (ys ∷ yss) (here px) rewrite px = here refl
map-prop x xs (ys ∷ yss) (there p) = let ih = map-prop x xs yss p in there ih

distr-++ : (x : A) → (ys zs : List A) → ys ++ x ∷ zs ∈ distr x (ys ++ zs)
distr-++ x [] [] = here refl
distr-++ x [] (z ∷ zs) = here refl
distr-++ x (y ∷ ys) zs = 
  let ih = distr-++ x ys zs 
  in let prop = map-prop y (ys ++ x ∷ zs) (distr x (ys ++ zs)) ih
  in there prop

distr-base : (x : A) → (pl : List A) → x ∷ pl ∈ distr x pl
distr-base x [] = here refl
distr-base x (x₁ ∷ pl) = here refl 

concat-lemma1 : {A : Set} → ∀ {xs : List A} {ys} → (zs : List (List (List A))) → xs ∈ ys 
  → xs ∈ concat (ys ∷ zs) 
concat-lemma1 zs (here px) = here px
concat-lemma1 zs (there p) = there (concat-lemma1 zs p)

concat-lemma2 : {A : Set} → ∀ {xs : List A} → (ys : List (List A)) → ∀{zs} 
  → xs ∈ concat zs → xs ∈ concat (ys ∷ zs) 
concat-lemma2 [] p = p
concat-lemma2 (ys ∷ yss) {zs} p = there (concat-lemma2 yss {zs} p)

trans-in-concat : (xs : List A) → (ys : List (List A)) → (zs : List(List (List A)))
  → xs ∈ ys
  → ys ∈ zs
  → xs ∈ concat zs
trans-in-concat xs ys (_ ∷ zs) p1 (here refl) = concat-lemma1 zs p1
trans-in-concat xs ys (z ∷ zs) p1 (there p3) = let ih = trans-in-concat xs ys _ p1 p3 in concat-lemma2 z {zs} ih

in-map : {ys : List A} {zs : List (List A)}
  → (f : List A → List (List A))
  → ys ∈ zs
  → (f ys) ∈ (map f zs)
in-map f (here refl) = here refl
in-map f (there p) = there (in-map f p)

perm-refl : (xs : List A) → xs ∈ perm xs
perm-refl [] = here refl
perm-refl (x ∷ xs) = let ih = perm-refl xs in trans-in-concat (x ∷ xs) _ _ (distr-base x xs) (in-map (distr x) ih)

distr-map : (a : A) → (xs : List A) 
  → distr a xs ∈ map (distr a) (perm xs)
distr-map a xs = in-map (distr a) (perm-refl xs)

skip-base : (a : A) → (xs : List A) → (yss : List (List A)) → xs ∈ yss → a ∷ xs ∈ (concatMap (distr a) yss)
skip-base a _ (ys ∷ yss) (here px) rewrite px = ∈-++⁺ˡ (distr-base a  ys)
skip-base a xs (ys ∷ yss) (there p) = let ih = skip-base a xs yss p in ∈-++⁺ʳ (distr a ys) ih

++-lemma : ∀ {A : Set} {l : List A} {xs ys : List (List A)}
      → l ∈ (xs ++ ys)
      → l ∈ xs ⊎ l ∈ ys
++-lemma {xs = []} i = inj₂ i
++-lemma {xs = xs ∷ xs₁} (here px) = inj₁ (here px)
++-lemma {xs = xs ∷ xs₁} (there i) with ++-lemma i
... | inj₁ a = inj₁ (there a)
... | inj₂ b = inj₂ b

concat-map-lemma : ∀ {A : Set} {l′ : List A} {xs : List (List A)} {f : List A → List (List A)}
      → l′ ∈ concatMap f xs
      → ∃[ l ] (l′ ∈ f l × l ∈ xs)
concat-map-lemma {xs = []} ()
concat-map-lemma {xs = xs ∷ xs₁} {f = f} i with ++-lemma {xs = f xs} i
... | inj₁ x = xs , x , here refl
... | inj₂ y with concat-map-lemma y
... | _ , fst , snd = _ , fst , there snd


map-pres-head-tail : (x y : A) (xs : List A) (ys : List (List A))
  → (x ∷ xs) ∈ map (y ∷_ ) ys
  → (x ≡ y × xs ∈ ys)
map-pres-head-tail x .x xs (.xs ∷ ys₁) (here refl) = refl , here refl
map-pres-head-tail x y xs (ys ∷ yss) (there p) = let ih1 , ih2 = map-pres-head-tail x y xs yss p in ih1 , there ih2

absurd-∈ : {A : Set} → (x : A) → (xs : List (List A)) → ¬ ([] ∈ map (x ∷_) xs)
absurd-∈ x [] = λ ()
absurd-∈ x (xs ∷ xss) (there hip) = absurd-∈ x xss hip

list-in-distr : (xs a : List A) (z : A)
  → xs ∈ distr z a 
  → ∃[ vs ] ∃[ us ] (a ≡ vs ++ us × xs ≡ vs ++ z ∷ us)
list-in-distr .(z ∷ []) [] z (here refl) = [] , [] , refl , refl
list-in-distr .(z ∷ x ∷ a) (x ∷ a) z (here refl) = [] , x ∷ a , refl , refl
list-in-distr [] (x ∷ a) z (there p) = ⊥-elim (absurd-∈ x (distr z a) p)
list-in-distr (x ∷ xs) (a1 ∷ a) z (there p) with map-pres-head-tail x a1 xs (distr z a) p 
... | refl , f2 with list-in-distr xs a z f2 
... | vs , us , refl , refl = x ∷ vs , us , refl , refl

inject-one : (vs us : List A) (xs : List (List A)) (x : A)
  → vs ++ us ∈ xs
  → vs ++ x ∷ us ∈ concatMap (distr x) xs
inject-one vs us (.(vs ++ us) ∷ xss) x (here refl) = 
  let dp = distr-++ x vs us 
  in concat-lemma1 (map (distr x) xss) dp
inject-one vs us (xs ∷ xss) x (there p) = 
  let ih = inject-one vs us xss x p 
  in concat-lemma2 ((distr x) xs) {map (distr x) xss} ih

hd-eq : ∀(xs ys : List A) → (x y : A) → x ∷ ys ≡ y ∷ ys → x ≡ y
hd-eq xs ys x .x refl = refl

tl-eq : ∀(xs ys : List A) → (x y : A) → x ∷ xs ≡ y ∷ ys → xs ≡ ys
tl-eq xs .xs x .x refl = refl

concat-eq-lemma : (vs us os ps : List A) (k : A)
  → vs ++ us ≡ os ++ k ∷ ps
  → ∃[ js ] (vs ≡ os ++ k ∷ js × ps ≡ js ++ us)
  ⊎ ∃[ js ] (os ≡ vs ++ js × us ≡ js ++ k ∷ ps)
concat-eq-lemma [] us [] ps k e = inj₂ ([] , refl , e)
concat-eq-lemma [] us (x ∷ os) ps k e = inj₂ (x ∷ os , refl , e)
concat-eq-lemma (x ∷ vs) us [] .(vs ++ us) .x refl = inj₁ (vs , refl , refl)
concat-eq-lemma (v ∷ vs) us (o ∷ os) ps k e 
  with concat-eq-lemma vs us os ps k (tl-eq (vs ++ us) (os ++ k ∷ ps) v o e) 
... | inj₁ (js , refl , refl) 
  rewrite (++-assoc os (k ∷ js) us) 
    | hd-eq js (os ++ k ∷ js ++ us) v o e 
    = inj₁ (js , refl , refl )
... | inj₂ (js , refl , refl) 
  rewrite (++-assoc vs js (k ∷ ps) )
    | hd-eq js (vs ++ js ++ k ∷ ps) v o e 
    = inj₂ (js , refl ,  refl )

head-tail-in-perm : (xs zs : List A) (z : A)
  → z ∷ zs ∈ perm xs
  → ∃[ us ] ∃[ vs ] (xs ≡ us ++ z ∷ vs × zs ∈ perm (us ++ vs)) 
head-tail-in-perm [] zs z (here ())
head-tail-in-perm [] zs z (there ())
head-tail-in-perm (x ∷ xs) zs z p with concat-map-lemma {_} {_} {perm xs} {distr x} p 
... | a , b , c with list-in-distr (z ∷ zs) a x b 
... | [] , .zs , refl , refl = [] , xs , refl , c 
... | .z ∷ ls , ks , refl , refl with head-tail-in-perm xs (ls ++ ks) z c 
... | ms , ts , refl , p5 with inject-one ls ks (perm (ms ++ ts)) x p5 
... | yo = x ∷ ms , ts , refl , yo

l0 : (xs ys zs vs : List A) → (xs ++ ys) ++ zs ++ vs ≡ xs ++ (ys ++ zs) ++ vs
l0 xs ys zs vs rewrite  ++-assoc xs ys (zs ++ vs) | sym (++-assoc ys zs vs) = refl

l1 : (xs ys zs vs : List A) → xs ++ (ys ++ zs) ++ vs ≡ (xs ++ ys) ++ zs ++ vs
l1 xs ys zs vs rewrite (++-assoc xs ys (zs ++ vs)) | ++-assoc ys zs vs = refl

l2 : (xs ys zs vs : List A) → (xs ++ ys ++ zs) ++ vs ≡ xs ++ ys ++ zs ++ vs
l2 xs ys zs vs rewrite ++-assoc xs (ys ++ zs) vs | ++-assoc ys zs vs = refl

l3 : (xs ys zs vs : List A) → (x : A) → xs ++ x ∷ (ys ++ zs) ++ vs ≡ (xs ++ x ∷ ys) ++ zs ++ vs
l3 xs ys zs vs x rewrite ++-assoc ys zs vs | sym (++-assoc xs (x ∷ ys) (zs ++ vs)) = refl

take-out-perm : (vs us ts ps : List A) (x : A)
  → vs ++ us ∈ perm (ts ++ x ∷ ps)
  →   (∃[ zs ] ∃[ js ] (vs ≡ zs ++ x ∷ js × zs ++ js ++ us ∈ perm (ts ++ ps)))
    ⊎ (∃[ zs ] ∃[ js ] (us ≡ zs ++ x ∷ js × vs ++ zs ++ js ∈ perm (ts ++ ps)))
take-out-perm vs us [] ps x p with concat-map-lemma {_} {_} {perm ps} {distr x} p 
... | a , b , c with list-in-distr (vs ++ us) a x b 
... | h , l , refl , i with concat-eq-lemma vs us h l x i 
... | inj₁ (js , refl , refl) = inj₁ (h , js , refl ,  c)
... | inj₂ (js , refl , refl) rewrite ++-assoc vs js l = inj₂ (js , l , refl , c)
take-out-perm vs us (t ∷ ts) ps x p with concat-map-lemma {_} {_} {perm (ts ++ x ∷ ps)} {distr t} p 
... | a , b , c with list-in-distr (vs ++ us) a t b 
... | h , l , refl , i  with concat-eq-lemma vs us h l t i
... | inj₁ (js , r3 , r7) with take-out-perm h l ts ps x c 
... | inj₁ (zs , jsp , refl , ih) 
  rewrite r7 
    | (++-assoc zs (x ∷ jsp) (t ∷ js))
    | sym (++-assoc zs jsp (js ++ us))
  = let daym = inject-one (zs ++ jsp) (js ++ us) (perm (ts ++ ps)) t ih 
  in inj₁ (zs , jsp ++ t ∷ js , r3 , subst (_∈ perm (t ∷ ts ++ ps)) (l0 zs jsp (t ∷ js) us) daym )
take-out-perm vs us (t ∷ ts) ps x p | a , b , c | h , l , refl , i | inj₁ (js , refl , r7) | inj₂ (zs , jsp , refl , ih) 
  rewrite r7 with concat-eq-lemma js us zs jsp x (sym r7) 
... | inj₁ (l1 , refl , refl) 
  = let day = inject-one h (zs ++ l1 ++ us) (perm (ts ++ ps)) t ih
  in inj₁ (h ++ t ∷ zs , l1 , sym (++-assoc h (t ∷ zs) (x ∷ l1)) , subst (_∈ perm (t ∷ ts ++ ps)) (sym (++-assoc h (t ∷ zs) (l1 ++ us))) day)
... | inj₂ (l1 , refl , refl) =
  let day = inject-one h ((js ++ l1) ++ jsp) (perm (ts ++ ps)) t ih 
  in inj₂ (l1 , jsp , refl , subst (_∈ perm (t ∷ ts ++ ps)) (l3 h js l1 jsp t) day)
take-out-perm vs us (t ∷ ts) ps x p | a , b , c | h , l , refl , i | inj₂ (js , refl , r7) rewrite ++-assoc vs js l with take-out-perm vs (js ++ l) ts ps x c 
... | inj₁ (a3 , a4 , refl , ih) rewrite r7 
  with  inject-one (a3 ++ a4 ++ js) l (perm (ts ++ ps)) t (subst (_∈ perm (ts ++ ps)) (sym (l2 a3 a4 js l)) ih)  
... | daym rewrite  (++-assoc a3 (a4 ++ js) (t ∷ l)) | ++-assoc a4 js (t ∷ l) = inj₁ (a3 , a4 , refl , daym)
take-out-perm vs us (t ∷ ts) ps x p | a , b , c | h , l , refl , i | inj₂ (js , refl , r7) | inj₂ (a3 , a4 , r9 , ih) 
  with concat-eq-lemma js l a3 a4 x r9
... | inj₁ (bs , refl , refl) 
  rewrite (++-assoc a3 (x ∷ bs) (t ∷ l)) 
    | sym (++-assoc vs a3 (bs ++ l))
    | sym (++-assoc (vs ++ a3) bs  l)
    | (++-assoc vs a3 bs)
  = let day = inject-one (vs ++ a3 ++ bs) l (perm (ts ++ ps)) t ih 
  in inj₂ (a3 , bs ++ (t ∷ l) , r7 , subst (_∈ perm(t ∷ ts ++ ps)) (l2 vs a3 bs (t ∷ l)) day)
... | inj₂ (bs , refl , refl) 
  rewrite (sym (++-assoc vs (js ++ bs) a4)) 
    | (sym (++-assoc vs js bs)) 
    | ++-assoc (vs ++ js) bs a4 
    | sym (++-assoc js (t ∷ bs)  (x ∷ a4)) 
  = let day = inject-one (vs ++ js) (bs ++ a4) (perm (ts ++ ps)) t ih
  in inj₂ (js ++ t ∷ bs , a4 , r7 , subst (_∈ perm(t ∷ ts ++ ps)) (sym (l1 vs js (t ∷ bs) a4)) day)
    
inject-arbitrary : (vs us ks js : List A)  (x : A)
  → vs ++ us ∈ perm (ks ++ js)
  → vs ++ x ∷ us ∈ perm (ks ++ x ∷ js)
inject-arbitrary vs us [] js x p = inject-one vs us (perm js) x p
inject-arbitrary vs us (k ∷ ks) js x p with concat-map-lemma {_} {_} {perm (ks ++ js)} {distr k} p
... | a , b , c with list-in-distr (vs ++ us) a k b
... | os , ps , refl , r2 with concat-eq-lemma vs us os ps k r2
... | inj₁ (ls , r9 , r16) rewrite r9 | r16 with inject-arbitrary (os ++ ls) us ks js x (subst (_∈ perm (ks ++ js)) (sym (++-assoc os ls us)) c) 
... | ih rewrite ++-assoc os ls (x ∷ us) with inject-one os (ls ++ x ∷ us) (perm (ks ++ x ∷ js)) k ih 
... | yo rewrite sym (++-assoc os (k ∷ ls) (x ∷ us)) = yo
inject-arbitrary vs us (k ∷ ks) js x p | a , b , c | os , ps , refl , r2 | inj₂ (ls , r9 , r16) rewrite r9 | r16 with inject-arbitrary vs (ls ++ ps) ks js x (subst (_∈ perm (ks ++ js)) (++-assoc vs ls ps) c)
... | ih with inject-one (vs ++ x ∷ ls) ps (perm (ks ++ x ∷ js)) k (subst (_∈ perm (ks ++ x ∷ js)) (sym (++-assoc vs (x ∷ ls) ps)) ih)
... | yo rewrite ++-assoc vs (x ∷ ls) (k ∷ ps) = yo

wf-fst : ∀ (xs vs us zs : List A) (x : A) → 
       suc (length (xs ++ (vs ++     us) ++     zs)) 
    ≤′ suc (length (xs ++ (vs ++ x ∷ us) ++ x ∷ zs))
wf-fst xs vs us zs x 
  rewrite length-++ xs {(vs ++ us) ++ zs} 
    | length-++ (vs ++ us) {zs} 
    | length-++ vs {us} 
    | length-++ xs {(vs ++ x ∷ us) ++ x ∷ zs} 
    | length-++ (vs ++ x ∷ us) {x ∷ zs} 
    | length-++ vs {x ∷ us} 
    = from-nats (length xs) (length vs) (length us) (length zs) 
  where
    from-nats : (a b c d : ℕ) →  suc (a + (b + c + d)) ≤′ suc (a + (b + suc c + suc d))
    from-nats a b c d rewrite +-suc b c | +-suc (b + c) d | +-suc a (suc (b + c + d)) | +-suc a (b + c + d)
      = ≤′-step (≤′-step ≤′-refl)

wf-snd : ∀ (ks js us es rs ts ps : List A) (x y z : A) → 
       suc (length ((ks ++     js) ++ (es ++      rs  ++     us) ++     ts ++     ps)) 
    ≤′ suc (length ((ks ++ z ∷ js) ++ ((es ++ x ∷ rs) ++ z ∷ us) ++ z ∷ ts ++ x ∷ ps))
wf-snd ks js us es rs ts ps x y z 
  rewrite length-++ (ks ++ js) {(es ++ rs ++ us) ++ ts ++ ps}
    | length-++ ks {js} 
    | length-++ (es ++ rs ++ us) {ts ++ ps}
    | length-++ es {rs ++ us}
    | length-++ rs {us} | length-++ ts {ps}
    | length-++ (ks ++ z ∷ js) {((es ++ x ∷ rs) ++ z ∷ us) ++ z ∷ ts ++ x ∷ ps}
    | length-++ ks {z ∷ js}
    | length-++ ((es ++ x ∷ rs) ++ z ∷ us) {z ∷ ts ++ x ∷ ps}
    | length-++ (es ++ x ∷ rs) {z ∷ us}
    | length-++ es {x ∷ rs}
    | length-++ ts {x ∷ ps}
  = from-nats (length ks) (length js) (length es) (length rs) (length us) (length ts) (length ps)
  where
    from-nats : (k j e r u t p : ℕ) →  suc (k + j + (e + (r + u) + (t + p))) ≤′ suc (k + suc j + (e + suc r + suc u + suc (t + suc p)))
    from-nats k j e r u t p 
      rewrite +-suc t p | +-suc e r | +-suc (e + r) u | +-suc (e + r + u) (suc (t + p)) | +-suc (e + r + u) (t + p)
        | +-suc k j | +-suc (k + j) (suc (suc (suc (e + r + u + (t + p))))) | +-suc (k + j) (suc (suc (e + r + u + (t + p))))
        | +-suc (k + j) (suc (e + r + u + (t + p)))
        | +-suc (k + j) (e + r + u + (t + p))
        | +-assoc e r u 
      = ≤′-step (≤′-step (≤′-step (≤′-step (≤′-step ≤′-refl))))


wf-trd : ∀ (ks js vs es rs ts ps : List A) (x y z : A) → 
     suc (length ((ks ++     js) ++ (vs ++     es ++     rs) ++     ts ++     ps)) 
  ≤′ suc (length ((ks ++ z ∷ js) ++ (vs ++ z ∷ es ++ x ∷ rs) ++ z ∷ ts ++ x ∷ ps))
wf-trd ks js vs es rs ts ps x y z 
  rewrite length-++ (ks ++ js) {(vs ++ es ++ rs) ++ ts ++ ps}
  | length-++ ks {js}
  | length-++ (vs ++ es ++ rs) {ts ++ ps}
  | length-++ vs {es ++ rs}
  | length-++ es {rs}
  | length-++ ts {ps}
  | length-++ (ks ++ z ∷ js) {(vs ++ z ∷ es ++ x ∷ rs) ++ z ∷ ts ++ x ∷ ps}
  | length-++ ks {z ∷ js}
  | length-++ (vs ++ z ∷ es ++ x ∷ rs) {z ∷ ts ++ x ∷ ps}
  | length-++ vs {z ∷ es ++ x ∷ rs}
  | length-++ (z ∷ es) {x ∷ rs}
  | length-++ ts {x ∷ ps}
  = from-nats (length ks) (length js) (length vs) (length es) (length rs) (length ts) (length ps)
  where 
    from-nats : (k j v e r t p : ℕ) → suc (k + j + (v + (e + r) + (t + p))) ≤′ suc (k + suc j + (v + suc (e + suc r) + suc (t + suc p)))
    from-nats k j v e r t p 
      rewrite +-suc k j | +-suc v (e + suc r) | +-suc e r | +-suc t p  | +-suc v (e + r) | +-suc (v + (e + r)) (suc (t + p))
        | +-suc (v + (e + r)) (t + p) 
        | +-suc (k + j) (suc (suc (suc (v + (e + r) + (t + p)))))
        | +-suc (k + j) (suc (suc (v + (e + r) + (t + p))))
        | +-suc (k + j) (suc (v + (e + r) + (t + p)))
        | +-suc (k + j) (v + (e + r) + (t + p))
      = ≤′-step (≤′-step (≤′-step (≤′-step (≤′-step ≤′-refl))))

swap-perm : (x y : A) → (ls : List A) 
  → y ∷ x ∷ ls ∈ perm (x ∷ y ∷ ls)
swap-perm x y [] = there (here refl)
swap-perm x y (l ∷ ls) = trans-in-concat _ _ _ (distr-++ x (y ∷ []) (l ∷ ls)) (distr-map x (y ∷ l ∷ ls))

skip-perm : (a : A) → (xs ys : List A) 
  → xs ∈ perm ys 
  → a ∷ xs ∈ perm (a ∷ ys)
skip-perm a xs ys p = skip-base a xs (perm ys) p

trans-perm : (xs ys zs : List A)
  → Acc _<′_ (length (xs ++ ys ++ zs))
  → ys ∈ perm zs 
  → zs ∈ perm xs 
  → ys ∈ perm xs
trans-perm xs .[] [] _  (here refl) p2 = p2
trans-perm [] ys (z ∷ zs) _ p1 (here ())
trans-perm [] ys (z ∷ zs) _  p1 (there ())
trans-perm (x ∷ xs) ys (z ∷ zs) (acc go)  p1 p2 with concat-map-lemma {_} {ys} {perm zs} {distr z} p1 | concat-map-lemma {_} {z ∷ zs} {perm xs} {distr x} p2 
... | a , b , c | d , e , f with list-in-distr ys a z b | list-in-distr (z ∷ zs) d x e 
... | vs , us , refl , refl | [] , ps , refl , refl = 
      let ih = trans-perm xs (vs ++ us) zs (go (length (xs ++ (vs ++ us) ++ zs)) (wf-fst xs vs us zs x))  c f 
      in inject-one vs us (perm xs) x ih
... | vs , us , refl , refl | .z ∷ ts , ps , refl , refl  with head-tail-in-perm xs (ts ++ ps) z f 
... | ks , js , r4 , r6 rewrite r4 with take-out-perm vs us ts ps x c 
... | inj₁ (es , rs , refl , p2) =
  let ih = trans-perm (ks ++ js) (es ++ rs ++ us) (ts ++ ps) (go (length ((ks ++ js) ++ (es ++ rs ++ us) ++ ts ++ ps)) (wf-snd ks js us es rs ts ps x z z)) p2 r6
  in let l1 = inject-arbitrary (es ++ rs) us ks js z (subst (_∈ perm (ks ++ js)) (sym (++-assoc es rs us )) ih) 
  in let dayum = inject-one es (rs ++ z ∷ us) (perm (ks ++ z ∷ js)) x (subst (_∈ perm (ks ++ z ∷ js)) (++-assoc es rs (z ∷ us)) l1 )
  in subst (_∈ (perm (x ∷ ks ++ z ∷ js))) (sym (++-assoc es (x ∷ rs) (z ∷ us))) dayum
... | inj₂ (es , rs , refl , p2) =
  let ih = trans-perm (ks ++ js) (vs ++ es ++ rs) (ts ++ ps) (go (length ((ks ++ js) ++ (vs ++ es ++ rs) ++ ts ++ ps)) (wf-trd ks js vs es rs ts ps x z z))  p2 r6 
  in let l1 = inject-arbitrary vs (es ++ rs) ks js z ih
  in let dayum = inject-one (vs ++ z ∷ es) rs (perm (ks ++ z ∷ js)) x (subst (_∈ perm (ks ++ z ∷ js)) (sym (++-assoc vs (z ∷ es) rs)) l1) 
  in subst (_∈ perm (x ∷ ks ++ z ∷ js)) (++-assoc vs (z ∷ es) (x ∷ rs)) dayum

complete : ∀{xs ys : List A} 
  → Permutation xs ys 
    -----------------
  → ys ∈ perm xs
complete base = here refl
complete (swap x y l) = swap-perm x y l
complete (skip {_} {l} {l'} x p) = skip-perm x l' l (complete p)
complete {_} {xs} {ys} (trans {_} {_} {l'} pe1 pe2) = 
  trans-perm xs ys _ (<′-wellFounded (length (xs ++ ys ++ l'))) (complete pe2) (complete pe1)


             