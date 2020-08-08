module ch6 where

open import bool
open import bool-thms2
open import eq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import unit
open import list
open import list-thms
open import list-simplifier

data Unit : Set where
  unit : Unit

ℤpos : ℕ → Set
ℤpos 0 = Unit
ℤpos (suc _) = 𝔹

data ℤ : Set where
  mkℤ : (n : ℕ) → ℤpos n → ℤ

diffℤ : ℕ → ℕ → ℤ
diffℤ n m with ℕ-trichotomy n m 
diffℤ n m | inj₁ p with <∸suc{m}{n} p               -- n < m
diffℤ n m | inj₁ p | x , _ = mkℤ (suc x) ff
diffℤ n m | inj₂ (inj₁ p) = mkℤ 0 unit              -- n = m 
diffℤ n m | inj₂ (inj₂ p) with <∸suc{n}{m} p
diffℤ n m | inj₂ (inj₂ p) | x , _ = mkℤ (suc x) tt  -- m < n

_+ℤ_ : ℤ → ℤ → ℤ
mkℤ zero x +ℤ m = m
mkℤ (suc n) x +ℤ mkℤ (suc n₁) x₁ with x xor x₁
... | tt = if x imp x₁ then (diffℤ n₁ n) else (diffℤ n n₁)
... | ff = mkℤ ((suc n) + (suc n₁)) x
n +ℤ mkℤ zero x₁ = n

_−_ : ℤ → ℤ → ℤ
mkℤ zero x − mkℤ zero x₁ = mkℤ zero unit
mkℤ zero x − mkℤ (suc n₁) x₁ with x₁
... | tt = mkℤ (suc n₁) ff
... | ff = mkℤ (suc n₁) tt
n − mkℤ zero x₁ = n
mkℤ (suc zero) x − m = (mkℤ zero unit) − m
mkℤ (suc (suc n)) x − mkℤ (suc (zero)) x₁ =  (mkℤ (suc n) x) − (mkℤ zero unit)
mkℤ (suc (suc n)) x − mkℤ (suc (suc n₁)) x₁ = (mkℤ (suc n) x) − (mkℤ (suc n₁) x₁)

-_ : ℤ → ℤ
- mkℤ zero x = mkℤ zero x
- mkℤ (suc n) x = mkℤ (suc n) (~ x)

_×ℤ_ : ℤ → ℤ → ℤ
mkℤ zero x ×ℤ _ = mkℤ zero unit
mkℤ (suc n) x ×ℤ mkℤ (suc n₁) x₁ = mkℤ ((suc n) * (suc n₁)) (x xor x₁)
_ ×ℤ mkℤ zero x₁ = mkℤ zero unit

+ℤ-comm : ∀ (n m : ℤ) → n +ℤ m ≡ m +ℤ n
+ℤ-comm (mkℤ zero unit) (mkℤ zero unit) = refl
+ℤ-comm (mkℤ zero x) (mkℤ (suc n₁) x₁) = refl
+ℤ-comm (mkℤ (suc n) x) (mkℤ zero x₁) = refl
+ℤ-comm (mkℤ (suc n) tt) (mkℤ (suc n₁) tt)
  rewrite +suc n n₁ rewrite +suc n₁ n rewrite +comm n n₁ = refl
+ℤ-comm (mkℤ (suc n) tt) (mkℤ (suc n₁) ff) = refl
+ℤ-comm (mkℤ (suc n) ff) (mkℤ (suc n₁) tt) = refl
+ℤ-comm (mkℤ (suc n) ff) (mkℤ (suc n₁) ff)
    rewrite +suc n n₁ rewrite +suc n₁ n rewrite +comm n n₁ = refl

samp-t = {A B : Set} {l1 l2 l3 : 𝕃 A} → {f : A → B} →
  𝕃⟦((((l1 ʳ) ++ʳ (l2 ʳ)) ++ʳ ([]ʳ)))⟧ ≡ 𝕃⟦(l1 ʳ) ++ʳ (l2 ʳ)⟧

test : samp-t
test {A} {B} {l1} {l2} rewrite (++[] (l1 ++ l2)) = refl
