module ch2 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

data 𝔹 : Set where
     t : 𝔹
     f : 𝔹 

_∧_ : 𝔹 → 𝔹 → 𝔹
t ∧ b = b
f ∧ _ = f
infixr 6 _∧_

_∨_ : 𝔹 → 𝔹 → 𝔹
t ∨ _ = t
f ∨ b = b
infixr 5 _∨_

~_ : 𝔹 → 𝔹
~ t = f
~ f = t
infix 7 ~_

∨≡f₂ : ∀ {b₁ b₂} → b₁ ∨ b₂ ≡ f → b₂ ≡ f
∨≡f₂ {f} p = p

~a∧b≡~a∨~b : ∀ {a b} → ~ (a ∧ b) ≡ ~ a ∨ ~ b 
~a∧b≡~a∨~b {t} {t} = refl
~a∧b≡~a∨~b {t} {f} = refl
~a∧b≡~a∨~b {f} {b} = refl

