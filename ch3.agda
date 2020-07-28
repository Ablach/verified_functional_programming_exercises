module ch3 where

open import ch2

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infixl 10 _×_
infixl 9 _+_
infixl 8 _<_ _≤_ _=ℕ_ _≥_ _>_

_+_ : ℕ → ℕ → ℕ
Z + m = m
S n + m = S (n + m)

_×_ : ℕ → ℕ → ℕ
Z × m = Z
S n × m = (S n) + (n × m)

_=ℕ_ : ℕ → ℕ → 𝔹
Z =ℕ Z = t
S n =ℕ S m = n =ℕ m
_ =ℕ _ = f

=ℕ-sym : ∀ (x y : ℕ) → (x =ℕ y) ≡ (y =ℕ x)
=ℕ-sym Z Z = refl
=ℕ-sym Z (S y) = refl
=ℕ-sym (S x) Z = refl
=ℕ-sym (S x) (S y) = =ℕ-sym x y


_<_ : ℕ → ℕ → 𝔹
Z < S m = t
S n < S m = n < m
_ < Z = f

_≤_ : ℕ → ℕ → 𝔹
Z ≤ Z = t
S n ≤ S m = n ≤ m
_ ≤ _ = f

_≥_ : ℕ → ℕ → 𝔹
Z ≥ S m = f
S n ≥ S m = n ≥ m
_ ≥ Z = t

_>_ : ℕ → ℕ → 𝔹
S n > Z = t
S n > S m = n > m
Z > _ = f

>-trans : ∀ {x y z : ℕ} → x > y ≡ t → y > z ≡ t → x > z ≡ t
>-trans {S x} {S y} {S z} h h' = >-trans {x} {y} {z} h h'
>-trans {S x} {S y} {Z} h h' = refl

S> : ∀ (x : ℕ) → S x > Z ≡ t
S> Z = refl
S> (S x) = S> x

>+ : ∀ {x y : ℕ} → x =ℕ Z ≡ f → y + x > y ≡ t
>+ {S x} {Z} h = refl
>+ {S x} {S y} h = >+ {S x} {y} h
