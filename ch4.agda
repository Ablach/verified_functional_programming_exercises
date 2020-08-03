module ch4 where

open import ch2
open import ch3

cong : ∀ {ℓ} {α β : Set ℓ} {a b : α} → (f : α → β) → a ≡ b → f a ≡ f b
cong fun refl = refl

data 𝕃 {ℓ} (α : Set ℓ) : Set ℓ where
  [] : 𝕃 α
  _∷_ : α → 𝕃 α → 𝕃 α

_++_ : ∀ {ℓ} {α : Set ℓ} → 𝕃 α → 𝕃 α → 𝕃 α
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {ℓ} {α : Set ℓ} → 𝕃 α → ℕ
length [] = Z
length (x ∷ xs ) = S (length xs)

takeWhile : ∀ {ℓ} {α : Set ℓ} → (α → 𝔹) → 𝕃 α → 𝕃 α
takeWhile p [] = []
takeWhile p (x ∷ xs) with p x
...                     | t = x ∷ takeWhile p xs
...                     | f = []

repeat : ∀ {ℓ} {α : Set ℓ} → ℕ → α → 𝕃 α
repeat Z     _ = []
repeat (S n) a = a ∷ repeat n a

takeW-Rep-eq : ∀ {ℓ} {α : Set ℓ} {a : α} {p : α → 𝔹} {n : ℕ} →
  p a ≡ t -> takeWhile p (repeat n a) ≡ repeat n a
takeW-Rep-eq {n = Z} h = refl
takeW-Rep-eq {a = a'} {n = S n'} h with takeW-Rep-eq {a = a'} {n = n'} h
...                                                                         | ih rewrite h = cong (λ as → a' ∷ as) ih

take : ∀ {ℓ} {α : Set ℓ} → ℕ → 𝕃 α → 𝕃 α
take Z l = []
take (S n) [] = []
take (S n) (x ∷ xs) = x ∷ take n xs

nᵗʰTail : ∀ {ℓ} {α : Set ℓ} → ℕ → 𝕃 α → 𝕃 α
nᵗʰTail Z l = l
nᵗʰTail (S n) [] = []
nᵗʰTail (S n) (x ∷ l) = nᵗʰTail n l

take++nᵗʰTail : ∀ {ℓ} {α : Set ℓ} →
              (l : 𝕃 α) → (n : ℕ) → (take n l) ++ (nᵗʰTail n l) ≡ l
take++nᵗʰTail l Z = refl
take++nᵗʰTail [] (S n) = refl
take++nᵗʰTail (x ∷ xs) (S n) = cong (λ as → x ∷ as) (take++nᵗʰTail xs n) 
