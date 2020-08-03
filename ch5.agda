open import ch2
open import ch3
open import ch4

import Agda.Primitive 

open Agda.Primitive public
  using    (Level ; _⊔_ ; lsuc ; lzero)

data Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  _**_ : (a : A) → (b : B a) → Σ A B
infix 5 _**_

_,_ : ∀ {ℓ ℓ'} (α : Set ℓ) (β : Set ℓ') → Set (ℓ ⊔ ℓ')
α , β = Σ α (λ x → β)
infix 5 _,_

data 𝕍 {ℓ} (α : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 α Z
  _∷_ : ∀ {n} → α → 𝕍 α n → 𝕍  α (S n)
infix 6 _∷_

_by_matrix : ℕ → ℕ → Set
n by m matrix =  𝕍 (𝕍 ℕ m) n

m-zs : (m : ℕ) → 𝕍 ℕ m
m-zs Z = []
m-zs (S n) = Z ∷ m-zs n

zero-matrix : (n : ℕ) → (m : ℕ) → n by m matrix
zero-matrix Z m = []
zero-matrix (S n) m = m-zs m ∷ zero-matrix n m

v-elem : ∀ {n : ℕ} → 𝕍 ℕ ( S n)  → (m : ℕ) → m ≤ (S n) ≡ t → ℕ
v-elem (x ∷ v) Z prf = x
v-elem (x ∷ []) (S Z) prf = x
v-elem (x ∷ (x₁ ∷ v)) (S (S m)) prf = v-elem (x₁ ∷ v) (S m) prf

matrix-elt : ∀ {m n : ℕ} →
  (S n) by (S m) matrix → (row : ℕ) → (col : ℕ) →
  (row ≤ (S n) ≡ t) → (col ≤ (S m) ≡ t) →
  ℕ
matrix-elt (mat ∷ mat₁) Z col prf prf' = v-elem mat col prf'
matrix-elt (mat ∷ []) (S row) col prf prf' = v-elem mat col prf'
matrix-elt (mat ∷ (mat₁ ∷ mat₂)) (S row) col prf prf' = matrix-elt ((mat₁ ∷ mat₂)) row col prf prf'

m-zs-with-e : (m : ℕ) → (e : ℕ) → 𝕍 ℕ m
m-zs-with-e Z e = []
m-zs-with-e (S m) e with (S m =ℕ e)
...                                             | t = e ∷ m-zs m
...                                             | f = Z ∷ m-zs-with-e m e

diagonal-matrix : (n : ℕ)→ (e : ℕ) → e ≤ n ≡ t → n by n matrix
diagonal-matrix n e prf = diagonal-matrix' n n e where
  diagonal-matrix' : (n : ℕ) → (m : ℕ) → (e : ℕ) →  n by m matrix
  diagonal-matrix' Z m e = []
  diagonal-matrix' (S n) m e with (S n =ℕ e)
  ...                                                          | t = m-zs-with-e m e ∷ diagonal-matrix' n m e
  ...                                                          | f = m-zs m ∷ diagonal-matrix' n m e

identity-matrix : (S Z) by (S Z) matrix
identity-matrix = diagonal-matrix (S Z) (S Z) refl

create-empties : ∀ {n : ℕ} → 𝕍 (𝕍 ℕ Z) n
create-empties {Z} = []
create-empties {S m} = [] ∷ create-empties {m}

transpose' : ∀ {m n : ℕ} → 𝕍 ℕ m → m by n matrix → m by (S n) matrix
transpose' [] vs = []
transpose' (x ∷ v) (vs ∷ vs₁) = (x ∷ vs) ∷ transpose' v vs₁ 

transpose : ∀ {n m : ℕ} → n by m matrix → m by n matrix
transpose [] = create-empties
transpose (v ∷ vs) =
  let bavs = transpose vs in
           transpose' v bavs

_∙_ : ∀ {n : ℕ} → 𝕍 ℕ n → 𝕍 ℕ n -> ℕ
_∙_ {.Z} [] [] = Z
_∙_ {.(S _)} (x ∷ a) (x₁ ∷ b) = x × x₁ + a ∙ b
infix 10 _∙_

_∙Row_ : ∀ {m p : ℕ} → 𝕍 ℕ m → p by m matrix → 𝕍 ℕ p
m ∙Row [] = []
m ∙Row (m₂ ∷ m₃) = m ∙ m₂ ∷ m ∙Row m₃
infix 7 _∙Row_

_∙𝕍_ : ∀ {n m p : ℕ} → n by m matrix → m by p matrix → n by p matrix
[] ∙𝕍 m2 = []
(m ∷ m₁) ∙𝕍 m₂ = m ∙Row (transpose m₂) ∷ m₁ ∙𝕍 m₂
infix 7 _∙𝕍_

𝕍-to-𝕃 : ∀ {ℓ} {n : ℕ} {α : Set ℓ} → 𝕍 α n → 𝕃 α
𝕍-to-𝕃 [] = []
𝕍-to-𝕃 (x ∷ v) = x ∷ 𝕍-to-𝕃 v

𝕃-to-𝕍 : ∀ {ℓ} {α : Set ℓ} → (l : 𝕃 α) → Σ ℕ (λ n → 𝕍 α n)
𝕃-to-𝕍 [] = Z ** []
𝕃-to-𝕍 (x ∷ l) with (𝕃-to-𝕍 l)
...                                 | n' ** v = S n' ** x ∷ v

𝕍-to-𝕃-and-back : ∀ {ℓ} {α : Set ℓ} {n : ℕ} →
                                            (v : 𝕍 α n) → 𝕃-to-𝕍 (𝕍-to-𝕃 v) ≡ n ** v
𝕍-to-𝕃-and-back [] = refl
𝕍-to-𝕃-and-back (x ∷ v) with (𝕍-to-𝕃-and-back v)
...                                                       | l rewrite l = refl

𝕍-unzip : ∀ {ℓ} {α β : Set ℓ} {n : ℕ} → (𝕍 (α , β) n) →  (𝕍 α n) , (𝕍 β n)
𝕍-unzip [] = {!!}
𝕍-unzip ((a ** b) ∷ v) = {!!}

{-
/home/scott/Agda/verified_functional_programming_exercises/ch5.agda:109,16-18
The constructor [] does not construct an element of Set _ℓ_192
when checking that the expression [] has type Set _ℓ_192
-}
