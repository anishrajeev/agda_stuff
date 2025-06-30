open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data 𝕊 {l} (A : Set l) : ℕ → Set l where
  empty : 𝕊 A 0
  push : {n : ℕ} (x : A) (s : 𝕊 A n) → 𝕊 A (suc n)

pop : ∀ {l} {A : Set l} {n : ℕ} → 𝕊 A (suc n) → (A × 𝕊 A n)
pop (push x s) = (x , s)

peek : ∀ {l} {A : Set l} {n : ℕ} → 𝕊 A (suc n) → A
peek (push x _) = x

v-papidentity : ∀ {l} {A : Set l} {n : ℕ} (x : A) (s : 𝕊 A n) → pop (push x s) ≡ (x , s)
v-papidentity x s = refl

v-peekapidentity : ∀ {l} {A : Set l} {n : ℕ} (x : A) (s : 𝕊 A n) → peek (push x s) ≡ x
v-peekapidentity x s = refl
