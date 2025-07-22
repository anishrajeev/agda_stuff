open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _⊔_)

module avl_tree (A : Set) (_≤A_ : A → A → Bool)
                     (trans≤A : ∀ {a b c : A} → a ≤A b ≡ true → b ≤A c ≡ true → a ≤A c ≡ true)
                     (total≤A : ∀{a b : A} → a ≤A b ≡ false → b ≤A a ≡ true) where

eq : ℕ → ℕ → Bool
eq zero zero = true
eq (suc x) (suc y) = eq x y
eq _ _ = false

mutual
   data avl : A → A → Set where
      leaf : ∀ {l u : A} → l ≤A u ≡ true → avl l u
      node : ∀ {l1 u1 l u : A} → (d : A) → (left : avl l1 d) → (right : avl d u1) →
             l ≤A l1 ≡ true → u1 ≤A u ≡ true → differs-by-one (height left) (height right) ≡ true → avl l u

   height : ∀ {l u} → avl l u → ℕ
   height (leaf _) = 0
   height (node _ left right _ _ _) = suc ((height left) ⊔ (height right))

   differs-by-one : ℕ → ℕ → Bool
   differs-by-one x y = (eq x y) ∨ (eq (suc x) y) ∨ (eq x (suc y))



  
