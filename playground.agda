open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Level using (Lift; lift)

open import Relation.Binary.Bundles using (TotalOrder)

queue : Set (lsuc lzero)
queue = {A : Set} → ℕ × (ℕ → A)
