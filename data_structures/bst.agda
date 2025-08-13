open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Level using (Lift; lift)
open import Relation.Binary.Bundles using (TotalOrder)

open import Data.Nat
open import Data.Vec using ([] ; _∷_ ; Vec; _++_; lookup)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

module bst (A : Set) (_≤A_ : A → A → Bool)
                     (trans≤A : ∀ {a b c : A} → a ≤A b ≡ true → b ≤A c ≡ true → a ≤A c ≡ true)
                     (total≤A : ∀{a b : A} → a ≤A b ≡ false → b ≤A a ≡ true)
                     (antisym≤A : ∀{a b : A} → a ≤A b ≡ true → b ≤A a ≡ true → a ≡ b)
                     where

data bst : A → A → Set where
  leaf : ∀ {l u : A} → l ≤A u ≡ true → bst l u
  node : ∀ {l1 l2 u1 u2 : A} → (d : A) → (left : bst l2 d) → (right : bst d u1) → (l1 ≤A l2 ≡ true) → (u1 ≤A u2 ≡ true) → bst l1 u2

lower : ∀ {l l' u : A} → (tree : bst l' u) → (p : l ≤A l' ≡ true) → bst l u
lower (leaf x) p = leaf (trans≤A p x)
lower (node n tree tree₁ x x₁) p = node n tree tree₁ (trans≤A p x) x₁

upper : ∀ {l u' u : A} → (tree : bst l u') → (p : u' ≤A u ≡ true) → bst l u
upper (leaf x) p = leaf (trans≤A x p)
upper (node n tree tree₁ x x₁) p = node n tree tree₁ x (trans≤A x₁ p)

max : A → A → A
max = λ x y → if x ≤A y then y else x

min : A → A → A
min = λ x y → if x ≤A y then x else y

reflexive : ∀ {x : A} → x ≤A x ≡ true
reflexive {x} with x ≤A x | inspect (x ≤A_) x
reflexive {x} | true | _ = refl
reflexive {x} | false | [ eq ] rewrite (sym eq)= total≤A refl

min-consume : ∀ {x y : A} → min x y ≤A x ≡ true
min-consume {x} {y} with x ≤A y | inspect (x ≤A_) y
min-consume {x} {y} | true | _ = reflexive
min-consume {x} {y} | false | [ eq ] =  total≤A eq

max-consume : ∀ {x y : A} → x ≤A max x y ≡ true
max-consume {x} {y} with x ≤A y | inspect (x ≤A_) y
max-consume {x} {y} | true | [ eq ] = eq
max-consume {x} {y} | false | [ eq ] =  reflexive

max-is-greatest : ∀ {x y : A} → x ≤A y ≡ true → max x y ≡ y
max-is-greatest p rewrite p = refl

equal-to-≤A : ∀ {x y : A} → x ≡ y → x ≤A y ≡ true
equal-to-≤A p rewrite p = reflexive

max-trans-≤A : ∀ {x y z : A} → x ≤A y ≡ true → x ≤A max z y ≡ true
max-trans-≤A {x} {y} {z} p with z ≤A y | inspect (z ≤A_) y
max-trans-≤A p | true | [ _ ] = p
max-trans-≤A p | false | [ pp ] = trans≤A p (total≤A pp)

min-preserves-≤A : ∀ {x y z : A} → x ≤A y ≡ true → min z x ≤A min z y ≡ true
min-preserves-≤A {x} {y} {z} p with z ≤A x | inspect (z ≤A_) x
min-preserves-≤A p | true | [ eq ] rewrite (trans≤A eq p)= reflexive
min-preserves-≤A {x} {y} {z} p | false | [ eq ] with z ≤A y
min-preserves-≤A p | false | [ eq ] | true = total≤A eq
min-preserves-≤A p | false | [ eq ] | false = p

min-is-smallest : ∀ {x y : A} → x ≤A y ≡ false → y ≡ min x y
min-is-smallest p rewrite p = sym refl

min-consumes-opp : ∀ {x y z : A} → x ≤A y ≡ true → min z x ≤A y ≡ true
min-consumes-opp {x} {y} {z} p with z ≤A x | inspect (z ≤A_) x
min-consumes-opp {x} {y} {z} p | true | [ eq ] = trans≤A eq p
min-consumes-opp {x} {y} {z} p | false | [ eq ] = p

max-preserves-≤A : ∀ {x y z : A} → x ≤A y ≡ true → max z x ≤A max z y ≡ true
max-preserves-≤A {x} {y} {z} p with z ≤A x | inspect (z ≤A_) x
max-preserves-≤A p | true | [ eq ] rewrite (trans≤A eq p) = p
max-preserves-≤A {x} {y} {z} p | false | [ eq ] with z ≤A y | inspect (z ≤A_) y
max-preserves-≤A p | false | [ _ ] | true | [ eq2 ] = eq2
max-preserves-≤A p | false | [ _ ] | false | [ _ ] = reflexive

insert : ∀ {l u : A} → (d : A) → (tree : bst l u) → bst (min d l) (max d u)
insert d (leaf x) = node d (leaf (min-consume)) (leaf (max-consume)) reflexive reflexive
insert d (node n tree₁ tree₂ x₁ x₂) with d ≤A n | inspect (d ≤A_) n
insert d (node n tree₁ tree₂ x₁ x₂) | true | [ eq ] = node n (upper (insert d tree₁) (equal-to-≤A (max-is-greatest eq)))
                                                             tree₂ (min-preserves-≤A x₁) (max-trans-≤A x₂)
insert d (node n tree₁ tree₂ x₁ x₂) | false | [ eq ] = node n tree₁ (lower (insert d tree₂) (equal-to-≤A (min-is-smallest eq)))
                                                                    (min-consumes-opp x₁) (max-preserves-≤A x₂)


combine : ∀ {x y : Bool} → x ≡ true → y ≡ true → x ∧ y ≡ true
combine p₁ p₂ rewrite p₁ = p₂


search : ∀ {l u : A} → (d : A) → (tree : bst l u) → Maybe (Σ A (λ d' → ((d ≤A d') ∧ (d' ≤A d)) ≡ true))
search d (leaf x) = nothing
search d (node n tree₁ tree₂ x₁ x₂) with d ≤A n | n ≤A d | inspect (d ≤A_) n | inspect (n ≤A_) d
search d (node n tree₁ tree₂ x₁ x₂) | true | true | [ eq₁ ] | [ eq₂ ] = just (n , combine eq₁ eq₂ )
search d (node n tree₁ tree₂ x₁ x₂) | true | false | [ eq₁ ] | [ eq₂ ] = search d tree₁
search d (node n tree₁ tree₂ x₁ x₂) | false | true | [ eq₁ ] | [ eq₂ ] = search d tree₂
search d (node n tree₁ tree₂ x₁ x₂) | false | false | [ eq₁ ] | [ eq₂ ] = nothing

size : ∀ {l u : A} → (tree : bst l u) → ℕ
size (leaf x) = 0
size (node d tree tree₁ x x₁) = suc (size tree + size tree₁)

preorderTraversal : ∀ {l u : A} → (tree : bst l u) → Vec A (size tree)
preorderTraversal (leaf x) = []
preorderTraversal (node d tree tree₁ x x₁) = d ∷ ((preorderTraversal tree) ++ (preorderTraversal tree₁))

lookupA : ∀ {l u : A} → (tree : bst l u) → (x : Fin (size tree)) → A
lookupA tree x = lookup (preorderTraversal tree) x

lookupA-injective : ∀ {l u : A} {tree : bst l u} {x y : Fin (size tree)} → (lookupA tree x) ≡ (lookupA tree y) → x ≡ y
lookupA-injective eq = {!!}

totality-helper : ∀ {x y : A} → (x ≤A y ≡ true) ⊎ (y ≤A x ≡ true)
totality-helper {x} {y} with (x ≤A y) | inspect (x ≤A_) y
totality-helper | true | [ eq ] = inj₁ refl
totality-helper | false | [ eq ] = inj₂ (total≤A eq)

reflexive-helper : ∀ {l u : A} {tree : bst l u} {r s : Fin (size tree)} → r ≡ s → (lookupA tree r) ≡ (lookupA tree s)
reflexive-helper eq rewrite eq = refl

reflexive-helper-2 : ∀ {x y : A} → (eq : x ≡ y) → (x ≤A y) ≡ true
reflexive-helper-2 {x} {y} eq with (x ≤A y) | inspect (x ≤A_) y
reflexive-helper-2 {x} {y} eq | true | [ _ ] = refl
reflexive-helper-2 {x} {y} eq | false | [ q ] rewrite (sym q) | eq = reflexive

μ : ∀ {l u : A} → (tree : bst l u) → TotalOrder lzero lzero lzero
μ {l} {u} tree = record
              { Carrier = Fin (size tree)
              ; _≈_ = _≡_
              ; _≤_ = λ r s → ((lookupA (tree) r) ≤A (lookupA (tree) s)) ≡ true
              ; isTotalOrder = record
                                { isPartialOrder = record
                                                    { isPreorder = record
                                                                    { isEquivalence = isEquivalence
                                                                    ; reflexive = λ {r} {s} r≈s → reflexive-helper-2 (reflexive-helper {l} {u} {tree} {r} {s} r≈s)
                                                                    ; trans = λ {p} {q} {r} p≤q q≤r → trans≤A p≤q q≤r
                                                                    }
                                                    ; antisym = λ x≤y y≤x → lookupA-injective (antisym≤A x≤y y≤x)
                                                    }
                                ; total = λ x y → totality-helper {lookupA tree x} {lookupA tree y}
                                }
              }
