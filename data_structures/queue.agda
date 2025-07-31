module queue where

open import Data.List using (List; []; _∷_; reverse)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record queue (A : Set) : Set where
   field
      front : List A
      back : List A

empty : {A : Set} → queue A
empty {A} = record {front = [] ; back = []}

enqueue : {A : Set} → (q : queue A) → (e : A) → queue A
enqueue record { front = front ; back = back } e = record { front = e ∷ front ; back = back }

shuffle-helper : {A : Set} → (front : List A) → (back : List A) → queue A
shuffle-helper [] back = record { front = [] ; back = back }
shuffle-helper (x ∷ front) back = shuffle-helper front (x ∷ back)

shuffle : {A : Set} → (q : queue A) → queue A
shuffle q = shuffle-helper (queue.front q) (queue.back q)

dequeue : {A : Set} → (q : queue A) → queue A
dequeue record { front = [] ; back = [] } = record { front = [] ; back = [] }
dequeue record { front = (x ∷ front) ; back = [] } with shuffle (record { front = x ∷ front ; back = [] })
dequeue record { front = (_ ∷ _) ; back = [] } | record { front = front' ; back = [] } =
   record { front = [] ; back = [] }
dequeue record { front = (_ ∷ _) ; back = [] } | record { front = front' ; back = x ∷ back } =
   record {front = front' ; back = back}
dequeue record { front = front ; back = (x ∷ back) } = record { front = front ; back = back }
