open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Product using (_×_ ; Σ)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Level using (Lift; lift)


record Category {ℓ : Level} : Set (lsuc  ℓ) where
  field
    Object : Set ℓ
    Hom : Object → Object → Set ℓ
    _∘_ : ∀ {x y z : Object} → Hom y z → Hom x y → Hom x z
    id : ∀ {x : Object} → Hom x x
    assoc : ∀ {r s t u : Object} {f : Hom r s} {g : Hom s t} {h : Hom t u} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    unit : ∀ {x y : Object} (f : Hom x y) → (id ∘ f ≡ f) × (f ∘ id ≡ f)


record Functor {ℓ₁ ℓ₂ : Level} (C : Category {ℓ₁}) (D : Category {ℓ₂}) : Set (ℓ₁ ⊔ ℓ₂) where     
  open Category C renaming (Object to ObjC; Hom to HomC; id to idC; _∘_ to _∘C_)
  open Category D renaming (Object to ObjD; Hom to HomD; id to idD; _∘_ to _∘D_)
  field
    map₀ : ObjC → ObjD
    map₁ : ∀ {x y : ObjC} → HomC x y → HomD (map₀ x) (map₀ y)
    id : ∀ {x : ObjC} → map₁ (idC {x}) ≡ idD {map₀ x}
    compose : ∀ {x y z : ObjC} (f : HomC x y) (g : HomC y z) → map₁ (g ∘C f) ≡ (map₁ g) ∘D (map₁ f)

id-functor : ∀ {ℓ : Level} {C : Category {ℓ}} → Functor C C
id-functor = record
              { map₀ = λ x → x
              ; map₁ = λ x → x
              ; id = refl
              ; compose = λ f g → refl
              }

compose-functor : ∀ {ℓ : Level} {C D E : Category {ℓ}} → Functor D E → Functor C D → Functor C E
compose-functor G F = record
                       { map₀ = λ c → (Functor.map₀ G ((Functor.map₀ F) c))
                       ; map₁ = λ f → (Functor.map₁ G ((Functor.map₁ F) f))
                       ; id = trans (cong (Functor.map₁ G) (Functor.id F)) (Functor.id G)
                       ; compose = λ f g → trans (cong (Functor.map₁ G) (Functor.compose F f g)) (Functor.compose G (Functor.map₁ F f) (Functor.map₁ F g))
                       }

record NaturalTransformation {ℓ₁ ℓ₂} {C : Category {ℓ₁}} {D : Category {ℓ₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂) where
  open Category C renaming (Object to ObjC; Hom to HomC; id to idC; _∘_ to _∘C_)
  open Category D renaming (Object to ObjD; Hom to HomD; id to idD; _∘_ to _∘D_)
  
  open Functor F renaming (map₀ to F₀; map₁ to F₁; id to idF; compose to composeF)
  open Functor G renaming (map₀ to G₀; map₁ to G₁; id to idG; compose to composeG)
  
  field
    η : ∀ {x : ObjC} → HomD (F₀ x) (G₀ x)
    comm : ∀ {x y : ObjC} {f : HomC x y} → (η {y}) ∘D (F₁ f) ≡ (G₁ f) ∘D (η {x})


record BinaryProduct {ℓ} {ℂ : Category {ℓ}} (C D : Category.Object ℂ) : Set ℓ where
  open Category ℂ renaming (Object to Obj; Hom to Hom; id to id; _∘_ to _∘_)
  field
    C×D : Obj
    π₁ : Hom C×D C
    π₂ : Hom C×D D
    UMP : ∀ {Q : Obj} {q₁ : Hom Q C} {q₂ : Hom Q D} → Σ (Hom Q C×D) (λ u → (π₁ ∘ u ≡ q₁) × (π₂ ∘ u ≡ q₂) × (∀ (u' : Hom Q C×D) → (π₁ ∘ u' ≡ q₁) × (π₂ ∘ u' ≡ q₂) → u' ≡ u))


Cat : Category {lsuc lzero}
Cat = record
  { Object = Category {lzero}
  ; Hom = λ C D → Lift (lsuc lzero) (Functor {lzero} {lzero} C D)
  ; _∘_ = λ {x} {y} {z} (lift G) (lift F) → lift (compose-functor G F)
  ; id = λ {x} → lift (id-functor {lzero} {x})
  ; assoc = {!λ {lift f} {lift g} {lift h} → !}
  ; unit = {!!}
  }

record double-category {ℓ} (ℂ₀ ℂ₁ : Category {ℓ}) : Set ℓ where
  field
    s : Functor ℂ₁ ℂ₀
    t : Functor ℂ₁ ℂ₀
    


  
