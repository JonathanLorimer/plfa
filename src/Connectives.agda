module Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open Isomorphism.≃-Reasoning

infixr 2 _×_

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , x₁ ⟩ = refl

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- NOTE: No need to pattern match on the record, that is because identity
-- holds definitionally for records!
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from∘to = λ { ⟨ x , x₁ ⟩ → refl }
    ; to∘from = λ { ⟨ x , x₁ ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to = λ { record { to = to ; from = from } → ⟨ to , from ⟩ }
  ; from = λ { ⟨ x , x₁ ⟩ → record { to = x ; from = x₁ } }
  ; from∘to = λ { x → refl }
  ; to∘from = λ { ⟨ x , x₁ ⟩ → refl }
  }

data ⊤ : Set where
  tt : ⊤

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where

  inj₁ : A → A ⊎ B

  inj₂ : B → A ⊎ B

case-⊎ : ∀ { A B C : Set } → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

swap-⊎ : ∀ { A B : Set } → A ⊎ B → B ⊎ A
swap-⊎ = case-⊎ inj₂ inj₁

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = swap-⊎
    ; from = swap-⊎
    ; from∘to = λ { (inj₁ x) → refl
                  ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ x) → refl
                  ; (inj₂ x) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ { (inj₁ (inj₁ x)) → inj₁ x
             ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
             ; (inj₂ x) → inj₂ (inj₂ x)
             }
    ; from = λ { (inj₁ x) → inj₁ (inj₁ x)
               ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
               ; (inj₂ (inj₂ x)) → inj₂ x }
    ; from∘to = λ { (inj₁ (inj₁ x)) → refl
                  ; (inj₁ (inj₂ x)) → refl
                  ; (inj₂ x) → refl
                  }
    ; to∘from = λ { (inj₁ x) → refl
                  ; (inj₂ (inj₁ x)) → refl
                  ; (inj₂ (inj₂ x)) → refl }
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ x) → x }
    ; from = λ { x → inj₂ x }
    ; from∘to = λ { (inj₂ x) → refl }
    ; to∘from = λ { y → refl }
    }

⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
  (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
  (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
  A
  ≃-∎

→-elim : ∀ {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- Proof that (p ^ n) ^ m ≡ p ^ (n * m)
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- Proof that p ^ (n + m) = (p ^ n) * (p ^ m)
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ { x → ⟨ x ∘ inj₁ , x ∘ inj₂ ⟩ }
    ; from = λ { ⟨ f , g ⟩ x → case-⊎ f g x }
    ; from∘to = λ{ f → extensionality λ { (inj₁ x) → refl
                                        ; (inj₂ x) → refl
                                        }
                 }
    ; to∘from = λ { ⟨ x , x₁ ⟩ → refl }
    }

-- Proof that (p * n) ^ m = (p ^ m) * (n ^ m)
→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , y ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ x , y ⟩ = inj₂ ⟨ x , y ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ x , y ⟩) = ⟨ inj₂ x , inj₂ y ⟩

data Singleton₁ : Set where
  S₁ : Singleton₁

data Singleton₂ : Set where
  S₂ : Singleton₂

data Singleton₃ : Set where
  S₃ : Singleton₃

data Singleton₄ : Set where
  S₄ : Singleton₄

×⊎-implies-⊎×-⊥
  : ( ∀ {A B C D : Set}
    → (A ⊎ B) × (C ⊎ D)
    → (A × C) ⊎ (B × D)
    )
  → ⊥
×⊎-implies-⊎×-⊥ abs with abs {A = ⊤} {B = ⊥} {C = ⊥} {D = ⊤} ⟨ (inj₁ tt), (inj₂ tt) ⟩
... | inj₁ ⟨ t , f ⟩ = f
... | inj₂ ⟨ f , t ⟩ = f
