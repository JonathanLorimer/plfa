module Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Function.Base using (case_of_)
open import Data.Empty using (⊥; ⊥-elim)

open import Isomorphism using (_≃_; extensionality)
open Isomorphism.≃-Reasoning

∀-elim : ∀ {A : Set} {B : A → Set} → (L : ∀ (x : A) → B x) → (M : A) → B M
∀-elim L M = L M

∀-distrib-×
  : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ { x → ⟨ proj₁ ∘ x , proj₂ ∘ x ⟩ }
    ; from = λ { ⟨ fst , snd ⟩ x₁ → ⟨ fst x₁ , snd x₁ ⟩ }
    ; from∘to = λ { x → refl }
    ; to∘from = λ { y → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) a = inj₁ (f a)
⊎∀-implies-∀⊎ (inj₂ f) a = inj₂ (f a)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  ezero : even zero
  esuc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  osuc : ∀ {n : ℕ} → even n → odd (suc n)

evenOrOdd : (x : ℕ) → even x ⊎ odd x
evenOrOdd zero = inj₁ ezero
evenOrOdd (suc x) with evenOrOdd x
... | inj₁ y = inj₂ (osuc y)
... | inj₂ z = inj₁ (esuc z)

∀⊎-implies-⊎∀
  : ( ∀ {A : Set} {B C : A → Set}
    → (∀ (x : A) → B x ⊎ C x)
    → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
    )
  → ⊥
∀⊎-implies-⊎∀ f with (f { A = ℕ } { B = even } { C = odd } evenOrOdd)
... | inj₁ x = case x 1 of
                λ { (esuc ()) }
... | inj₂ y = case y 0 of
                λ { () }


data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀
    {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
    → f ≡ g

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to = λ { x → ⟨ x aa , ⟨ x bb , x cc ⟩ ⟩ }
    ; from = λ { x aa → proj₁ x
               ; x bb → proj₁ (proj₂ x)
               ; x cc → proj₂ (proj₂ x)
               }
    ; from∘to = λ { x → ∀-extensionality λ { aa → refl
                                           ; bb → refl
                                           ; cc → refl }  }
    ; to∘from = λ { y → refl }
    }

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

sample : (n : ℕ) → Σ ℕ even
sample zero = ⟨ zero , ezero ⟩
sample (suc n) with sample n
... | ⟨ x , x₁ ⟩ = ⟨ suc (suc x) , esuc (osuc x₁) ⟩

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
_≃_.to ∃-distrib-⊎ ⟨ x , inj₁ x₁ ⟩ = inj₁ ⟨ x , x₁ ⟩
_≃_.to ∃-distrib-⊎ ⟨ x , inj₂ y ⟩ = inj₂ ⟨ x , y ⟩
_≃_.from ∃-distrib-⊎ (inj₁ ⟨ x , x₁ ⟩) = ⟨ x , inj₁ x₁ ⟩
_≃_.from ∃-distrib-⊎ (inj₂ ⟨ x , x₁ ⟩) = ⟨ x , inj₂ x₁ ⟩
_≃_.from∘to ∃-distrib-⊎ ⟨ x , inj₁ x₁ ⟩ = refl
_≃_.from∘to ∃-distrib-⊎ ⟨ x , inj₂ y ⟩ = refl
_≃_.to∘from ∃-distrib-⊎ (inj₁ ⟨ x , x₁ ⟩) = refl
_≃_.to∘from ∃-distrib-⊎ (inj₂ ⟨ x , x₁ ⟩) = refl


∃-× : {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
_≃_.to ∃-× ⟨ aa , x₁ ⟩ = inj₁ x₁
_≃_.to ∃-× ⟨ bb , x₁ ⟩ = inj₂ (inj₁ x₁)
_≃_.to ∃-× ⟨ cc , x₁ ⟩ = inj₂ (inj₂ x₁)
_≃_.from ∃-× (inj₁ x) = ⟨ aa , x ⟩
_≃_.from ∃-× (inj₂ (inj₁ x)) = ⟨ bb , x ⟩
_≃_.from ∃-× (inj₂ (inj₂ x)) = ⟨ cc , x ⟩
_≃_.from∘to ∃-× ⟨ aa , x₁ ⟩ = refl
_≃_.from∘to ∃-× ⟨ bb , x₁ ⟩ = refl
_≃_.from∘to ∃-× ⟨ cc , x₁ ⟩ = refl
_≃_.to∘from ∃-× (inj₁ x) = refl
_≃_.to∘from ∃-× (inj₂ (inj₁ x)) = refl
_≃_.to∘from ∃-× (inj₂ (inj₂ x)) = refl

open import Data.Nat.Properties

open _≤_

≡⇒≤ : ( x y : ℕ ) → x ≡ y → x ≤ y
≡⇒≤ zero zero x₁ = z≤n
≡⇒≤ (suc x) (suc .x) refl = s≤s (≡⇒≤ x x refl)

∃-+-≤ : {y z : ℕ} → Σ ℕ (λ { x → x + y ≡ z }) → y ≤ z
∃-+-≤ {zero} {.(zero + zero)} ⟨ zero , refl ⟩ = z≤n
∃-+-≤ {suc y} {.(zero + suc y)} ⟨ zero , refl ⟩ = s≤s (∃-+-≤ ⟨ 0 , refl ⟩)
∃-+-≤ {zero} {.(suc x + zero)} ⟨ suc x , refl ⟩ = z≤n
∃-+-≤ {suc y} {.(suc x + suc y)} ⟨ suc x , refl ⟩ = s≤s (∃-+-≤ ⟨ x + 1 , +-assoc x 1 y ⟩)

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , y ⟩ = λ { z → y (z x) }
