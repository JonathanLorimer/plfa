module Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Isomorphism using (_≃_; extensionality; _∘_)


infix 3 ¬_

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ { ¬x → ¬x x }

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x = λ { x → ¬¬¬x (¬¬-intro x) }

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬b = ¬b ∘ f

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ { x → ⊥-elim (¬x x) }

assimilation′ : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation′ ¬x ¬x′ = refl

open _≤_

<-irreflexive : ∀ (n : ℕ) → ¬ n < n
<-irreflexive zero = λ { () }
<-irreflexive (suc n) = λ { (s≤s x) → (<-irreflexive n) x }

data Trichotomy (A B C : Set) : Set where
  opt₁ : A → (¬ B) → (¬ C) → Trichotomy A B C
  opt₂ : (¬ A) → B → (¬ C) → Trichotomy A B C
  opt₃ : (¬ A) → (¬ B) → C → Trichotomy A B C

suc≡-implies-≡ : ∀ (n m : ℕ) → suc n ≡ suc m → n ≡ m
suc≡-implies-≡ n .n refl = refl

trichotomy : ∀ (n m : ℕ) → Trichotomy (n < m) (m ≡ n) (m < n)
trichotomy zero zero = opt₂ (<-irreflexive zero) refl (<-irreflexive zero)
trichotomy zero (suc m) = opt₁ (s≤s z≤n) (λ { () }) (λ { () })
trichotomy (suc n) zero = opt₃ (λ { () }) (λ { () }) (s≤s z≤n)
trichotomy (suc n) (suc m) with trichotomy n m
... | opt₁ a b c = opt₁ (s≤s a) (λ { x → b (suc≡-implies-≡ m n x) }) (λ { (s≤s x) → c x })
... | opt₂ a b c = opt₂ (λ { (s≤s x) → a x }) (cong suc b) (λ { (s≤s x) → c x })
... | opt₃ a b c = opt₃ (λ { (s≤s x) → a x }) (λ { x → b (suc≡-implies-≡ m n x) }) (s≤s c)

de-morgans : ∀ { A B : Set } → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
de-morgans =
  record
    { to = λ { x → x ∘ inj₁ , x ∘ inj₂ }
    ; from = λ { (fst , snd) (inj₁ x) → fst x
               ; (fst , snd) (inj₂ x) → snd x
               }
    ; from∘to = λ { x → refl }
    ; to∘from = λ { y → refl }
    }

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (k ∘ inj₁))
