{-# OPTIONS --rewriting #-}
module Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Naturals

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ } → zero ≤ n
  s≤s : ∀ { m n : ℕ } → m ≤ n → succ m ≤ succ n

infix 4 _≤_

inv-s≤s : ∀ { m n : ℕ } → succ m ≤ succ n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero -> m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {succ n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n x₁ = z≤n
≤-trans (s≤s x) (s≤s x₁) = s≤s (≤-trans x x₁)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x) (s≤s x₁) = cong succ (≤-antisym x x₁)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (succ m) zero = flipped z≤n
≤-total (succ m) (succ n) with ≤-total m n
... | forward x = forward (s≤s x)
... | flipped x = flipped (s≤s x)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (succ n) p q x = s≤s (+-monoʳ-≤ n p q x)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p x rewrite +comm {x = m} {y = p} | +comm {x = n} {y = p} = +-monoʳ-≤ p m n x

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (succ n) p q x rewrite *succ n p = +-mono-≤ p q (n * p) (n * q) x (*-monoʳ-≤ n p q x)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p x rewrite *comm {x = m} {y = p} | *comm {x = n} {y = p} = *-monoʳ-≤ p m n x

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans left-proof right-proof
  where
    left-proof : m * p ≤ n * p
    left-proof = *-monoˡ-≤ m n p m≤n

    right-proof : n * p ≤ n * q
    right-proof = *-monoʳ-≤ n p q p≤q

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < succ n
  s<s : ∀ {m n : ℕ} → m < n → succ m < succ n

infix 4 _<_

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s x₁) = z<s
<-trans (s<s x) (s<s x₁) = s<s (<-trans x x₁)

open import Data.Empty

<-refl-⊥ : (n : ℕ) → ((n : ℕ) → n < n) -> ⊥
<-refl-⊥ zero proof with proof zero
... | ()
<-refl-⊥ (succ n) proof = <-refl-⊥ n proof

data Trichotomy (m n : ℕ) : Set where
  ineqˡ : m < n → Trichotomy m n
  ineqʳ : n < m → Trichotomy m n
  eq    : m ≡ n → Trichotomy m n

trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (succ n) = ineqˡ z<s
trichotomy (succ m) zero = ineqʳ z<s
trichotomy (succ m) (succ n) with trichotomy m n
... | ineqˡ x = ineqˡ (s<s x)
... | ineqʳ x = ineqʳ (s<s x)
... | eq x = eq (cong succ x)

+-monoʳ-< : (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (succ n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p x rewrite +comm {x = m} {y = p} | +comm {x = n} {y = p} = +-monoʳ-< p m n x

+-mono-< : (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : (m n : ℕ) → succ m ≤ n → m < n
≤-iff-< zero .(succ _) (s≤s x) = z<s
≤-iff-< (succ m) (succ n) (s≤s x) = s<s (≤-iff-< m n x)

<-if-≤ : (m n : ℕ) → m < n → succ m ≤ n
<-if-≤ .zero .(succ _) z<s = s≤s z≤n
<-if-≤ (succ m) (succ n) (s<s x) = s≤s (<-if-≤ m n x)

≤-succ : (m n : ℕ) → m ≤ n → m ≤ succ n
≤-succ .zero n z≤n = z≤n
≤-succ (succ m) (succ n) (s≤s x) = s≤s (≤-succ m n x)

<-trans-revisited : (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p = ≤-iff-< m p (trans-ir)
  where
    m≤n : succ m ≤ n
    m≤n = <-if-≤ m n m<n

    n≤p : succ n ≤ p
    n≤p = <-if-≤ n p n<p

    trans-ir : succ m ≤ p
    trans-ir = ≤-trans (≤-succ (succ m) n m≤n) n≤p

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  succ : ∀ {n : ℕ} → odd n → even (succ n)

data odd where
  succ : ∀ {n : ℕ} → even n → odd (succ n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero     en = en
e+e≡e (succ om) en = succ (o+e≡o om en)

o+e≡o (succ em) en = succ (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (succ zero) n = succ n
o+o≡e (succ (succ x)) n = succ (succ (o+o≡e x n))
