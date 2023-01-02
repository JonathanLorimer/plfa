import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-zeroʳ; *-suc; *-comm; +-cancelˡ-≡; +-cancelʳ-≡)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ } → zero ≤ n
  s≤s : ∀ { m n : ℕ } → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ { m n : ℕ } → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero -> m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n x₁ = z≤n
≤-trans (s≤s x) (s≤s x₁) = s≤s (≤-trans x x₁)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s x) (s≤s x₁) = cong suc (≤-antisym x x₁)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward x = forward (s≤s x)
... | flipped x = flipped (s≤s x)

+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q x = s≤s (+-monoʳ-≤ n p q x)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p x rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n x

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q x rewrite *-suc n p = +-mono-≤ p q (n * p) (n * q) x (*-monoʳ-≤ n p q x)

*-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p x rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n x

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans left-proof right-proof
  where
    left-proof : m * p ≤ n * p
    left-proof = *-monoˡ-≤ m n p m≤n

    right-proof : n * p ≤ n * q
    right-proof = *-monoʳ-≤ n p q p≤q

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s (s<s x₁) = z<s
<-trans (s<s x) (s<s x₁) = s<s (<-trans x x₁)

open import Data.Empty

<-refl-⊥ : (n : ℕ) → ((n : ℕ) → n < n) -> ⊥
<-refl-⊥ zero proof with proof zero
... | ()
<-refl-⊥ (suc n) proof = <-refl-⊥ n proof

data Trichotomy (m n : ℕ) : Set where
  ineqˡ : m < n → Trichotomy m n
  ineqʳ : n < m → Trichotomy m n
  eq    : m ≡ n → Trichotomy m n

trichotomy : (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eq refl
trichotomy zero (suc n) = ineqˡ z<s
trichotomy (suc m) zero = ineqʳ z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | ineqˡ x = ineqˡ (s<s x)
... | ineqʳ x = ineqʳ (s<s x)
... | eq x = eq (cong suc x)

+-monoʳ-< : (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p x rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n x

+-mono-< : (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero .(suc _) (s≤s x) = z<s
≤-iff-< (suc m) (suc n) (s≤s x) = s<s (≤-iff-< m n x)

<-if-≤ : (m n : ℕ) → m < n → suc m ≤ n
<-if-≤ .zero .(suc _) z<s = s≤s z≤n
<-if-≤ (suc m) (suc n) (s<s x) = s≤s (<-if-≤ m n x)

≤-suc : (m n : ℕ) → m ≤ n → m ≤ suc n
≤-suc .zero n z≤n = z≤n
≤-suc (suc m) (suc n) (s≤s x) = s≤s (≤-suc m n x)

<-trans-revisited : (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p m<n n<p = ≤-iff-< m p (trans-ir)
  where
    m≤n : suc m ≤ n
    m≤n = <-if-≤ m n m<n

    n≤p : suc n ≤ p
    n≤p = <-if-≤ n p n<p

    trans-ir : suc m ≤ p
    trans-ir = ≤-trans (≤-suc (suc m) n m≤n) n≤p

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero) n = suc n
o+o≡e (suc (suc x)) n = suc (suc (o+o≡e x n))
