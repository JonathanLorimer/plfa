{-# OPTIONS --rewriting #-}
module Bins.Relations where

open import Bins
open import Naturals
open import Relations

data One : (b : Bin) → Set

data One where
  ⟨⟩I : One (⟨⟩ I)
  _I¹ : ∀ {b : Bin} → One b → One (b I)
  _O¹ : ∀ {b : Bin} → One b → One (b O)

data Can : (b : Bin) → Set

data Can where
  zero : Can (⟨⟩ O)
  bits : ∀ {b : Bin} → One b → Can b

one-inc : ∀ {b : Bin} → One b → One (inc b)
one-inc ⟨⟩I = ⟨⟩I O¹
one-inc (x O¹) = x I¹
one-inc (x I¹) = one-inc x O¹

can-inc : ∀ {b : Bin} → Can b → Can (inc b)
can-inc zero = bits ⟨⟩I
can-inc (bits x) = bits (one-inc x)

can-to : (n : ℕ) → Can (to n)
can-to zero = zero
can-to (succ n) = can-inc (can-to n)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)


from-n-≤-from-m : {b : Bin} → (n : ℕ) → (m : ℕ) → One b → n ≤ m → from' n b ≤ from' m b
from-n-≤-from-m .zero zero ⟨⟩I z≤n = s≤s z≤n
from-n-≤-from-m .zero (succ n) ⟨⟩I z≤n rewrite refl = ?  -- x zero m ⟨⟩I (s≤s z≤n)
from-n-≤-from-m .(succ _) .(succ _) ⟨⟩I (s≤s x₂) rewrite refl = {! !}
from-n-≤-from-m n m (x₁ I¹) x₂ rewrite refl = {! !}
from-n-≤-from-m n m (x₁ O¹) x₂ rewrite refl = {! !}


one-≤-one-O : {b : Bin} → (b₁ : One b) → from b ≤ from (b O)
one-≤-one-O ⟨⟩I = s≤s z≤n
one-≤-one-O (_I¹ {b} one) = s≤s (+-mono-≤ 0 1 (from (b O)) (from ((b O) O)) z≤n (one-≤-one-O (one O¹)))
one-≤-one-O (_O¹ {b} one) = from-n-≤-from-m 1 2 one (s≤s z≤n)

-- Also, you may need to prove that if One b then 1 is less or equal to the result of from b.
1-≤-One : {b : Bin} → (b₁ : One b) → 1 ≤ from b
1-≤-One ⟨⟩I = s≤s z≤n
1-≤-One (one I¹) = s≤s z≤n
1-≤-One (one O¹) = ≤-trans (1-≤-One one) (one-≤-one-O one)  -- need to somehow

one-to-from : (b : Bin) → One b → to (from b) ≡ b
one-to-from .(⟨⟩ I) ⟨⟩I = refl
one-to-from (b I) (x I¹) =
  begin
  inc (to (from (b O)))
  ≡⟨ cong inc (one-to-from (b O) (x O¹)) ⟩
  b I
  ∎
one-to-from (b O) (x O¹) = ?
  -- begin
  -- to (from (b O))
  -- -- to (from' (zero + 1) b)
  -- ≡⟨ one-to-from b x ⟩
  -- ?
  -- ≡⟨ ? ⟩
  -- b O
  -- ∎

-- from' : ℕ -> Bin -> ℕ
-- from' _ ⟨⟩ = zero
-- from' exponent (x I) = 2 ^ exponent + (from' (exponent + 1)  x)
-- from' exponent (x O) = from' (exponent + 1) x

-- inc-≡-succ-general : (e : ℕ) → (b : Bin) → from' e (inc b) ≡ 2 ^ e + from' e b

-- can-to-from : (b : Bin) → Can b → to (from b) ≡ b
-- can-to-from .(⟨⟩ O) zero = refl
-- can-to-from (b O) (bits x) =
--   begin
--   to (from' (zero + 1) b)
--   ≡⟨⟩
--   to (from' 1 b)
--   ≡⟨ ? ⟩
--   b O
--   ∎
-- can-to-from (b I) (bits x) = {! !}


-- from' : ℕ -> Bin -> ℕ
-- from' _ ⟨⟩ = zero
-- from' exponent (x I) = 2 ^ exponent + (from' (exponent + 1)  x)
-- from' exponent (x O) = from' (exponent + 1) x
