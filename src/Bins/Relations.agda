{-# OPTIONS --rewriting #-}
module Bins.Relations where

open import Bins
open import Naturals

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

-- one-to-from : (n : ℕ) → (b : Bin) → One b → to (from' n b) ≡ b
-- one-to-from .(⟨⟩ I) ⟨⟩I = refl
-- one-to-from (b I) (x I¹) =
--   begin
--   inc (to (from' (0 + 1) b))
--   ≡⟨ ? ⟩
--   b I
--   ∎
-- one-to-from (b O) (x O¹) =
--   begin
--   to (from (b O))
--   ≡⟨ ? ⟩
--   b O
--   ∎

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
