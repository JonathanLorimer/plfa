{-# OPTIONS --rewriting #-}
module Naturals where
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

seven : ℕ
seven = succ (succ (succ (succ (succ (succ (succ zero))))))

{-# BUILTIN NATURAL ℕ #-}

seven' : ℕ
seven' = 7

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
(succ m) + n = succ (m + n)

_*_ : ℕ -> ℕ -> ℕ
zero * n = zero
(succ m) * n = n + (m * n)

_^_ : ℕ -> ℕ -> ℕ
m ^ zero  = 1
m ^ (succ n) = m * (m ^ n)

_∸_ : ℕ -> ℕ -> ℕ
m ∸ zero = m
zero ∸ (succ n) = zero
(succ m) ∸ (succ n) = m ∸ n

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

+zero : { n : ℕ } -> n + zero ≡ n
+zero {zero} = refl
+zero {succ a} = cong succ +zero

+succ : { n m : ℕ } -> n + (succ m) ≡ succ (n + m)
+succ {zero} = refl
+succ {succ a} = cong succ +succ

*zerol : { n : ℕ } -> zero * n ≡ zero
*zerol {zero} = refl
*zerol {succ a} = refl

*one : { n : ℕ } -> n * 1 ≡ n
*one {zero} = refl
*one {succ a} =
  begin
  succ a * 1
  ≡⟨⟩
  1 + (a * 1)
  ≡⟨ cong (1 +_) (*one {n = a}) ⟩
  1 + a
  ≡⟨⟩
  succ a
  ∎

^one : { n : ℕ } -> n ^ 1 ≡ n
^one {n} =
  begin
  n ^ 1
  ≡⟨⟩
  n * (n ^ zero)
  ≡⟨⟩
  n * 1
  ≡⟨ *one {n = n} ⟩
  n
  ∎

{-# BUILTIN REWRITE _≡_ #-}

{-# REWRITE +zero +succ #-}

*zeror : { n : ℕ } -> n * zero ≡ zero
*zeror {zero} = refl
*zeror {succ a} =
  begin
  (succ a) * zero
  ≡⟨⟩
  zero + (a * zero)
  ≡⟨ +zero ⟩
  (a * zero)
  ≡⟨ *zeror {n = a} ⟩
  zero
  ∎

+comm : { x y : ℕ } -> x + y ≡ y + x
+comm {zero} = refl
+comm {succ x} {y} = cong succ (+comm {x = x} {y = y})

+zeroʳ : (n : ℕ) -> zero + n ≡ n
+zeroʳ n rewrite +comm {x = n} {y = zero} = +zero

+assoc : { a b c : ℕ } -> (a + b) + c ≡ a + (b + c)
+assoc { zero } { b } { c } = refl
+assoc { succ a } { b } { c } = cong succ (+assoc {a = a} {b = b} {c = c})

+dist : { a b c : ℕ } -> (a + b) * c ≡ (a * c) + (b * c)
+dist {zero} {b} {c} = refl
+dist {succ a} {b} {c} =
  begin
  (succ a + b) * c
  ≡⟨⟩
  succ (a + b) * c
  ≡⟨⟩
  c + ((a + b) * c)
  ≡⟨ cong (c +_) (+dist {a = a} {b = b} {c = c}) ⟩
  c + ((a * c) + (b * c))
  ≡⟨ sym (+assoc {a = c} {b = a * c} {c = b * c}) ⟩
  (c + (a * c)) + (b * c)
  ≡⟨⟩
  (succ a * c) + (b * c)
  ∎

+swap : { m n p : ℕ } -> m + (n + p) ≡ n + (m + p)
+swap {m} {n} {p} =
  begin
  m + (n + p)
  ≡⟨ sym (+assoc {a = m} {b = n} {c = p}) ⟩
  (m + n) + p
  ≡⟨ cong (_+ p) (+comm {x = m} {y = n}) ⟩
  (n + m) + p
  ≡⟨ +assoc {a = n} {b = m} {c = p} ⟩
  n + (m + p)
  ∎

∸zerol : {n : ℕ} -> zero ∸ n ≡ zero
∸zerol {zero} = refl
∸zerol {succ n} = refl

∸assoc : { m n p : ℕ } -> m ∸ n ∸ p ≡ m ∸ (n + p)
∸assoc {zero} {n} {p} =
  begin
  (zero ∸ n) ∸ p
  ≡⟨ cong (_∸ p) (∸zerol {n = n}) ⟩
  zero ∸ p
  ≡⟨ ∸zerol {n = p} ⟩
  zero
  ≡⟨ sym (∸zerol {n = n + p}) ⟩
  zero ∸ (n + p)
  ∎
∸assoc {succ m} {zero} {zero} = refl
∸assoc {succ m} {zero} {succ p} = refl
∸assoc {succ m} {succ n} {zero} = refl
∸assoc {succ m} {succ n} {succ p} =
  begin
  (succ m) ∸ (succ n) ∸ (succ p)
  ≡⟨⟩
  m ∸ n ∸ (succ p)
  ≡⟨⟩
  (m ∸ n) ∸ (1 + p)
  ≡⟨ sym (∸assoc {m = m ∸ n} {n = 1} {p = p}) ⟩
  m ∸ n ∸ 1 ∸ p
  ≡⟨ cong (_∸ p) (∸assoc {m = m} {n = n} {p = 1}) ⟩
  m ∸ (n + 1) ∸ p
  ≡⟨⟩
  m ∸ (1 + n) ∸ p
  ≡⟨ ∸assoc {m = m} {n = 1 + n} {p = p} ⟩
  m ∸ (1 + (n + p))
  ≡⟨⟩
  succ m ∸ (1 + (1 + (n + p)))
  ≡⟨ cong (succ m ∸_) (cong (1 +_) (+swap {m = 1} {n = n} {p = p})) ⟩
  succ m ∸ (1 + (n + (1 + p)))
  ≡⟨⟩
  succ m ∸ ((1 + n) + (1 + p))
  ≡⟨⟩
  (succ m) ∸ ((succ n) + (succ p))
  ∎

*succ : ∀ m n → m * succ n ≡ m + m * n
*succ zero n = refl
*succ (succ m) n =
  begin
  succ m * succ n
  ≡⟨ cong (succ n +_) (*succ m n) ⟩
  succ (n + (m + m * n))
  ≡⟨ cong succ (sym (+assoc {a = n} {b = m} {c = m * n})) ⟩
  succ (n + m + m * n)
  ≡⟨ cong (λ x → succ (x + m * n)) (+comm {x = n} {y = m}) ⟩
  succ (m + n + m * n)
  ≡⟨ cong succ (+assoc {a = m} {b = n} {c = (m * n)}) ⟩
  succ (m + succ m * n)
  ∎

+-to-* : (n : ℕ) → n + n ≡ 2 * n
+-to-* n = refl


*comm : { x y : ℕ } -> x * y ≡ y * x
*comm {zero} {y} =
  begin
  zero * y
  ≡⟨ *zerol {n = y} ⟩
  zero
  ≡⟨ sym (*zeror {n = y}) ⟩
  y * zero
  ∎
*comm {succ x} {zero} =
  begin
  succ x * zero
  ≡⟨ *zeror {n = succ x} ⟩
  zero
  ≡⟨ sym (*zerol {n = succ x}) ⟩
  zero * succ x
  ∎
*comm {succ x} {succ y} =
  begin
  succ x * succ y
  ≡⟨⟩
  succ y + (x * (succ y))
  ≡⟨ cong (succ y +_) (*comm { x = x } { y = succ y }) ⟩
  succ y + ((succ y) * x)
  ≡⟨⟩
  succ y + ((1 * x) + (y * x))
  ≡⟨⟩
  succ y + (x + (y * x))
  ≡⟨⟩
  (1 + y) + (x + (y * x))
  ≡⟨ cong (1 + y +_) (cong (x +_) (*comm { x = y } { y = x }) ) ⟩
  (1 + y) + (x + (x * y))
  ≡⟨ sym (+assoc { a = 1 + y } { b = x } { c = x * y } )⟩
  ((1 + y) + x) + (x * y)
  ≡⟨⟩
  (1 + (y + x)) + (x * y)
  ≡⟨ cong (_+ x * y) (cong (1 +_) (+comm {x = y} {y = x})) ⟩
  (1 + (x + y)) + (x * y)
  ≡⟨ cong (_+ x * y) (sym (+assoc {a = 1} {b = x} {c = y})) ⟩
  ((1 + x) + y) + (x * y)
  ≡⟨ +assoc {a = succ x} {b = y} {c = x * y} ⟩
  (1 + x) + (y + (x * y))
  ≡⟨⟩
  (1 + x) + ((1 * y) + (x * y))
  ≡⟨ cong (1 + x +_) (*comm {x = succ x} { y = y } )⟩
  (1 + x) + (y * (1 + x))
  ≡⟨⟩
  succ x + (y * (succ x))
  ≡⟨⟩
  succ y * succ x
  ∎

*assoc : { a b c : ℕ } -> (a * b) * c ≡ a * (b * c)
*assoc { zero } { b } { c } = refl
*assoc { succ a } { b } { c } =
  begin
  (succ a * b) * c
  ≡⟨⟩
  (b + (a * b)) * c
  ≡⟨ +dist {a = b} {b = a * b} {c = c} ⟩
  (b * c) + ((a * b) * c)
  ≡⟨ cong ((b * c) +_) (*assoc {a = a} {b = b} {c = c}) ⟩
  (b * c) + (a * (b * c))
  ≡⟨⟩
  succ a * (b * c)
  ∎

^squared : { m : ℕ } -> m * m ≡ m ^ 2
^squared {m} =
  begin
  m * m
  ≡⟨ cong (m *_) (sym (^one {n = m})) ⟩
  m * (m ^ 1)
  ≡⟨⟩
  m ^ 2
  ∎

^distrib+ : {m n p : ℕ } -> m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^distrib+ {m} {zero} {p} = refl
^distrib+ {m} {succ n} {p} =
  begin
  m ^ (succ n + p)
  ≡⟨⟩
  m * m ^ (n + p)
  ≡⟨ cong (m *_) (^distrib+ {m = m} {n = n} {p = p}) ⟩
  m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*assoc {a = m} {b = m ^ n} {c = m ^ p}) ⟩
  m * (m ^ n) * (m ^ p)
  ≡⟨ cong (_* (m ^ p)) (cong (_* (m ^ n)) (sym (^one {n = m}))) ⟩
  (m ^ 1) * (m ^ n) * (m ^ p)
  ≡⟨ cong (_* m ^ p) (*comm {x = m ^ 1} {y = m ^ n}) ⟩
  (m ^ n) * (m ^ 1) * (m ^ p)
  ≡⟨ cong (_* m ^ p) (sym (^distrib+ {m = m} {n = n} {p = 1})) ⟩
  (m ^ succ n) * (m ^ p)
  ∎

^distrib* : {m n p : ℕ } ->  (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^distrib* {m} {n} {zero} = refl
^distrib* {m} {n} {succ p} =
  begin
  (m * n) ^ (succ p)
  ≡⟨⟩
  (m * n) * ((m * n) ^ p)
  ≡⟨ cong (m * n *_) (^distrib* {m = m} {n = n} {p = p}) ⟩
  (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*assoc {a = m * n} {b = m ^ p} {c = n ^ p}) ⟩
  ((m * n) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (cong (_* (m ^ p)) (*comm {x = m} {y = n})) ⟩
  ((n * m) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*assoc {a = n} {b = m} {c = m ^ p}) ⟩
  (n * (m * (m ^ p))) * (n ^ p)
  ≡⟨⟩
  (n * (m ^ succ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*comm {x = n} {y = m ^ succ p}) ⟩
  ((m ^ succ p) * n) * (n ^ p)
  ≡⟨ *assoc {a = m ^ succ p} {b = n} {c = n ^ p} ⟩
  (m ^ succ p) * (n * (n ^ p))
  ≡⟨⟩
  (m ^ succ p) * (n ^ succ p)
  ∎

^assoc : {m n p : ℕ } -> (m ^ n) ^ p ≡ m ^ (n * p)
^assoc {m} {n} {zero} =
  begin
  (m ^ n) ^ zero
  ≡⟨ cong (m ^_) (sym (*zeror { n = n })) ⟩
  m ^ (n * zero)
  ∎
^assoc {m} {n} {succ p} =
  begin
  (m ^ n) ^ (succ p)
  ≡⟨ ^distrib+ {m = m ^ n} {n = 1} {p = p} ⟩
  ((m ^ n) ^ 1) * ((m ^ n) ^ p)
  ≡⟨ cong (_* ((m ^ n) ^ p)) (^one {n = m ^ n}) ⟩
  (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong (m ^ n *_) (^assoc {m = m} {n = n} {p = p}) ⟩
  (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^distrib+ {m = m} {n = n} {p = n * p}) ⟩
  m ^ (n + (n * p))
  ≡⟨ cong (m ^_) (cong (n +_) (*comm {x = n} {y = p})) ⟩
  m ^ (n + (p * n))
  ≡⟨⟩
  m ^ ((succ p) * n)
  ≡⟨ cong (m ^_) (*comm {x = succ p} {y = n}) ⟩
  m ^ (n * succ p)
  ∎
