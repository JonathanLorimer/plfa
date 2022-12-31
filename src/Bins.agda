{-# OPTIONS --rewriting #-}
open import Naturals
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Data.Empty

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

inc : Bin -> Bin
inc ⟨⟩ = (⟨⟩ I)
inc (x O) = x I
inc (x I) = (inc x) O

inc-proof-0 : inc (⟨⟩ O) ≡ ⟨⟩ I
inc-proof-0 = refl

inc-proof-1 : inc (⟨⟩ I) ≡ ⟨⟩ I O
inc-proof-1 = refl

inc-proof-2 : inc (⟨⟩ I O) ≡ ⟨⟩ I I
inc-proof-2 = refl

inc-proof-3 : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
inc-proof-3 = refl

inc-proof-4 : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
inc-proof-4 = refl

inc-proof-11 : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
inc-proof-11 = refl

to : ℕ -> Bin
to zero = ⟨⟩
to (succ n) = inc (to n)

_ : to 0 ≡ ⟨⟩
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

_ : to 11 ≡ ⟨⟩ I O I I
_ = refl

from' : ℕ -> Bin -> ℕ
from' _ ⟨⟩ = zero
from' exponent (x I) = 2 ^ exponent + (from' (exponent + 1)  x)
from' exponent (x O) = from' (exponent + 1) x

from : Bin -> ℕ
from = from' zero

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

_ : from (⟨⟩ I O I I) ≡ 11
_ = refl

inc-≡-succ-general : (e : ℕ) → (b : Bin) → from' e (inc b) ≡ 2 ^ e + from' e b
inc-≡-succ-general zero ⟨⟩ = refl
inc-≡-succ-general zero (b O) = refl
inc-≡-succ-general zero (b I) =
  begin
  from' zero (inc (b I))
  ≡⟨⟩
  from' zero ((inc b) O)
  ≡⟨⟩
  from' 1 (inc b)
  ≡⟨ inc-≡-succ-general 1 b ⟩
  2 ^ 1 + from' 1 b
  ≡⟨⟩
  1 + from' zero (b I)
  ≡⟨⟩
  (2 ^ zero) + from' zero (b I)
  ∎
inc-≡-succ-general (succ e) ⟨⟩ = refl
inc-≡-succ-general (succ e) (b O) = refl
inc-≡-succ-general (succ e) (b I) =
  begin
  from' (succ e) (inc (b I))
  ≡⟨⟩
  from' (succ e) ((inc b) O)
  ≡⟨⟩
  from' (succ (succ e)) (inc b)
  ≡⟨ inc-≡-succ-general (succ (succ e)) b ⟩
  2 ^ (succ (succ e)) + from' (succ (succ e)) b
  ≡⟨⟩
  (2 * (2 ^ e)) + (2 * (2 ^ e)) + (from' (succ (succ e)) b)
  ≡⟨ +assoc {a = 2 * (2 ^ e)} {b = 2 * (2 ^ e)} {c = from' (succ (succ e)) b} ⟩
  2 * (2 ^ e) + (2 * (2 ^ e) + (from' (succ (succ e)) b))
  ≡⟨ cong (2 * (2 ^ e) +_) (+comm {x = 2 * (2 ^ e)} {y = (from' (succ (succ e)) b)}) ⟩
  2 * (2 ^ e) + ((from' (succ (succ e)) b) + (2 * (2 ^ e)))
  ≡⟨ sym (cong (_+ ((from' (succ (succ e)) b) + (2 * (2 ^ e)))) (^distrib+ {m = 2} {n = 1} {p = e}))⟩
  (2 ^ (1 + e)) + ((from' (succ (succ e)) b) + (2 * (2 ^ e)))
  ≡⟨⟩
  (2 ^ (succ e)) + ((from' (succ (succ e)) b) + (2 * (2 ^ e)))
  ≡⟨ sym (+assoc {a = 2 ^ (succ e)} {b = (from' (succ (succ e)) b)} {c = (2 * (2 ^ e))} )⟩
  ((2 ^ (succ e)) + (from' (succ (succ e)) b)) + (2 * (2 ^ e))
  ≡⟨ +comm {x = ((2 ^ (succ e)) + (from' (succ (succ e)) b))} {y = 2 * (2 ^ e)} ⟩
  2 * (2 ^ e) + ((2 ^ (succ e)) + (from' (succ (succ e)) b))
  ≡⟨⟩
  (2 ^ 1) * (2 ^ e) + ((2 ^ (succ e)) + (from' (succ (succ e)) b))
  ≡⟨ sym (cong (_+ ((2 ^ (1 + e)) + (from' (succ (succ e)) b))) (^distrib+ {m = 2} {n = 1} {p = e}))⟩
  (2 ^ (1 + e)) + ((2 ^ (1 + e)) + (from' (succ (succ e)) b))
  ≡⟨⟩
  (2 ^ (succ e)) + from' (succ e) (b I)
  ∎

inc-≡-succ : { b : Bin } -> from (inc b) ≡ succ (from b)
inc-≡-succ {⟨⟩} = refl
inc-≡-succ {b O} = refl
inc-≡-succ {b I} = inc-≡-succ-general zero (b I)

bin-to-from-counter : ((bin : Bin) -> to (from bin) ≡ bin) → ⊥
bin-to-from-counter prop with prop (⟨⟩ O O)
... | ()

bin-from-to : ( n : ℕ ) → from (to n) ≡ n
bin-from-to zero = refl
bin-from-to (succ n) =
  begin
  from (to (succ n))
  ≡⟨⟩
  from (inc (to n))
  ≡⟨ inc-≡-succ {b = to n} ⟩
  succ (from (to n))
  ≡⟨ cong succ (bin-from-to n) ⟩
  succ n
  ∎

-- | Attempts to prove bin-to-from with the pre-condition that the bin is normalized
--------------------------------------------------------------------------------------
--
<>-bin : Bin -> Bin -> Bin
<>-bin b ⟨⟩ = b
<>-bin b (x O) = (<>-bin b x) O
<>-bin b (x I) = (<>-bin b x) I

norm-bin' : Bin -> Bin -> Bin
norm-bin' _ ⟨⟩ = ⟨⟩
norm-bin' acc (b O) = norm-bin' (acc O) b
norm-bin' acc (b I) = <>-bin ((norm-bin' ⟨⟩ b) I) acc

norm-bin : Bin -> Bin
norm-bin = norm-bin' ⟨⟩

_ : norm-bin (⟨⟩ O) ≡ ⟨⟩
_ = refl

_ : norm-bin (⟨⟩ O O) ≡ ⟨⟩
_ = refl

_ : norm-bin (⟨⟩ O I) ≡ ⟨⟩ I
_ = refl

_ : norm-bin (⟨⟩ O I O) ≡ ⟨⟩ I O
_ = refl

<>-bin-swap-⊥ : ((b : Bin) → (b' : Bin) → norm-bin (<>-bin b b') ≡ <>-bin (norm-bin b) b') → ⊥
<>-bin-swap-⊥ prop with prop ⟨⟩ (⟨⟩ O)
... | ()

<>-bin-dist-⊥ : ((b : Bin) → (b' : Bin) → norm-bin (<>-bin b b') ≡ <>-bin (norm-bin b) (norm-bin b')) → ⊥
<>-bin-dist-⊥ prop with prop (⟨⟩ I) (⟨⟩ O)
... | ()

idemp-norm-bin-lemma : (b : Bin) → (b' : Bin) → norm-bin (<>-bin (b I) b') ≡ <>-bin (norm-bin b I) b'
idemp-norm-bin-lemma b ⟨⟩ = refl
idemp-norm-bin-lemma b (b' O) =
  begin
  norm-bin (<>-bin (b I) (b' O))
  ≡⟨⟩
  norm-bin' ⟨⟩ (<>-bin (b I) (b' O))
  ≡⟨⟩
-- NOTE: Stuck, need to prove to agda that we can re-associate concatenation under normalization if the left hand
-- binary is non-zero (i.e. has an I somewhere)
  norm-bin ((<>-bin (b I) b') O)
  ≡⟨ ? ⟩
  (<>-bin (norm-bin b I) b') O
  ≡⟨⟩
  <>-bin (norm-bin b I) (b' O)
  ∎
idemp-norm-bin-lemma b (b' I) =
  begin
  norm-bin' ⟨⟩ (<>-bin (b I) b') I
  ≡⟨ cong (_I) (idemp-norm-bin-lemma b b') ⟩
  <>-bin (norm-bin b I) b' I
  ∎

idemp-norm-bin
  : (acc : Bin) → (b : Bin)
  → norm-bin (norm-bin' acc b) ≡ norm-bin' acc b
idemp-norm-bin a ⟨⟩ = refl
idemp-norm-bin a (bin O) =
  begin
  norm-bin' ⟨⟩ (norm-bin' (a O) bin)
  ≡⟨ idemp-norm-bin (a O) bin ⟩
  norm-bin' (a O) bin
  ∎
idemp-norm-bin ⟨⟩ (bin I) =
  begin
  norm-bin' ⟨⟩ (norm-bin' ⟨⟩ bin) I
  ≡⟨ cong (_I) (idemp-norm-bin ⟨⟩ bin) ⟩
  (norm-bin' ⟨⟩ bin) I
  ∎
idemp-norm-bin (a O) (bin I) =
  begin
  norm-bin' (⟨⟩ O) (<>-bin (norm-bin' ⟨⟩ bin I) a)
  ≡⟨ ? ⟩
  <>-bin (norm-bin' ⟨⟩ bin I) a O
  ∎
idemp-norm-bin (a I) (bin I) =
  begin
  norm-bin' ⟨⟩ (<>-bin ((norm-bin' ⟨⟩ bin) I) a) I
  ≡⟨ ? ⟩
  (<>-bin (norm-bin' ⟨⟩ bin I) a) I
  ∎

bin-to-from : (n : ℕ) → ( bin : Bin ) → norm-bin bin ≡ bin → to (from' n bin) ≡ bin
bin-to-from n ⟨⟩ norm = refl
bin-to-from n (b O) norm = ?
bin-to-from n (b I) norm = ?
