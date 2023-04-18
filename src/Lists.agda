module Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Level)
open import Isomorphism using (_≃_; _⇔_; extensionality)


data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
  x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
  x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
  x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
  x ∷ xs ++ ys ++ zs
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
  x ∷ xs ++ []
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
  x ∷ xs
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

reverse-distrib : ∀ {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-distrib [] ys =
  begin
  reverse ys
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
  reverse ys ++ []
  ≡⟨⟩
  reverse ys ++ reverse []
  ∎
reverse-distrib (x ∷ xs) ys =
  begin
  reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-distrib xs ys) ⟩
  ((reverse ys) ++ (reverse xs)) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
  (reverse ys) ++ ((reverse xs) ++ [ x ])
  ≡⟨⟩
  reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
  reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-distrib (reverse xs) [ x ] ⟩
  [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
  [ x ] ++ xs
  ≡⟨⟩
  x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

map-compose
  : ∀ {A B C : Set}
  → (f : A → B)
  → (g : B → C)
  → (xs : List A)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose f g [] = refl
map-compose f g (x ∷ xs) =
  begin
  (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong (((g ∘ f) x) ∷_) (map-compose f g xs) ⟩
  g (f x) ∷ map g (map f xs)
  ∎

map-++-distribute
  : ∀ {A B : Set}
  → (f : A → B)
  → (xs : List A)
  → (ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys =
  begin
  f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
  f x ∷ map f xs ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

product : List ℕ → ℕ
product = foldr (_*_) 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++
  : ∀ { A : Set }
  → (e : A)
  → (_⊗_ : A → A → A)
  → (xs : List A)
  → (ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ e _⊗_ [] ys = refl
foldr-++ e _⊗_ (x ∷ xs) ys =
  begin
  x ⊗ foldr _⊗_ e (xs ++ ys)
  ≡⟨ cong (x ⊗_) (foldr-++ e _⊗_ xs ys) ⟩
  x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs
  ∎

foldr-∷ : ∀ { A : Set } → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) =
  begin
  x ∷ foldr _∷_ [] xs
  ≡⟨ cong (x ∷_) (foldr-∷ xs) ⟩
  x ∷ xs
  ∎

map-is-foldr
  : ∀ { A B : Set }
  → (f : A → B)
  → (ys : List A)
  → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr f [] = refl
map-is-foldr f (y ∷ ys) =
  begin
  f y ∷ map f ys
  ≡⟨ cong ((f y) ∷_) (map-is-foldr f ys) ⟩
  f y ∷ foldr (λ x → _∷_ (f x)) [] ys
  ∎

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

map-Tree-is-fold-Tree
  : ∀ { A B C D : Set }
  → (f : A → C)
  → (g : B → D)
  → (tree : Tree A B)
  → map-Tree f g tree ≡ fold-Tree (λ a → leaf (f a)) (λ t₁ b t₂ → node t₁ (g b) t₂) tree
map-Tree-is-fold-Tree f g (leaf x) = refl
map-Tree-is-fold-Tree f g (node l x r) =
  begin
  node (map-Tree f g l) (g x) (map-Tree f g r)
  ≡⟨ cong (λ foldTree → node foldTree (g x) (map-Tree f g r)) (map-Tree-is-fold-Tree f g l) ⟩
  node (fold-Tree (λ a → leaf (f a)) (λ t₁ b → node t₁ (g b)) l) (g x) (map-Tree f g r)
  ≡⟨ cong (λ foldTree → node (fold-Tree (λ a → leaf (f a)) (λ t₁ b → node t₁ (g b)) l) (g x) foldTree) (map-Tree-is-fold-Tree f g r) ⟩
  node (fold-Tree (λ a → leaf (f a)) (λ t₁ b → node t₁ (g b)) l) (g x) (fold-Tree (λ a → leaf (f a)) (λ t₁ b → node t₁ (g b)) r)
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []        =  e
foldl _⊗_ e (x ∷ xs)  =  foldl _⊗_ (e ⊗ x) xs

_ : ∀ {A B : Set} → {_⊗_ : A → B → B} → {e : B} → {x y z : A} → foldr _⊗_ e [ x , y , z ] ≡  x ⊗ (y ⊗ (z ⊗ e))
_ = refl

_ : ∀ {A B : Set} → { _⊗_ : B → A → B } → { e : B } → { x y z : A } → foldl _⊗_ e [ x , y , z ] ≡ ((e ⊗ x) ⊗ y) ⊗ z
_ = refl

foldr-monoid
  : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A)
  → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
    begin
    y
    ≡⟨ sym (IsMonoid.identityˡ ⊗-monoid y)⟩
    e ⊗ y
    ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
    ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
  x ⊗ foldr _⊗_ y xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y)⟩
  x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (IsMonoid.assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
  (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
  foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldl-monoid
  : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A)
  → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e m [] y =
  begin
  y
  ≡⟨ sym (IsMonoid.identityʳ m y) ⟩
  y ⊗ foldl _⊗_ e []
  ∎
foldl-monoid _⊗_ e m (x ∷ xs) y =
  begin
  foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e m xs (y ⊗ x) ⟩
  (y ⊗ x) ⊗ (foldl _⊗_ e xs)
  ≡⟨ IsMonoid.assoc m y x (foldl _⊗_ e xs) ⟩
  y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e m xs x)) ⟩
  y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (λ { e⊗x → y ⊗ foldl _⊗_ e⊗x xs }) (sym (IsMonoid.identityˡ m x)) ⟩
  y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
  y ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl
  : ∀ { A : Set }
  → ( e : A ) ( _⊗_ : A → A → A )
  → IsMonoid _⊗_ e
  → (xs : List A)
  → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl e _⊗_ m [] = refl
foldr-monoid-foldl e _⊗_ m (x ∷ xs) =
  begin
  x ⊗ foldr _⊗_ e xs
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl e _⊗_ m xs) ⟩
  x ⊗ foldl _⊗_ e xs
  ≡⟨ cong (_⊗ foldl _⊗_ e xs) (sym (IsMonoid.identityˡ m x)) ⟩
  (e ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ sym (foldl-monoid _⊗_ e m xs (e ⊗ x)) ⟩
  foldl _⊗_ (e ⊗ x) xs
  ∎

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)


infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys allPys = ⟨ [] , allPys ⟩
  to (x ∷ xs) ys (Px ∷ allP) with to xs ys allP
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

Pxs⇒Pxs++ˡ : ∀ { A : Set } → {P : A → Set} → (xs ys : List A) → Any P xs → Any P (xs ++ ys)
Pxs⇒Pxs++ˡ .(_ ∷ _) ys (here x) = here x
Pxs⇒Pxs++ˡ .(_ ∷ _) ys (there p) = there (Pxs⇒Pxs++ˡ _ ys p)

Pxs⇒Pxs++ʳ : ∀ { A : Set } → {P : A → Set} → (xs ys : List A) → Any P ys → Any P (xs ++ ys)
Pxs⇒Pxs++ʳ [] .(_ ∷ _) (here x) = here x
Pxs⇒Pxs++ʳ [] .(_ ∷ _) (there x) = there x
Pxs⇒Pxs++ʳ (x ∷ xs) ys p = there (Pxs⇒Pxs++ʳ xs ys p)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ { A : Set } → {P : A → Set} → (xs ys : List A) →
      Any P (xs ++ ys) → Any P xs ⊎ Any P ys
    to [] .(_ ∷ _) (here Px) = inj₂ (here Px)
    to [] .(_ ∷ _) (there Pxs) = inj₂ (there Pxs)
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there Pxs) with to xs ys Pxs
    ... | inj₁ anyPxs = inj₁ (there anyPxs)
    ... | inj₂ anyPys = inj₂ anyPys

    from : ∀ { A : Set } → {P : A → Set} → (xs ys : List A) →
      Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from xs ys (inj₁ anyPxs) = Pxs⇒Pxs++ˡ xs ys anyPxs
    from xs ys (inj₂ anyPys) = Pxs⇒Pxs++ʳ xs ys anyPys

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to = to xs
    ; from = from xs
    }
    where
      from : ∀ {A : Set} {P : A → Set} (xs : List A) →
        All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
      from (x ∷ xs) (¬Px ∷ all¬P) (here Px) = ¬Px Px
      from (x ∷ xs) (¬Px ∷ all¬P) (there ¬AnyP) = (from xs all¬P) ¬AnyP

      to : ∀ {A : Set} {P : A → Set} (xs : List A) →
        (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
      to [] ¬AnyP = []
      to (x ∷ xs) ¬AnyP = (λ { Px → ¬AnyP (here Px) })
                        ∷ (to xs λ { anyP → ¬AnyP (there anyP) })

open import Data.Empty using (⊥; ⊥-elim)


Any¬⇔¬All : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
Any¬⇔¬All dec xs =
  record
    { to = to dec xs
    ; from = from xs
    }
    where
      to : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs
      to dec [] x with x []
      ... | ()
      to dec (x ∷ xs) ¬AllP with dec x
      ...| yes Px = there (to dec xs λ { allP → ¬AllP (Px ∷ allP) })
      ...| no ¬Px = here ¬Px

      from : {A : Set} {P : A → Set} → (xs : List A) → Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs
      from (x ∷ xs) (here ¬Px) (Px ∷ allP) = ¬Px Px
      from (x ∷ xs) (there any¬P) (Px ∷ allP) = (from xs any¬P) allP

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs ≃ (∀ x → x ∈ xs → P x)
All-∀ { P = P } xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = λ { y →
        extensionality
          (λ { a → extensionality
            (λ { a∈xs → to∘from xs y a a∈xs
            })
          })
      }
    }
    where
      to : ∀ {A : Set} {P : A → Set} (xs : List A) → All P xs → (x : A) → x ∈ xs → P x
      to (y ∷ ys) (Px ∷ allP) x (here x≡y) rewrite x≡y = Px
      to (y ∷ ys) (Px ∷ allP) x (there exists) = to ys allP x exists

      from : ∀ {A : Set} {P : A → Set} (xs : List A) → ((x : A) → x ∈ xs → P x) → All P xs
      from [] x = []
      from (a ∷ as) ∈Pa = (∈Pa a (here refl)) ∷ (from as λ { b b∈ → ∈Pa b (there b∈) })

      from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) →
        (x : All P xs) → from xs (to xs x) ≡ x
      from∘to [] [] = refl
      from∘to (x ∷ xs) (Px ∷ allP) =
        begin
        to (x ∷ xs) (Px ∷ allP) x (here refl) ∷ from xs (λ { b b∈ → to (x ∷ xs) (Px ∷ allP) b (there b∈) })
        ≡⟨ cong (_∷ from xs (λ { b b∈ → to (x ∷ xs) (Px ∷ allP) b (there b∈) })) refl ⟩
        Px ∷ from xs (λ { b b∈ → to (x ∷ xs) (Px ∷ allP) b (there b∈) })
        ≡⟨ cong (Px ∷_) (from∘to xs allP) ⟩
        Px ∷ allP
        ∎

      to∘from
        : ∀ { A : Set } { P : A → Set }
        → (xs : List A)
        → (y : (x : A) → x ∈ xs → P x)
        → (a : A) → (a∈xs : a ∈ xs) → (to xs (from xs y)) a a∈xs ≡ (y a a∈xs)
      to∘from = ?
