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
foldr-++ = ?

foldr-∷ : ∀ { A : Set } → (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ = ?

map-is-foldr
  : ∀ { A B : Set }
  → (f : A → B)
  → (ys : List A)
  → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr = ?

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree = ?

map-Tree-is-fold-Tree
  : ∀ { A B C D : Set }
  → (f : A → C)
  → (g : B → D)
  → (tree : Tree A B)
  → map-Tree f g tree ≡ fold-Tree (λ a → leaf (f a)) (λ t₁ b t₂ → node t₁ (g b) t₂) tree
map-Tree-is-fold-Tree = ?

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


