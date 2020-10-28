module plfa.part1.Lists where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribˡ-+; *-distribʳ-+; 0∸n≡0)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; flip)
open import Level using (Level)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)
open import plfa.part1.Quantifiers using (∀extensionality)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

data List′ : Set → Set where
  []′ : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc      []  ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A)
             → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A)
             → xs ++ [] ≡ xs
++-identityʳ       [] = refl
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- Length

length : ∀ {A : Set} → List A → ℕ
length       [] = 0
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A)
          → length (xs ++ ys) ≡ length xs + length ys
length-++          []  ys = refl
length-++ {A} (x ∷ xs) ys =
  begin
    length (x ∷ xs ++ ys)
  ≡⟨⟩
    length (x ∷ (xs ++ ys))
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    suc (length xs) + length ys
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse      []  = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
                   → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] [] = refl
reverse-++-distrib [] (y ∷ ys) rewrite ++-identityʳ (reverse ys ++ [ y ]) = refl
reverse-++-distrib (x ∷ xs) ys =
  begin
    reverse (x ∷ xs ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set} (xs : List A)
                   → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse ([ x ]) ++ reverse (reverse xs)
  ≡⟨⟩
    x ∷ reverse (reverse xs)
  ≡⟨ cong (x ∷_) (reverse-involutive xs) ⟩
    x ∷ xs
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt      []  ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
              → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse      []  ys = refl
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ x ∷ ys
  ≡⟨⟩
    reverse xs ++ [ x ] ++ ys
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set } (xs : List A)
         → reverse′ xs ≡ reverse xs
reverses      []  = refl
reverses (x ∷ xs) =
  begin
    reverse′ (x ∷ xs)
  ≡⟨⟩
    shunt (x ∷ xs) []
  ≡⟨⟩
    shunt xs [ x ]
  ≡⟨ shunt-reverse xs [ x ] ⟩
    reverse xs ++ [ x ]
  ≡⟨⟩
    reverse (x ∷ xs)
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f      []  = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

map-compose : ∀ {A B C : Set} (g : B → C) (f : A → B)
            → map (g ∘ f) ≡ map g ∘ map f
map-compose g f = extensionality (map-compose-xs g f)
  where
  map-compose-xs : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : List A)
                → map (g ∘ f) xs ≡ (map g ∘ map f) xs
  map-compose-xs g f      []  = refl
  map-compose-xs g f (x ∷ xs) =
     begin
       map (g ∘ f) (x ∷ xs)
     ≡⟨⟩
       map (λ z → g (f z)) (x ∷ xs)
     ≡⟨⟩
       g (f x) ∷ map (λ z → g (f z)) xs
     ≡⟨ cong (g (f x) ∷_) (map-compose-xs g f xs) ⟩
       g (f x) ∷ map g (map f xs)
     ≡⟨⟩
       map g (map f (x ∷ xs))
     ≡⟨⟩
       (map g ∘ map f) (x ∷ xs)
     ∎

map-++-distribute : ∀ {A B} (f : A → B) (xs ys : List A)
                  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f      []  ys = refl
map-++-distribute f (x ∷ xs) ys =
  begin
    map f (x ∷ xs ++ ys)
  ≡⟨⟩
    f x ∷ map f (xs ++ ys)
  ≡⟨ cong (f x ∷_) (map-++-distribute f xs ys) ⟩
    map f (x ∷ xs) ++ map f ys
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f-leaf f-node            (leaf value) = leaf (f-leaf value)
map-Tree f-leaf f-node (node left value right) = node (map-Tree f-leaf f-node left) (f-node value) (map-Tree f-leaf f-node right)

_ : map-Tree (_+ 1) (_* 2) (node (node (leaf 7) 3 (node (leaf 2) 4 (leaf 6))) 1 (leaf 5))
    ≡ node (node (leaf 8) 6 (node (leaf 3) 8 (leaf 7))) 2 (leaf 6)
_ = refl

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e      []  = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

_ : product [ 5 , 4 , 3 , 2 ] ≡ 120
_ = refl

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
         → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

foldr-∷ : ∀ {A : Set} (xs : List A)
        → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite foldr-∷ xs = refl

++-foldr : ∀ {A : Set} (xs ys : List A)
         → xs ++ ys ≡ foldr _∷_ ys xs
++-foldr xs ys rewrite sym (foldr-∷ (xs ++ ys)) | foldr-++ _∷_ [] xs ys | foldr-∷ ys = refl

map-is-foldr : ∀ {A B : Set} (f : A → B)
             → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr-xs f)
  where
  map-is-foldr-xs : ∀ {A B : Set} (f : A → B) (xs : List A)
               → map f xs ≡ foldr (λ y ys → f y ∷ ys) [] xs
  map-is-foldr-xs f [] = refl
  map-is-foldr-xs f (x ∷ xs) rewrite map-is-foldr-xs f xs = refl

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f-leaf f-node            (leaf value) = f-leaf value
fold-Tree f-leaf f-node (node left value right) = f-node (fold-Tree f-leaf f-node left) value (fold-Tree f-leaf f-node right)

_ : fold-Tree (_* 2) (λ l v r → l + v + r) (node (node (leaf 7) 3 (node (leaf 2) 4 (leaf 6))) 1 (leaf 5))
    ≡ 14 + 3 + 4 + 4 + 12 + 1 + 10 -- 48
_ = refl

map-is-fold-Tree : ∀ {A B C D : Set} (f-leaf : A → C) (f-node : B → D)
                 → map-Tree f-leaf f-node ≡ fold-Tree (leaf ∘ f-leaf) (λ l v r → node l (f-node v) r)
map-is-fold-Tree f-leaf f-node = extensionality (map-is-fold-Tree-tree f-leaf f-node)
  where
  map-is-fold-Tree-tree : ∀ {A B C D : Set} (f-leaf : A → C) (f-node : B → D) (tree : Tree A B)
                        → map-Tree f-leaf f-node tree ≡ fold-Tree (leaf ∘ f-leaf) (λ l v r → node l (f-node v) r) tree
  map-is-fold-Tree-tree f-leaf f-node            (leaf value) = refl
  map-is-fold-Tree-tree f-leaf f-node (node left value right) =
    begin
      map-Tree f-leaf f-node (node left value right)
    ≡⟨⟩
      node (map-Tree f-leaf f-node left) (f-node value) (map-Tree f-leaf f-node right)
    ≡⟨ cong₂ (λ l r → node l (f-node value) r) (map-is-fold-Tree-tree f-leaf f-node left) (map-is-fold-Tree-tree f-leaf f-node right) ⟩
      node
        (fold-Tree (leaf ∘ f-leaf) (λ l v r → node l (f-node v) r) left)
        (f-node value)
        (fold-Tree (leaf ∘ f-leaf) (λ l v r → node l (f-node v) r) right)
    ≡⟨⟩
      fold-Tree (leaf ∘ f-leaf) (λ l v r → node l (f-node v) r) (node left value right)
    ∎

downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

sum-downFrom : ∀ (n : ℕ)
             → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero          = refl
sum-downFrom (suc zero)    = refl
sum-downFrom (suc (suc n)) =
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    sum (suc n ∷ downFrom (suc n)) * 2
  ≡⟨⟩
    (suc n + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ 2 (suc n) (sum (downFrom (suc n))) ⟩
    suc n * 2 + sum (downFrom (suc n)) * 2
  ≡⟨ cong (suc n * 2 +_) (sum-downFrom (suc n)) ⟩
    suc n * 2 + suc n * (suc n ∸ 1)
  ≡⟨ sym (*-distribˡ-+ (suc n) 2 (suc n ∸ 1)) ⟩
    suc n * (2 + (suc n ∸ 1))
  ≡⟨⟩
    suc n * (1 + suc n)
  ≡⟨ *-distribˡ-+ (suc n) 1 (suc n) ⟩
    suc n * 1 + suc n * suc n
  ≡⟨ cong (_+ suc n * suc n) (*-identityʳ (suc n)) ⟩
    suc n + suc n * suc n
  ≡⟨⟩
    suc (suc n) * suc n
  ≡⟨⟩
    suc (suc n) * (suc (suc n) ∸ 1)
  ∎

-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

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

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
             → IsMonoid _⊗_ e
             → ∀ (xs : List A) (y : A)
             → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    e ⊗ y
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ foldr _⊗_ y xs
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

_ : foldl (λ xs x → x ∷ xs) [] [ 1 , 2 , 3 ] ≡ [ 3 , 2 , 1 ]
_ = refl

foldr-monoid-foldl-example : foldr _++_ ([] {ℕ}) [ [ 1 ] , [ 2 , 3 ] , [ 4 , 5 , 6 ] ]
                           ≡ foldl _++_ ([] {ℕ}) [ [ 1 ] , [ 2 , 3 ] , [ 4 , 5 , 6 ] ]
foldr-monoid-foldl-example = refl

foldl-++ : ∀ {A B : Set} (_⊗_ : B → A → B) (e : B) (xs ys : List A)
         → foldl _⊗_ e (xs ++ ys) ≡ foldl _⊗_ (foldl _⊗_ e xs) ys
foldl-++ _⊗_ e      []  ys = refl
foldl-++ _⊗_ e (x ∷ xs) ys rewrite foldl-++ _⊗_ (e ⊗ x) xs ys = refl

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
             → IsMonoid _⊗_ e
             → ∀ (xs : List A) (y : A)
             → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldl _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityʳ ⊗-monoid y) ⟩
    y ⊗ e
  ≡⟨⟩
    y ⊗ foldl _⊗_ e []
  ∎
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ foldl _⊗_ e xs
  ≡⟨ assoc ⊗-monoid y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
    y ⊗ foldl _⊗_ x xs
  ≡⟨ cong (λ z → y ⊗ foldl _⊗_ z xs) (sym (identityˡ ⊗-monoid x)) ⟩
    y ⊗ foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    y ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
                   → IsMonoid _⊗_ e
                   → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (foldr-monoid-foldl-xs _⊗_ e ⊗-monoid)
  where
  foldr-monoid-foldl-xs : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
                        → IsMonoid _⊗_ e
                        → (xs : List A)
                        → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
  foldr-monoid-foldl-xs _⊗_ e ⊗-monoid [] = refl
  foldr-monoid-foldl-xs _⊗_ e ⊗-monoid (x ∷ xs) =
    begin
      foldr _⊗_ e (x ∷ xs)
    ≡⟨⟩
      x ⊗ foldr _⊗_ e xs
    ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-xs _⊗_ e ⊗-monoid xs) ⟩
      x ⊗ foldl _⊗_ e xs
    ≡⟨ sym (foldl-monoid _⊗_ e ⊗-monoid xs x) ⟩
      foldl _⊗_ x xs
    ≡⟨ cong (λ z → foldl _⊗_ z xs) (sym (identityˡ ⊗-monoid x)) ⟩
      foldl _⊗_ (e ⊗ x) xs
    ≡⟨⟩
      foldl _⊗_ e (x ∷ xs)
    ∎

-- All and Any

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} →     P x  → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

example-not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
example-not-in (there (there (there (here ()))))
example-not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
         → All P (xs ++ ys) ⇔ All P xs × All P ys
All-++-⇔ xs ys =
  record
    { to   = to   xs ys
    ; from = from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
     → All P (xs ++ ys)
     → All P xs × All P ys
  to      []  ys all = ⟨ [] , all ⟩
  to (x ∷ xs) ys (all-x ∷ all-xs++all-ys)
    with to xs ys all-xs++all-ys
  ...  | ⟨ all-xs , all-ys ⟩ = ⟨ all-x ∷ all-xs , all-ys ⟩

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
       → All P xs × All P ys
       → All P (xs ++ ys)
  from      []  ys ⟨         all-xs , all-ys ⟩ = all-ys
  from (x ∷ xs) ys ⟨ all-x ∷ all-xs , all-ys ⟩ = all-x ∷ from xs ys ⟨ all-xs , all-ys ⟩

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
         → Any P (xs ++ ys) ⇔ Any P xs ⊎ Any P ys
Any-++-⇔ xs ys =
  record
    { to   = to   xs ys
    ; from = from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A)
     → Any P (xs ++ ys)
     → Any P xs ⊎ Any P ys
  to [] ys any = inj₂ any
  to (x ∷ xs) ys (here any-x) = inj₁ (here any-x)
  to (x ∷ xs) ys (there any-xs++ys)
    with to xs ys any-xs++ys
  ...  | inj₁ any-xs = inj₁ (there any-xs)
  ...  | inj₂ any-ys = inj₂ any-ys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A)
       → Any P xs ⊎ Any P ys
       → Any P (xs ++ ys)
  from [] ys (inj₂ y) = y
  from (x ∷ xs) ys (inj₁ (here any-x)) = here any-x
  from (x ∷ xs) ys (inj₁ (there any-xs)) = there (from xs ys (inj₁ any-xs))
  from (x ∷ xs) ys (inj₂ any-ys) = there (from xs ys (inj₂ any-ys))

∈-++ : ∀ {A : Set} (z : A) (xs ys : List A)
     → z ∈ (xs ++ ys) ⇔ z ∈ xs ⊎ z ∈ ys
∈-++ {A} z = Any-++-⇔ {A} {z ≡_}

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A)
         → All P (xs ++ ys) ≃ All P xs × All P ys
All-++-≃ xs ys =
  record
    { to   = _⇔_.to (All-++-⇔ xs ys)
    ; from = _⇔_.from (All-++-⇔ xs ys)
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (all : All P (xs ++ ys))
          → _⇔_.from (All-++-⇔ xs ys) (_⇔_.to (All-++-⇔ xs ys) all) ≡ all
  from∘to [] ys all = refl
  from∘to (x ∷ xs) ys (all-x ∷ all-xs++ys) =
    begin
      _⇔_.from (All-++-⇔ (x ∷ xs) ys) (_⇔_.to (All-++-⇔ (x ∷ xs) ys) (all-x ∷ all-xs++ys))
    ≡⟨⟩
      all-x ∷ _⇔_.from (All-++-⇔ xs ys) (_⇔_.to (All-++-⇔ xs ys) all-xs++ys)
    ≡⟨ cong (all-x ∷_) (from∘to xs ys all-xs++ys) ⟩
      (all-x ∷ all-xs++ys)
    ∎

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (all : All P xs × All P ys)
          → _⇔_.to (All-++-⇔ xs ys) (_⇔_.from (All-++-⇔ xs ys) all) ≡ all
  to∘from [] ys ⟨ [] , all-ys ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ all-x ∷ all-xs , all-ys ⟩ =
    begin
      _⇔_.to (All-++-⇔ (x ∷ xs) ys) (_⇔_.from (All-++-⇔ (x ∷ xs) ys) ⟨ all-x ∷ all-xs , all-ys ⟩)
    ≡⟨⟩
      _⇔_.to (All-++-⇔ (x ∷ xs) ys) (all-x ∷ _⇔_.from (All-++-⇔ xs ys) ⟨ all-xs , all-ys ⟩)
    ≡⟨⟩
      let all-xs++ys = _⇔_.from (All-++-⇔ xs ys) ⟨ all-xs , all-ys ⟩
          ⟨ all-xs₂ , all-ys₂ ⟩ = _⇔_.to (All-++-⇔ xs ys) all-xs++ys
      in ⟨ all-x ∷ all-xs₂ , all-ys₂ ⟩
    ≡⟨ cong (λ{ ⟨ x , y ⟩ → ⟨ all-x ∷ x , y ⟩ }) (to∘from xs ys ⟨ all-xs , all-ys ⟩) ⟩
      ⟨ all-x ∷ all-xs , all-ys ⟩
    ∎

¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
          → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to   = to xs
    ; from = from xs
    }
    where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
       → (¬_ ∘ Any P) xs
       → All (¬_ ∘ P) xs
    to [] _ = []
    to (_ ∷ xs) ¬[any[P,x∷xs]] = (¬[any[P,x∷xs]] ∘ here) ∷ to xs (¬[any[P,x∷xs]] ∘ there)

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
         → All (¬_ ∘ P) xs
         → (¬_ ∘ Any P) xs
    from [] _ = λ ()
    from (x ∷ xs) (¬Px ∷          _) (here Px) = ¬Px Px
    from (x ∷ xs) (¬Px ∷ all[¬P,xs]) (there any[P,xs]) = from xs all[¬P,xs] any[P,xs]

-- ¬All⇔Any¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
--           → (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
-- ¬All⇔Any¬ xs =
--   record
--     { to = to xs
--     ; from = from xs
--     }
--     where
--     to : ∀ {A : Set} {P : A → Set} (xs : List A)
--        → (¬_ ∘ All P) xs
--        → Any (¬_ ∘ P) xs
--     to [] ¬all[P,xs] = ⊥-elim (¬all[P,xs] [])
--     -- We cannot implement this without knowing more about the input.
--     to (x ∷ xs) ¬all[P,x∷xs] = {!!}

--     from : ∀ {A : Set} {P : A → Set} (xs : List A)
--          → Any (¬_ ∘ P) xs
--          → (¬_ ∘ All P) xs
--     from (x ∷  _)         (here ¬Px) (Px ∷         _) = ¬Px Px
--     from (_ ∷ xs) (there any[¬P,xs]) ( _ ∷ all[P,xs]) = from xs any[¬P,xs] all[P,xs]

postulate
  ∀∀extensionality : ∀ {A : Set} {B C : A → Set} {f g : ∀ {x : A} → B x → C x}
                   → (∀ {x : A} → (y : B x) → f y ≡ g y)
                   → (λ {x : A} (y : B x) → f y) ≡ (λ {x : A} (y : B x) → g y)

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All P xs ≃ (∀ {z} → z ∈ xs → P z)
All-∀ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = λ z∈xs→Pz → ∀∀extensionality (to∘from xs z∈xs→Pz)
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A)
     → All P xs
     → (∀ {z} → z ∈ xs → P z)
  to [] [] ()
  to (_ ∷  _) (Px ∷ all[P,xs])  (here refl) = Px
  to (x ∷ xs) (Px ∷ all[P,xs]) (there z∈xs) = to xs all[P,xs] z∈xs

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
       → (∀ {z} → z ∈ xs → P z)
       → All P xs
  from [] _ = []
  from (x ∷ xs) z∈xs→Pz = z∈xs→Pz (here refl) ∷ from xs (z∈xs→Pz ∘ there)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (all[P,xs] : All P xs)
          → from xs (to xs all[P,xs]) ≡ all[P,xs]
  from∘to [] [] = refl
  from∘to (x ∷ xs) (Px ∷ all[P,xs]) =
    begin
      from (x ∷ xs) (to (x ∷ xs) (Px ∷ all[P,xs]))
    ≡⟨⟩
      Px ∷ from xs (to xs all[P,xs])
    ≡⟨ cong (Px ∷_) (from∘to xs all[P,xs]) ⟩
      Px ∷ all[P,xs]
    ∎

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (z∈xs→Pz : ∀ {z} → z ∈ xs → P z)
          → ∀ {z : A}
          → (z∈xs : z ∈ xs)
          → to xs (from xs z∈xs→Pz) z∈xs ≡ z∈xs→Pz z∈xs
  to∘from [] _ ()
  to∘from (x ∷ xs) z∈x∷xs→Pz (here refl) = refl
  to∘from (x ∷ xs) z∈x∷xs→Pz (there z∈xs) = to∘from xs (z∈x∷xs→Pz ∘ there) z∈xs

Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
      → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A)
     → Any P xs
     → ∃[ x ] (x ∈ xs × P x)
  to (x ∷ xs)         (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
  to (x ∷ xs) (there any[P,xs]) =
    let ⟨ ∃x , ⟨ x∈xs , Px ⟩ ⟩ = to xs any[P,xs]
     in ⟨ ∃x , ⟨ there x∈xs , Px ⟩ ⟩

  from : ∀ {A : Set} {P : A → Set} (xs : List A)
       → ∃[ x ] (x ∈ xs × P x)
       → Any P xs
  from (x ∷ xs) ⟨  x , ⟨  here refl , Px ⟩ ⟩ = here Px
  from (x ∷ xs) ⟨ ∃x , ⟨ there x∈xs , Px ⟩ ⟩ = there (from xs ⟨ ∃x , ⟨ x∈xs , Px ⟩ ⟩)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A)
          → (any[P,xs] : Any P xs)
          → from xs (to xs any[P,xs]) ≡ any[P,xs]
  from∘to (x ∷ xs)         (here Px) = refl
  from∘to (x ∷ xs) (there any[P,xs]) =
    begin
      from (x ∷ xs) (to (x ∷ xs) (there any[P,xs]))
    ≡⟨⟩
      there (from xs (to xs any[P,xs]))
    ≡⟨ cong there (from∘to xs any[P,xs]) ⟩
      (there any[P,xs])
    ∎

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A)
          → (∃x[x∃xs,Px] : ∃[ x ] (x ∈ xs × P x))
          → to xs (from xs ∃x[x∃xs,Px]) ≡ ∃x[x∃xs,Px]
  to∘from (x ∷ xs) ⟨  x , ⟨ here           refl , Px ⟩ ⟩ = refl
  to∘from (x ∷ xs) ⟨ ∃x , ⟨ there x∈xs , Px ⟩ ⟩ =
    cong (λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ a , ⟨ there b , c ⟩ ⟩ }) (to∘from xs ⟨ ∃x , ⟨ x∈xs , Px ⟩ ⟩)

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P = ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? [] = yes []
All? P? (x ∷ xs) with   P? x | All? P? xs
...                 | yes Px |    yes Pxs = yes (Px ∷ Pxs)
...                 | no ¬Px |          _ = no λ{ (Px ∷ _) → ¬Px Px }
...                 | yes  _ |    no ¬Pxs = no λ{ (_ ∷ Pxs) → ¬Pxs Pxs }

any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p = foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with   P? x | Any? P? xs
...                 | yes Px |          _ = yes (here Px)
...                 | no ¬Px |    yes Pxs = yes (there Pxs)
...                 | no ¬Px |    no ¬Pxs = no (λ { (here Px) → ¬Px Px ; (there Pxs) → ¬Pxs Pxs })
