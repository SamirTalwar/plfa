module plfa.part1.Lists where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribˡ-+; *-distribʳ-+; 0∸n≡0)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_; flip)
open import Level using (Level)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

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
