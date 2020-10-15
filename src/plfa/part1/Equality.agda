module plfa.part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A}
    → x ≡ y
    → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
      → x ≡ y
      → y ≡ z
      → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
     → x ≡ y
     → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
      → u ≡ x
      → v ≡ y
      → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
         → f ≡ g
         → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
      → x ≡ y
      → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where
  infix 1  begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3  _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
        → x ≡ y
        → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
         → x ≡ y
         → y ≡ z
         → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
     → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
       → x ≡ y
       → y ≡ z
       → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

postulate
  +-identity : ∀ (n : ℕ) → n + zero ≡ n
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

module Relations where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
        → zero ≤ n

    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        → suc m ≤ suc n

  n≤n : ∀ {n : ℕ}
      → n ≤ n
  n≤n {zero} = z≤n
  n≤n {suc n} = s≤s n≤n

  ≤-trans : ∀ {m n p : ℕ}
          → m ≤ n
          → n ≤ p
          → m ≤ p
  ≤-trans z≤n z≤n = z≤n
  ≤-trans z≤n (s≤s _) = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

  ≡→≤ : ∀ {m n : ℕ}
      → m ≡ n
      → m ≤ n
  ≡→≤ {zero} {zero} refl = z≤n
  ≡→≤ {suc m} {suc m} refl = s≤s (≡→≤ refl)

  module ≤-Reasoning where
    infix  1 ≤begin_
    infixr 2 _≤⟨⟩_ _≤⟨_⟩_
    infix  3 _≤∎

    ≤begin_ : ∀ {m n : ℕ}
            → m ≤ n
            → m ≤ n
    ≤begin m≤n = m≤n

    _≤⟨⟩_ : ∀ (m : ℕ) {n : ℕ}
          → m ≤ n
          → m ≤ n
    m ≤⟨⟩ m≤n = m≤n

    _≤⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
           → m ≤ n
           → n ≤ p
           → m ≤ p
    m ≤⟨ m≤n ⟩ n≤p = ≤-trans m≤n n≤p

    _≤∎ : ∀ (n : ℕ)
        → n ≤ n
    n ≤∎ = n≤n

  open ≤-Reasoning

  +-monoˡ-≤ : ∀ {m n p : ℕ}
            → m ≤ n
            → (m + p) ≤ (n + p)
  +-monoˡ-≤ {m} {n} {zero} m≤n =
    ≤begin
      m + zero
    ≤⟨ ≡→≤ (+-comm m zero) ⟩
      m
    ≤⟨ m≤n ⟩
      n
    ≤⟨ ≡→≤ (+-comm zero n) ⟩
      n + zero
    ≤∎
  +-monoˡ-≤ {m} {n} {suc p} m≤n =
    ≤begin
      m + suc p
    ≤⟨ ≡→≤ (+-suc m p) ⟩
      suc (m + p)
    ≤⟨ s≤s (+-monoˡ-≤ m≤n) ⟩
      suc (n + p)
    ≤⟨ ≡→≤ (sym (+-suc n p)) ⟩
      n + suc p
    ≤∎

  +-monoʳ-≤ : ∀ {n p q : ℕ}
            → p ≤ q
            → (n + p) ≤ (n + q)
  +-monoʳ-≤ {zero} {p} {q} p≤q =
    ≤begin
      zero + p
    ≤⟨⟩
      p
    ≤⟨ p≤q ⟩
      q
    ≤⟨⟩
      zero + q
    ≤∎
  +-monoʳ-≤ {suc n} {p} {q} p≤q =
    ≤begin
      suc n + p
    ≤⟨ ≡→≤ (+-comm (suc n) p) ⟩
      p + suc n
    ≤⟨ ≡→≤ (+-suc p n) ⟩
      suc (p + n)
    ≤⟨ s≤s (+-monoˡ-≤ p≤q) ⟩
      suc (q + n)
    ≤⟨ ≡→≤ (sym (+-suc q n)) ⟩
      q + suc n
    ≤⟨ ≡→≤ (+-comm q (suc n)) ⟩
      suc n + q
    ≤∎

  +-mono-≤ : ∀ {m n p q : ℕ}
          → m ≤ n
          → p ≤ q
          → (m + p) ≤ (n + q)
  +-mono-≤ {m} {n} {p} {q} m≤n p≤q =
    ≤begin
      m + p
    ≤⟨ +-monoˡ-≤ m≤n ⟩
      n + p
    ≤⟨ +-monoʳ-≤ p≤q ⟩
      n + q
    ≤∎

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
           → odd n
           → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
          → even n
          → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
          → even (m + n)
          → even (n + m)
even-comm m n ev rewrite +-comm m n = ev

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl

even-comm′ : ∀ (m n : ℕ)
           → even (m + n)
           → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl
  = ev

even-comm″ : ∀ (m n : ℕ)
           → even (m + n)
           → even (n + m)
even-comm″ m n = subst even (+-comm m n)

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
       → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
        → x ≐ y
        → y ≐ z
        → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
      → x ≐ y
      → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
  Q : A → Set
  Q z = P z → P x
  Qx : Q x
  Qx = refl-≐ P
  Qy : Q y
  Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
            → x ≡ y
            → x ≐ y
≡-implies-≐ x≡y P = subst P x≡y

≐-implies-≡ : ∀ {A : Set} {x y : A}
            → x ≐ y
            → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y (λ z → x ≡ z) refl

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
     → x ≡′ y
     → y ≡′ x
sym′ refl′ = refl′

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
