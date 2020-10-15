module plfa.part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
                 → (∀ (x : A) → f x ≡ g x)
                 → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
                   → (∀ (x : A) → f x ≡ g x)
                   → f ≡ g

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to   = λ x → x
    ; from = λ y → y
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

≃-sym : ∀ {A B : Set}
      → A ≃ B
      → B ≃ A
≃-sym A≃B =
  record
    { to   = from A≃B
    ; from = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set}
        → A ≃ B
        → B ≃ C
        → A ≃ C
≃-trans A≃B B≃C =
  record
    { to   = to B≃C ∘ to A≃B
    ; from = from A≃B ∘ from B≃C
    ; from∘to = λ x →
        begin
          ((from A≃B ∘ from B≃C) ∘ (to B≃C ∘ to A≃B)) x
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎
    ; to∘from = λ y →
        begin
          ((to B≃C ∘ to A≃B) ∘ (from A≃B ∘ from B≃C)) y
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎
    }

module ≃-Reasoning where
  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
           → A ≃ B
           → A ≃ B
  ≃-begin_ A≃B = A≃B

  _≃⟨_⟩_ : ∀ A {B C : Set}
         → A ≃ B
         → B ≃ C
         → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
       → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to   = λ x → x
    ; from = λ y → y
    ; from∘to = λ x → refl
    }

≲-trans : ∀ {A B C : Set}
        → A ≲ B
        → B ≲ C
        → A ≲ C
≲-trans A≲B B≲C =
  record
    { to   = to B≲C ∘ to A≲B
    ; from = from A≲B ∘ from B≲C
    ; from∘to = λ x →
      begin
        ((from A≲B ∘ from B≲C) ∘ (to B≲C ∘ to A≲B)) x
      ≡⟨⟩
        from A≲B (from B≲C (to B≲C (to A≲B x)))
      ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
        from A≲B (to A≲B x)
      ≡⟨ from∘to A≲B x ⟩
        x
      ∎
    }

≲-antisym : ∀ {A B : Set}
          → (A≲B : A ≲ B)
          → (B≲A : B ≲ A)
          → (to A≲B) ≡ (from B≲A)
          → (from A≲B) ≡ (to B≲A)
          → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to   = to A≲B
    ; from = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ y →
        begin
          (to A≲B ∘ from A≲B) y
        ≡⟨⟩
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎
    }
module ≲-Reasoning where
  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
           → A ≲ B
           → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ A {B C : Set}
         → A ≲ B
         → B ≲ C
         → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
       → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

≃-implies-≲ : ∀ {A B : Set}
            → A ≃ B
            → A ≲ B
≃-implies-≲ A≃B =
  record
    { to   = to A≃B
    ; from = from A≃B
    ; from∘to = from∘to A≃B
    }

infix 0 _⇔_
record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set}
       → A ⇔ A
⇔-refl =
  record
    { to   = λ x → x
    ; from = λ y → y
    }
⇔-sym : ∀ {A B : Set}
      → A ⇔ B
      → B ⇔ A
⇔-sym A⇔B =
  record
    { to   = from A⇔B
    ; from = to A⇔B
    }

⇔-trans : ∀ {A B C : Set}
        → A ⇔ B
        → B ⇔ C
        → A ⇔ C
⇔-trans A⇔B B⇔C =
  record
  { to   = to B⇔C ∘ to A⇔B
  ; from = from A⇔B ∘ from B⇔C
  }

module Binary where
  open import Data.Nat using (_*_)

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  inc : Bin → Bin
  inc ⟨⟩ = ⟨⟩ I
  inc (n O) = n I
  inc (n I) = inc n O

  to-bin : ℕ → Bin
  to-bin zero = ⟨⟩ O
  to-bin (suc n) = inc (to-bin n)

  from-bin : Bin → ℕ
  from-bin ⟨⟩ = 0
  from-bin (bin O) = from-bin bin * 2
  from-bin (bin I) = suc (from-bin bin * 2)

  bin-inc-is-suc : ∀ (b : Bin) → from-bin (inc b) ≡ suc (from-bin b)
  bin-inc-is-suc ⟨⟩ = refl
  bin-inc-is-suc (b O) rewrite bin-inc-is-suc b = refl
  bin-inc-is-suc (b I) rewrite bin-inc-is-suc b = refl

  bin-convert-to-from : ∀ (n : ℕ) → from-bin (to-bin n) ≡ n
  bin-convert-to-from zero = refl
  bin-convert-to-from (suc n) rewrite bin-inc-is-suc (to-bin n) | bin-convert-to-from n = refl

  ℕ≲Bin : ℕ ≲ Bin
  ℕ≲Bin =
    record
      { to = to-bin
      ; from = from-bin
      ; from∘to = bin-convert-to-from
      -- `to∘from` cannot be defined because binary numbers can have leading zeroes.
      -- e.g. `to (from (⟨⟩ O I)) = ⟨⟩ I`
      }

-- import Function using (_∘_)
-- import Function.Inverse using (_↔_)
-- import Function.LeftInverse using (_↞_)
