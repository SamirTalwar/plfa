module plfa.stretch.Binary where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityˡ; +-identityʳ; +-suc; *-comm; *-suc; *-zero; *-zeroˡ)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import plfa.part1.Isomorphism using (_≲_)

-- Binary

-- Part 1, Chapter 1: Naturals

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = from bin * 2
from (bin I) = suc (from bin * 2)

_ : from (to 0) ≡ 0
_ = refl

_ : from (to 1) ≡ 1
_ = refl

_ : from (to 2) ≡ 2
_ = refl

_ : from (to 3) ≡ 3
_ = refl

_ : from (to 4) ≡ 4
_ = refl

-- Part 1, Chapter 2: Induction

bin-inc-is-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-inc-is-suc ⟨⟩ = refl
bin-inc-is-suc (b O) rewrite bin-inc-is-suc b = refl
bin-inc-is-suc (b I) rewrite bin-inc-is-suc b = refl

-- does not hold:
-- bin-convert-from-to : ∀ (b : Bin) → to (from b) ≡ b
-- counter-examples:
_ : to (from (⟨⟩)) ≡ ⟨⟩ O
_ = refl
_ : to (from (⟨⟩ O I)) ≡ ⟨⟩ I
_ = refl

bin-convert-to-from : ∀ (n : ℕ) → from (to n) ≡ n
bin-convert-to-from zero = refl
bin-convert-to-from (suc n) rewrite bin-inc-is-suc (to n) | bin-convert-to-from n = refl

-- Part 1, Chapter 3: Relations

data One : Bin → Set where
  one : One (⟨⟩ I)
  one-O : {b : Bin}
        → One b
        → One (b O)
  one-I : {b : Bin}
        → One b
        → One (b I)

data Can : Bin → Set where
  zero : Can (⟨⟩ O)
  canonical : {b : Bin}
            → One b
            → Can b

_ : Can (⟨⟩ O)
_ = zero

_ : Can (⟨⟩ I O I I)
_ = canonical (one-I (one-I (one-O one)))

inc-preserves-one : ∀ {b : Bin}
                  → One b
                  → One (inc b)
inc-preserves-one {⟨⟩ I} one = one-O one
inc-preserves-one (one-O o) = one-I o
inc-preserves-one (one-I o) = one-O (inc-preserves-one o)

inc-preserves-can : ∀ {b : Bin}
                  → Can b
                  → Can (inc b)
inc-preserves-can zero = canonical one
inc-preserves-can (canonical o) = canonical (inc-preserves-one o)

to-produces-can : ∀ (n : ℕ)
                → Can (to n)
to-produces-can   zero  = zero
to-produces-can (suc n) = inc-preserves-can (to-produces-can n)

_+ᵇ_ : ∀ (a b : Bin) → Bin
⟨⟩ +ᵇ ⟨⟩ = ⟨⟩
a@(_ O) +ᵇ ⟨⟩ = a
a@(_ I) +ᵇ ⟨⟩ = a
⟨⟩ +ᵇ b@(_ O) = b
⟨⟩ +ᵇ b@(_ I) = b
(a O) +ᵇ (b O) = (a +ᵇ b) O
(a O) +ᵇ (b I) = (a +ᵇ b) I
(a I) +ᵇ (b O) = (a +ᵇ b) I
(a I) +ᵇ (b I) = (inc (a +ᵇ b)) O

infixl 6 _+ᵇ_

_ : ⟨⟩ I I +ᵇ ⟨⟩ I I ≡ ⟨⟩ I I O
_ = refl

data BinZero : Bin → Set where
  zero⁰ : BinZero ⟨⟩
  zero¹ : BinZero (⟨⟩ O)

+ᵇ-comm : ∀ (a b : Bin)
        → a +ᵇ b ≡ b +ᵇ a
+ᵇ-comm ⟨⟩ ⟨⟩ = refl
+ᵇ-comm ⟨⟩ (b O) = refl
+ᵇ-comm ⟨⟩ (b I) = refl
+ᵇ-comm (a O) ⟨⟩ = refl
+ᵇ-comm (a O) (b O) rewrite +ᵇ-comm a b = refl
+ᵇ-comm (a O) (b I) rewrite +ᵇ-comm a b = refl
+ᵇ-comm (a I) ⟨⟩ = refl
+ᵇ-comm (a I) (b O) rewrite +ᵇ-comm a b = refl
+ᵇ-comm (a I) (b I) rewrite +ᵇ-comm a b = refl

+ᵇ-identityˡ : ∀ {a b : Bin} → BinZero a → Can b → a +ᵇ b ≡ b
+ᵇ-identityˡ zero⁰ zero = refl
+ᵇ-identityˡ zero⁰ (canonical one) = refl
+ᵇ-identityˡ zero⁰ (canonical (one-O _)) = refl
+ᵇ-identityˡ zero⁰ (canonical (one-I _)) = refl
+ᵇ-identityˡ zero¹ zero = refl
+ᵇ-identityˡ zero¹ (canonical one) = refl
+ᵇ-identityˡ zero¹ (canonical (one-O o)) rewrite +ᵇ-identityˡ zero⁰ (canonical o) = refl
+ᵇ-identityˡ zero¹ (canonical (one-I o)) rewrite +ᵇ-identityˡ zero⁰ (canonical o) = refl

+ᵇ-identityʳ : ∀ {a b : Bin}
             → Can a
             → BinZero b
             → a +ᵇ b ≡ a
+ᵇ-identityʳ {a} {b} can-a zero-b rewrite +ᵇ-comm a b | +ᵇ-identityˡ zero-b can-a = refl

+ᵇ-inc : ∀ {a b : Bin}
       → Can a
       → Can b
       → a +ᵇ inc b ≡ inc (a +ᵇ b)
+ᵇ-inc {⟨⟩ O} {⟨⟩ O} zero zero = refl
+ᵇ-inc {⟨⟩ O} {b O} zero (canonical _) = refl
+ᵇ-inc {a O} {⟨⟩ O} (canonical _) zero = refl
+ᵇ-inc {a O} {b O} (canonical _) (canonical _) = refl
+ᵇ-inc {⟨⟩ O} {⟨⟩ I} zero (canonical one) = refl
+ᵇ-inc {⟨⟩ O} {(b O) I} zero (canonical (one-I _)) = refl
+ᵇ-inc {⟨⟩ O} {(b I) I} zero (canonical (one-I _)) = refl
+ᵇ-inc {(a O) O} {⟨⟩ I} (canonical (one-O (one-O one-a))) (canonical one)
  rewrite +ᵇ-identityʳ (canonical one-a) zero⁰
  = refl
+ᵇ-inc {(.⟨⟩ I) O} {⟨⟩ I} (canonical (one-O one)) (canonical one) = refl
+ᵇ-inc {(a I) O} {⟨⟩ I} (canonical (one-O (one-I one-a))) (canonical one)
  rewrite +ᵇ-identityʳ (canonical one-a) zero⁰
  = refl
+ᵇ-inc {a O} {b I} (canonical (one-O one-a)) (canonical (one-I one-b))
  rewrite +ᵇ-inc (canonical one-a) (canonical one-b)
  = refl
+ᵇ-inc {a I} {⟨⟩ O} (canonical _) zero = refl
+ᵇ-inc {a I} {b O} (canonical _) (canonical _) = refl
+ᵇ-inc {⟨⟩ I} {⟨⟩ I} (canonical one) (canonical one) = refl
+ᵇ-inc {⟨⟩ I} {b I} (canonical one) (canonical (one-I one-b))
  rewrite +ᵇ-identityˡ zero⁰ (inc-preserves-can (canonical one-b))
        | +ᵇ-identityˡ zero⁰ (canonical one-b)
  = refl
+ᵇ-inc {a I} {⟨⟩ I} (canonical (one-I one-a)) (canonical one)
  rewrite +ᵇ-inc (canonical one-a) zero
        | +ᵇ-identityʳ (canonical one-a) zero⁰
        | +ᵇ-identityʳ (canonical one-a) zero¹
  = refl
+ᵇ-inc {a I} {b I} (canonical (one-I one-a)) (canonical (one-I one-b)) =
  begin
    a I +ᵇ inc (b I)
  ≡⟨⟩
    a I +ᵇ inc b O
  ≡⟨⟩
    a I +ᵇ inc b O
  ≡⟨ cong _I (+ᵇ-inc (canonical one-a) (canonical one-b)) ⟩
    inc (a I +ᵇ b I)
  ∎

+≡+ᵇ : ∀ (m n : ℕ)
     → to (m + n) ≡ to m +ᵇ to n
+≡+ᵇ zero zero = refl
+≡+ᵇ zero (suc n) =
  begin
    to (zero + suc n)
  ≡⟨ cong to (+-identityˡ (suc n)) ⟩
    to (suc n)
  ≡⟨ sym (+ᵇ-identityˡ zero¹ (to-produces-can (suc n))) ⟩
    to zero +ᵇ to (suc n)
  ∎
+≡+ᵇ (suc m) zero =
  begin
    to (suc m + zero)
  ≡⟨ cong to (+-identityʳ (suc m)) ⟩
    to (suc m)
  ≡⟨ sym (+ᵇ-identityʳ (to-produces-can (suc m)) zero¹) ⟩
    to (suc m) +ᵇ to zero
  ∎
+≡+ᵇ (suc m) (suc n) =
  begin
    to (suc m + suc n)
  ≡⟨ cong to (+-suc (suc m) n) ⟩
    inc (to (suc m + n))
  ≡⟨ cong (inc ∘ to) (+-comm (suc m) n) ⟩
    inc (to (n + suc m))
  ≡⟨ cong (inc ∘ to) (+-suc n m) ⟩
    inc (inc (to (n + m)))
  ≡⟨ cong (inc ∘ inc) (+≡+ᵇ n m) ⟩
    inc (inc (to n +ᵇ to m))
  ≡⟨ cong inc (sym (+ᵇ-inc (to-produces-can n) (to-produces-can m))) ⟩
    inc (to n +ᵇ inc (to m))
  ≡⟨ cong inc (+ᵇ-comm (to n) (inc (to m))) ⟩
    inc (inc (to m) +ᵇ to n)
  ≡⟨ sym (+ᵇ-inc (inc-preserves-can (to-produces-can m)) (to-produces-can n)) ⟩
    inc (to m) +ᵇ inc (to n)
  ≡⟨⟩
    to (suc m) +ᵇ to (suc n)
  ∎

x+ᵇx≡xO : ∀ {b : Bin}
        → One b
        → b +ᵇ b ≡ b O
x+ᵇx≡xO one = refl
x+ᵇx≡xO (one-O o) rewrite x+ᵇx≡xO o = refl
x+ᵇx≡xO (one-I o) rewrite x+ᵇx≡xO o = refl

can-identity : ∀ {b : Bin}
             → Can b
             → to (from b) ≡ b
can-identity zero = refl
can-identity (canonical one) = refl
can-identity (canonical (one-O {b} o)) =
  begin
    to (from (b O))
  ≡⟨⟩
    to (from b * 2)
  ≡⟨ cong to (*-comm (from b) 2) ⟩
    to (from b + (from b + zero))
  ≡⟨ cong to (cong (from b +_) (+-identityʳ (from b))) ⟩
    to (from b + from b)
  ≡⟨ +≡+ᵇ (from b) (from b) ⟩
    to (from b) +ᵇ to (from b)
  ≡⟨ cong (_+ᵇ to (from b)) (can-identity (canonical o)) ⟩
    b +ᵇ to (from b)
  ≡⟨ cong (b +ᵇ_) (can-identity (canonical o)) ⟩
    b +ᵇ b
  ≡⟨ x+ᵇx≡xO o ⟩
    b O
  ∎
can-identity (canonical (one-I {b} o)) =
  begin
    to (from (b I))
  ≡⟨⟩
    inc (to (from b * 2))
  ≡⟨ cong (inc ∘ to) (*-comm (from b) 2) ⟩
    inc (to (from b + (from b + zero)))
  ≡⟨ cong (inc ∘ to) (cong (from b +_) (+-identityʳ (from b))) ⟩
    inc (to (from b + from b))
  ≡⟨ cong inc (+≡+ᵇ (from b) (from b)) ⟩
    inc (to (from b) +ᵇ to (from b))
  ≡⟨ cong (inc ∘ (_+ᵇ to (from b))) (can-identity (canonical o)) ⟩
    inc (b +ᵇ to (from b))
  ≡⟨ cong (inc ∘ (b +ᵇ_)) (can-identity (canonical o)) ⟩
    inc (b +ᵇ b)
  ≡⟨ cong inc (x+ᵇx≡xO o) ⟩
    inc (b O)
  ≡⟨⟩
    b I
  ∎

-- Part 1, Chapter 5: Isomorphism

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to = to
    ; from = from
    ; from∘to = bin-convert-to-from
    -- `to∘from` cannot be defined because binary numbers can have leading zeroes.
    -- e.g. `to (from (⟨⟩ O I)) = ⟨⟩ I`
    }
