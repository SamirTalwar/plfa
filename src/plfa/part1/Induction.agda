module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _^_)

--  operators exercise:
--    and (_&&_):
--      has identity: false
--      is associative: (m && n) && p ≡ m && (n && p)
--      is commutative: m && n ≡ n && m
--    or (_||_):
--      has identity: true
--      is associative: (m || n) || p ≡ m || (n || p)
--      is commutative: m || n ≡ n || m
--    `and` distributes over `or`:
--      (m || n) && p ≡ (m && p) || (n && p)
--      m && (p || q) ≡ (m && p) || (m && q)
--    matrix multiplication
--      has identity: I
--      is associative: (m * n) * p ≡ m * (n * p)
--      is not commutative: m * n ≢ n * m

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + 0
  ≡⟨ +-identityʳ m ⟩
    0 + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identityʳ′ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ′ zero = refl
+-identityʳ′ (suc m) rewrite +-identityʳ′ m = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identityʳ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m zero p rewrite +-identityʳ m | +-identityʳ (m * p) = refl
*-distrib-+ m (suc n) p
  rewrite +-suc m n
        | *-distrib-+ m n p
        | sym (+-assoc (m * p) p (n * p))
        | +-assoc (m * p) p (n * p)
        | +-swap (m * p) p (n * p)
  = refl

*-identityˡ : ∀ (n : ℕ) → 1 * n ≡ n
*-identityˡ zero = refl
*-identityˡ (suc n) rewrite *-identityˡ n = refl

*-identityʳ : ∀ (n : ℕ) → n * 1 ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((1 + m) * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + m * n * p
  ≡⟨ cong (_+ m * n * p) (sym (*-identityˡ (n * p))) ⟩
    1 * (n * p) + m * n * p
  ≡⟨ cong (1 * (n * p) +_) (*-assoc m n p) ⟩
    1 * (n * p) + m * (n * p)
  ≡⟨ sym (*-distrib-+ 1 m (n * p)) ⟩
    (1 + m) * (n * p)
  ∎

*-zeroˡ : ∀ (n : ℕ) → 0 * n ≡ 0
*-zeroˡ n = refl

*-zeroʳ : ∀ (n : ℕ) → n * 0 ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-sucˡ : ∀ (m n : ℕ) → suc m * n ≡ n + m * n
*-sucˡ zero n = refl
*-sucˡ (suc m) n = refl

*-sucʳ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-sucʳ zero n = refl
*-sucʳ (suc m) n rewrite *-sucʳ m n | +-swap m n (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zeroʳ m = refl
*-comm m (suc n) rewrite *-sucʳ m n | *-comm m n = refl

∸-zero : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-zero zero = refl
∸-zero (suc n) = refl

+-identityˡ : ∀ (m : ℕ) → zero + m ≡ m
+-identityˡ zero = refl
+-identityˡ (suc m) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p rewrite ∸-zero m | +-identityˡ p = refl
∸-+-assoc zero (suc n) p rewrite ∸-zero (suc n) | ∸-zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-zeroˡ : ∀ (n : ℕ) → 0 ^ suc n ≡ 0
^-zeroˡ zero = refl
^-zeroˡ (suc n) = refl

^-zeroʳ : ∀ (n : ℕ) → n ^ 0 ≡ 1
^-zeroʳ zero = refl
^-zeroʳ (suc n) = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ m ^ n * m ^ p
^-distribˡ-+-* m zero zero = refl
^-distribˡ-+-* m zero (suc p) rewrite +-identityʳ (suc p) | +-identityʳ (m * (m ^ p)) = refl
^-distribˡ-+-* m (suc n) zero rewrite +-identityʳ (suc n) | +-identityʳ n | *-identityʳ (m * (m ^ n)) = refl
^-distribˡ-+-* m (suc n) (suc p) rewrite ^-distribˡ-+-* m n (suc p) | *-assoc m (m ^ n) (m * (m ^ p)) = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p rewrite (sym (*-assoc m n p)) | *-comm m n | *-assoc n m p = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p)
  rewrite ^-distribʳ-* m n p
        | *-assoc m (m ^ p) (n * (n ^ p))
        | cong (m *_) (*-swap (m ^ p) n (n ^ p))
        | *-assoc m n (m ^ p * n ^ p)
  = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite ^-zeroʳ (m ^ n) | *-identityʳ n | *-zeroʳ n | ^-zeroʳ m = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p | sym (^-distribˡ-+-* m n (n * p)) | sym (*-sucʳ n p) = refl

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

to : ℕ → Bin
-- This must be `⟨⟩`, not `⟨⟩ O`, for the laws to hold.
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = from bin * 2
from (bin I) = suc (from bin * 2)

bin-inc-is-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
bin-inc-is-suc ⟨⟩ = refl
bin-inc-is-suc (b O) rewrite bin-inc-is-suc b = refl
bin-inc-is-suc (b I) rewrite bin-inc-is-suc b = refl

bin-O-is-*2 : ∀ (n : ℕ) → to ((suc n) * 2) ≡ (to (suc n)) O
bin-O-is-*2 zero rewrite *-zeroˡ 2 = refl
bin-O-is-*2 (suc n) rewrite bin-O-is-*2 n = refl

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

-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
