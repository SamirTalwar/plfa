module plfa.part1.Naturals where

-- Naturals

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- Addition

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (suc (suc zero)) + suc (suc (suc (suc zero)))
  ≡⟨⟩
    suc (suc zero) + suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    suc zero + suc (suc (suc (suc (suc (suc zero)))))
  ≡⟨⟩
    zero + suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩
    7
  ∎

+-example-refl : 3 + 4 ≡ 7
+-example-refl = refl

-- Multiplication

_*_ : ℕ → ℕ → ℕ
zero * n  = zero
suc m * n = n + (m * n)

*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    suc (suc (suc zero)) * suc (suc (suc (suc zero)))
  ≡⟨⟩
    4 + (suc (suc zero) * suc (suc (suc (suc zero))))
  ≡⟨⟩
    4 + (4 + (suc zero * suc (suc (suc (suc zero)))))
  ≡⟨⟩
    4 + (4 + (4 + (zero * suc (suc (suc (suc zero))))))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

-- Exponentiation

_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ suc n = m * (m ^ n)

^-example : 3 ^ 4 ≡ 81
^-example = refl

-- Monus

_∸_ : ℕ → ℕ → ℕ
m ∸ 0 = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example2 : 3 ∸ 5 ≡ 0
∸-example2 =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- Precedence

infixl 6 _+_
infixl 6 _∸_
infixl 7 _*_
infixl 8 _^_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
