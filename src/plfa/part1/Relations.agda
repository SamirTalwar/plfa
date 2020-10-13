module plfa.part1.Relations where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-identityʳ; *-comm; *-suc; *-zero; *-zeroˡ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      → zero ≤ n

  s≤s : ∀ {m n : ℕ}
      → m ≤ n
      → suc m ≤ suc n

+-identityʳ′ : ∀ {m n : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
        → suc m ≤ suc n
        → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
        → m ≤ zero
        → m ≡ zero
inv-z≤n z≤n = refl

-- In a directed graph, where x ≤ y if there is a path from x to y,
--   `≤` is a preorder if there are cycles, and a partial order if not.
-- The subset operator `⊆` is a partial order, but not a total order.

≤-refl : ∀ {n : ℕ}
       → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
        → m ≤ n
        → n ≤ p
        → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
          → m ≤ n
          → n ≤ m
          → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
-- We can omit the cases where one argument is `z≤n` and the other is `s≤s`
-- because in the first case, `0 ≤ n` implies `n ≤ 0`, which must be `0 ≤ 0`,
-- which is then covered by the first case. And similarly for the second case.

data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
    → Total m n

  flipped :
      n ≤ m
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
         → p ≤ q
         → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
         → m ≤ n
         → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
         → m ≤ n
         → p ≤ q
         → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-monoʳ-≤ : ∀ (n p q : ℕ)
         → p ≤ q
         → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q rewrite *-comm (suc n) p | *-suc p n | *-comm p n =
  +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
         → m ≤ n
         → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
         → m ≤ n
         → p ≤ q
         → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      → zero < suc n

  s<s : ∀ {m n : ℕ}
      → m < n
      → suc m < suc n

<-trans : ∀ {m n p : ℕ}
        → m < n
        → n < p
        → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy (m n : ℕ) : Set where
  less-than :
      m < n
    → Trichotomy m n
  equal :
      m ≡ n
    → Trichotomy m n
  greater-than :
      n < m
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equal refl
<-trichotomy zero (suc n) = less-than z<s
<-trichotomy (suc m) zero = greater-than z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | less-than    m<n = less-than (s<s m<n)
...                             | equal        m≡n = equal (cong suc m≡n)
...                             | greater-than m>n = greater-than (s<s m>n)

+-monoʳ-< : ∀ {n p q : ℕ}
         → p < q
         → n + p < n + q
+-monoʳ-< {zero} p<q = p<q
+-monoʳ-< {suc n} p<q = s<s (+-monoʳ-< {n} p<q)

+-monoˡ-< : ∀ {m n p : ℕ}
         → m < n
         → m + p < n + p
+-monoˡ-< {m} {n} {p} m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-< m≤n

+-mono-< : ∀ {m n p q : ℕ}
         → m < n
         → p < q
         → m + p < n + q
+-mono-< m<n p<q = <-trans (+-monoˡ-< m<n) (+-monoʳ-< p<q)

≤-iff-< : ∀ {m n : ℕ}
        → suc m ≤ n
        → m < n
≤-iff-< {zero} {suc n} sm≤n = z<s
≤-iff-< {suc m} {suc n} (s≤s sm≤n) = s<s (≤-iff-< sm≤n)

<-iff-≤ : ∀ {m n : ℕ}
        → m < n
        → suc m ≤ n
<-iff-≤ {zero} {suc n} z<s = s≤s z≤n
<-iff-≤ {suc m} {suc n} (s<s m<n) = s≤s (<-iff-≤ m<n)

<-suc : ∀ {m n : ℕ}
      → m < n
      → m < suc n
<-suc z<s = z<s
<-suc (s<s m<n) = s<s (<-suc m<n)

<-trans-revisited : ∀ {m n p : ℕ}
                  → m < n
                  → n < p
                  → m < p
<-trans-revisited z<s (s<s n<p) = z<s
<-trans-revisited (s<s m<n) (s<s (s<s n<p)) =
  s<s (≤-iff-< (≤-trans (<-iff-≤ m<n) (<-iff-≤ (<-suc n<p))))

-- Even and odd

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
         even zero

  suc : ∀ {n : ℕ}
      → odd n
      → even (suc n)

data odd where
  suc : ∀ {n : ℕ}
      → even n
      → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
      → even m
      → even n
      → even (m + n)

o+e≡o : ∀ {m n : ℕ}
      → odd m
      → even n
      → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
      → odd m
      → odd n
      → even (m + n)
o+o≡e {suc m} {suc n} (suc em) (suc en) rewrite +-comm m (suc n) =
  suc (suc (e+e≡e en em))

-- Bin

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (bin O) = from bin * 2
from (bin I) = from bin * 2 + 1

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

to-produces-can : ∀ {n : ℕ}
                → Can (to n)
to-produces-can {zero} = zero
to-produces-can {suc n} = inc-preserves-can (to-produces-can {n})

m≤m+n : ∀ (m n : ℕ) → m ≤ m + n
m≤m+n zero _ = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

from-one-is-non-zero : ∀ {b : Bin}
                     → One b
                     → 1 ≤ from b
from-one-is-non-zero one = s≤s z≤n
from-one-is-non-zero {b O} (one-O {b} o)
  rewrite *-comm (from b) 2
        | +-identityʳ (from b)
  = ≤-trans (from-one-is-non-zero o) (m≤m+n (from b) (from b))
from-one-is-non-zero {b I} (one-I {b} o)
  rewrite *-comm (from b) 2
        | +-identityʳ (from b)
        | +-assoc (from b) (from b) 1
  = ≤-trans (from-one-is-non-zero o) (m≤m+n (from b) (from b + 1))

bin-inc-is-suc : ∀ (n : ℕ) → to (suc n) ≡ inc (to n)
bin-inc-is-suc zero = refl
bin-inc-is-suc (suc n) rewrite bin-inc-is-suc n = refl

n+n≡n*2 : ∀ (n : ℕ) → n + n ≡ n * 2
n+n≡n*2 zero = refl
n+n≡n*2 (suc n) rewrite *-comm (suc n) 2 | +-identityʳ n = refl

un-inc : ∀ (b : Bin) → b I ≡ inc (b O)
un-inc ⟨⟩ = refl
un-inc (b O) rewrite un-inc b = refl
un-inc (b I) rewrite un-inc b = refl

one-identity : ∀ {b : Bin}
             → One b
             → to (from b) ≡ b
one-identity one = refl
one-identity {b O} (one-O {b} o)
  rewrite one-identity o
  = {!!}
one-identity {b I} (one-I {b} o)
  rewrite one-identity o
        | +-comm (from b * 2) 1
        | bin-inc-is-suc (from b * 2)
        | *-comm (from b) 2
        | +-identityʳ (from b)
        | un-inc b
  = {!!}

can-identity : ∀ {b : Bin}
             → Can b
             → to (from b) ≡ b
can-identity zero = refl
can-identity {b} (canonical o) rewrite one-identity {b} o = refl
