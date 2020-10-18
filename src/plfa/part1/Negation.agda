module plfa.part1.Negation where

import Relation.Binary.PropositionalEquality as Eq
import Relation.Nullary
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function.Base using (_∘_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _>_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂; swap)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
       → ¬ A
       → A
       → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
         → A
         → ¬ ¬ A
¬¬-intro x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
         → ¬ ¬ ¬ A
         → ¬ A
¬¬¬-elim ¬¬¬x ¬x = ¬¬¬x (¬¬-intro ¬x)

contraposition : ∀ {A B : Set}
               → (A → B)
               → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {n : ℕ} → zero ≢ suc n
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x _ = extensionality (λ x → ⊥-elim (¬x x))

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {zero} = λ ()
<-irreflexive {suc n} (s≤s sn≤n) = <-irreflexive sn≤n

data Trichotomy (m n : ℕ) : Set where
  less-than :
         m < n
    → ¬ (m ≡ n)
    → ¬ (m > n)
    → Trichotomy m n
  equal :
      ¬ (m < n)
    →    m ≡ n
    → ¬ (m > n)
    → Trichotomy m n
  greater-than :
      ¬ (m < n)
    → ¬ (m ≡ n)
    →    m > n
    → Trichotomy m n

suc-m≡n : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
suc-m≡n refl = refl

suc-¬m≡n : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
suc-¬m≡n ¬m≡n = λ{ refl → ¬m≡n refl }

suc-¬m<n : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
suc-¬m<n ¬m<n = λ{ (s≤s m<n) → ¬m<n m<n }

suc-¬m>n : ∀ {m n : ℕ} → ¬ (m > n) → ¬ (suc m > suc n)
suc-¬m>n {m} {n} = suc-¬m<n {n} {m}

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy   zero    zero  = equal (λ ()) refl (λ ())
trichotomy   zero  (suc n) = less-than (s≤s z≤n) (λ ()) (λ ())
trichotomy (suc m)   zero  = greater-than (λ ()) (λ ()) (s≤s z≤n)
trichotomy (suc m) (suc n) with trichotomy m n
...                           | less-than     m<n ¬m≡n ¬m>n = less-than         (s≤s  m<n) (suc-¬m≡n ¬m≡n) (suc-¬m>n ¬m>n)
...                           | equal        ¬m<n  m≡n ¬m>n = equal        (suc-¬m<n ¬m<n) ( suc-m≡n  m≡n) (suc-¬m>n ¬m>n)
...                           | greater-than ¬m<n ¬m≡n  m>n = greater-than (suc-¬m<n ¬m<n) (suc-¬m≡n ¬m≡n)      (s≤s  m>n)

⊎-dual-x : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-x =
  record
    { to   = λ ¬a⊎b → ( (λ a → ¬a⊎b (inj₁ a)) , (λ b → ¬a⊎b (inj₂ b)) )
    ; from = λ{ (¬a , ¬b) → λ{ (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b } }
    ; from∘to = λ ¬a⊎b → extensionality λ{ (inj₁ a) → refl ; (inj₂ b) → refl }
    ; to∘from = λ{ ¬a×¬b → refl }
    }

-- x-dual-⊎ : ∀ {A B : Set} → ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
-- x-dual-⊎ =
--   record
--     { to   = λ ¬a×b → {!!}
--     ; from = λ{ (inj₁ ¬a) → λ{ (a , _) → ¬a a }; (inj₂ ¬b) → λ{ (_ , b) → ¬b b } }
--     ; from∘to = {!!}
--     ; to∘from = {!!}
--     }

-- I am fairly sure that `to` is possible, but I don't know how to solve it.
-- `from∘to` seems impossible, because `to` would have to choose either `¬ A` or `¬ B` in the case where `¬ A × ¬ B`.
-- So I expect that it is possible to show `(¬ A) ⊎ (¬ B) ≲ ¬ (A × B)`.

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ x → k (inj₁ x))

module Classical where
  em→double-negation : (∀ {A : Set} → A ⊎ ¬ A)
                     → (∀ {A : Set} → ¬ ¬ A → A)
  em→double-negation em ¬¬a = [ (λ a → a) , (⊥-elim ∘ ¬¬a) ] em

  double-negation→em : (∀ {A : Set} → ¬ ¬ A → A)
                     → (∀ {A : Set} → A ⊎ ¬ A)
  double-negation→em dn = dn λ neg → neg (inj₂ λ a → neg (inj₁ a))

  em→peirce : (∀ {A : Set} → A ⊎ ¬ A)
            → (∀ {A B : Set} → ((A → B) → A) → A)
  em→peirce em f = [ (λ a → a) , (λ ¬a → f λ a → ⊥-elim (¬a a)) ] em

  peirce→em : (∀ {A B : Set} → ((A → B) → A) → A)
            → (∀ {A : Set} → A ⊎ ¬ A)
  peirce→em peirce = peirce (λ z → inj₂ (λ x → z (inj₁ x)))

  em→impl-disj : (∀ {A : Set} → A ⊎ ¬ A)
               → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
  em→impl-disj em f = [ (λ b → inj₂ b) , (λ ¬a → inj₁ (λ a → ¬a (f a))) ] em

  impl-disj→em : (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
               → (∀ {A : Set} → A ⊎ ¬ A)
  impl-disj→em impl-disj = swap (impl-disj λ x → x)

  em→de-morgan : (∀ {A : Set} → A ⊎ ¬ A)
               → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
  em→de-morgan em dm = [ (λ a → inj₁ a) , (λ ¬a → [ (λ b → inj₂ b) , (λ ¬b → ⊥-elim (dm (¬a , ¬b))) ] em) ] em

  de-morgan→em : (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
               → (∀ {A : Set} → A ⊎ ¬ A)
  de-morgan→em dm = dm (λ{ (¬a , ¬¬a) → ¬¬a ¬a })

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-is-stable : ∀ {A : Set} → Stable (¬ A)
¬-is-stable ¬¬a a = ¬¬a λ ¬a → ¬a a

×-is-stable : ∀ {A B : Set}
            → Stable A
            → Stable B
            → Stable (A × B)
×-is-stable sa sb ¬¬a×b = ( sa (λ ¬a → ¬¬a×b λ{ (a , _) → ¬a a })
                          , sb (λ ¬b → ¬¬a×b λ{ (_ , b) → ¬b b })
                          )

-- import Relation.Nullary using (¬_)
-- import Relation.Nullary.Negation using (contraposition)
