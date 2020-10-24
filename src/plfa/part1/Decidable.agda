module plfa.part1.Decidable where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import plfa.part1.Relations using (_≤_; z≤n; s≤s; _<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

-- Booleans

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ n     = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool)
    → T b
    → b ≡ true
T→≡ true tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool}
    → b ≡ true
    → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤   zero       n  tt = z≤n
≤ᵇ→≤ (suc m) (suc n)  t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ      z≤n  = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

-- Decidables

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

¬m<z : ∀ {m : ℕ} → ¬ (m < zero)
¬m<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m     <? zero  = no ¬m<z
zero  <? suc n = yes z<s
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no (λ ())
suc m ≡ℕ? zero = no (λ ())
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (cong suc m≡n)
...                | no ¬m≡n = no (¬s≡s ¬m≡n)

_ : 3 ≡ℕ? 3 ≡ yes _
_ = refl

_ : 2 ≡ℕ? 3 ≡ no _
_ = refl

-- Decidables from booleans, and booleans from decidables

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        |   true |       p |            _ = yes (p tt)
...        |  false |       _ |           ¬p = no ¬p

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness

-- Logical connectives

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
true  ∧ false = false
false ∧ _     = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec yes _ = no λ{ ⟨ x , _ ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ _ , y ⟩ → ¬y y }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
false ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
no  _ ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ { (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ false = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes (λ _ → y)
yes x →-dec no ¬y = no (λ f → ¬y (f x))
no ¬x →-dec no ¬y = yes λ x → ⊥-elim (¬x x)

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes _) (yes _) = refl
∧-× (yes _) ( no _) = refl
∧-× ( no _) (yes _) = refl
∧-× ( no _) ( no _) = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes _) (yes _) = refl
∨-⊎ (yes _) ( no _) = refl
∨-⊎ ( no _) (yes _) = refl
∨-⊎ ( no _) ( no _) = refl

not-¬ : ∀ {A : Set} → (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes _) = refl
not-¬ ( no _) = refl

_iff_ : Bool → Bool → Bool
true  iff true  = true
true  iff false = false
false iff true  = false
false iff false = true

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes (record { to = λ _ → y ; from = λ _ → x })
yes x ⇔-dec no ¬y = no (λ a⇔b → ¬y (_⇔_.to a⇔b x))
no ¬x ⇔-dec yes y = no (λ a⇔b → ¬x (_⇔_.from a⇔b y))
no ¬x ⇔-dec no ¬y = yes (record { to = λ x → ⊥-elim (¬x x) ; from = λ y → ⊥-elim (¬y y) })

-- Proof by reflection

minus : (m n : ℕ) → (n≤m : n ≤ m) → ℕ
minus      m    zero         _  = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (m n : ℕ) → {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

False : ∀ {Q} → Dec Q → Set
False Q = T ⌊ ¬? Q ⌋

toWitnessFalse : ∀ {A : Set} {D : Dec A} → T ⌊ ¬? D ⌋ → ¬ A
toWitnessFalse {A} {no ¬x} tt = ¬x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → T ⌊ ¬? D ⌋
fromWitnessFalse {A} {yes x} ¬a = ¬a x
fromWitnessFalse {A}  {no x} ¬a = tt

minus′ : (m n : ℕ) → ¬ (m < n) → ℕ
minus′      m    zero       _ = m
minus′   zero  (suc n)  ¬z<sn = ⊥-elim (¬z<sn z<s)
minus′ (suc m) (suc n) ¬sm<sn = minus′ m n λ m<n → ¬sm<sn (s<s m<n)

_-′_ : (m n : ℕ) → {¬m<n : False (m <? n)} → ℕ
_-′_ m n {¬m<n} = minus′ m n (toWitnessFalse ¬m<n)

_ : 5 -′ 3 ≡ 2
_ = refl
