module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; ≢-sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

-- Values do not reduce

V¬⟶ : ∀ {M N}
    → Value M
    → ¬ (M ⟶ N)
V¬⟶       V-ƛ            ()
V¬⟶    V-zero            ()
V¬⟶ (V-suc VM) (ξ-suc M⟶N) = V¬⟶ VM M⟶N

⟶¬V : ∀ {M N}
    → M ⟶ N
    → ¬ Value M
⟶¬V M⟶N VM = V¬⟶ VM M⟶N

-- Canonical Forms

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
      → ∅ , x ⦂ A ⊢ N ⦂ B
      → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero : Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
        → Canonical V ⦂ `ℕ
        → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A}
          → ∅ ⊢ V ⦂ A
          → Value V
          → Canonical V ⦂ A
canonical   (⊢ƛ ⊢N)       V-ƛ  = C-ƛ ⊢N
canonical    ⊢zero     V-zero  = C-zero
canonical (⊢suc ⊢M) (V-suc VM) = C-suc (canonical ⊢M VM)

value : ∀ {M A}
      → Canonical M ⦂ A
      → Value M
value   (C-ƛ ⊢N) = V-ƛ
value    C-zero  = V-zero
value (C-suc CM) = V-suc (value CM)

typed : ∀ {M A}
      → Canonical M ⦂ A
      → ∅ ⊢ M ⦂ A
typed   (C-ƛ ⊢N) = ⊢ƛ ⊢N
typed    C-zero  = ⊢zero
typed (C-suc CM) = ⊢suc (typed CM)

-- Progress

data Progress (M : Term) : Set where
  step : ∀ {N}
       → M ⟶ N
       → Progress M

  done : Value M
       → Progress M

progress : ∀ {M A}
         → ∅ ⊢ M ⦂ A
         → Progress M
progress (⊢ƛ ⊢N) = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L⟶L′ = step (ξ-·₁ L⟶L′)
... | done VL with progress ⊢M
...   | step M⟶M′ = step (ξ-·₂ VL M⟶M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _ = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M⟶M′ = step (ξ-suc M⟶M′)
... | done VM = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L⟶L′ = step (ξ-case L⟶L′)
... | done VL with canonical ⊢L VL
...   | C-zero = step β-zero
...   | C-suc CL = step β-suc
progress (⊢μ ⊢M) = step β-μ

Progress-≃ : ∀ {M}
           → Progress M ≃ Value M ⊎ ∃[ N ] (M ⟶ N)
Progress-≃ =
  record
    { to   = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
  to : ∀ {M}
     → Progress M
     → Value M ⊎ ∃[ N ] (M ⟶ N)
  to (step {N} M⟶N) = inj₂ ⟨ N , M⟶N ⟩
  to (done VM) = inj₁ VM

  from : ∀ {M}
       → Value M ⊎ ∃[ N ] (M ⟶ N)
       → Progress M
  from (inj₁ VM) = done VM
  from (inj₂ ⟨ _ , M⟶N ⟩) = step M⟶N

  from∘to : ∀ {M}
          → (x : Progress M)
          → from (to x) ≡ x
  from∘to (step _) = refl
  from∘to (done _) = refl

  to∘from : ∀ {M}
          → (y : Value M ⊎ ∃[ N ] (M ⟶ N))
          → to (from y) ≡ y
  to∘from (inj₁ _) = refl
  to∘from (inj₂ _) = refl

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M ⟶ N)
progress′ (ƛ _ ⇒ _) (⊢ƛ _) = inj₁ V-ƛ
progress′ (L · M) (⊢L · ⊢M) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L⟶L′ ⟩ = inj₂ ⟨ L′ · M , ξ-·₁ L⟶L′ ⟩
... | inj₁ VL with progress′ M ⊢M
... |   inj₂ ⟨ M′ , M⟶M′ ⟩ = inj₂ ⟨ L · M′ , ξ-·₂ VL M⟶M′ ⟩
... |   inj₁ VM with canonical ⊢L VL
... |     C-ƛ {x = x} {N = N} ⊢N = inj₂ ⟨ N [ x := M ] , β-ƛ VM ⟩
progress′ `zero ⊢zero = inj₁ V-zero
progress′ (`suc _) (⊢suc {_} {M} ⊢M) with progress′ M ⊢M
... | inj₂ ⟨ M′ , M⟶M′ ⟩ = inj₂ ⟨ `suc M′ , ξ-suc M⟶M′ ⟩
... | inj₁ VM = inj₁ (V-suc VM)
progress′ (case L [zero⇒ M |suc x ⇒ N ]) (⊢case ⊢L ⊢M ⊢N) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L⟶L′ ⟩ = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , ξ-case L⟶L′ ⟩
... | inj₁ VL with canonical ⊢L VL
...   | C-zero = inj₂ ⟨ M , β-zero ⟩
...   | C-suc {V} CL = inj₂ ⟨ N [ x := V ] , β-suc ⟩
progress′ (μ x ⇒ M) (⊢μ ⊢M) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | step M⟶M′ = no (⟶¬V M⟶M′)
... | done VM = yes VM

-- Renaming

ext : ∀ {Γ Δ}
    → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ         Z  = Z
ext ρ (S x≢y ∋x) = S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
       → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
       → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ          (⊢` ∋w) = ⊢` (ρ ∋w)
rename ρ          (⊢ƛ ⊢N) = ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ        (⊢L · ⊢M) = rename ρ ⊢L · rename ρ ⊢M
rename ρ           ⊢zero  = ⊢zero
rename ρ        (⊢suc ⊢M) = ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N) = ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ          (⊢μ ⊢M) = ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
       → ∅ ⊢ M ⦂ A
       → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
     → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
     → Γ         , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z D}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ D
    → Γ         , x ⦂ B ∋ z ⦂ D
  ρ                  Z  = Z
  ρ          (S x≢x Z ) = ⊥-elim (x≢x refl)
  ρ (S z≢x (S z≢x₁ ∋z)) = S z≢x₁ ∋z

swap : ∀ {Γ x y M A B C}
     → x ≢ y
     → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
     → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z D}
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ D
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ D
  ρ                 Z  = S (≢-sym x≢y) Z
  ρ          (S z≢x Z) = Z
  ρ (S z≢y (S z≢x ∋z)) = S z≢x (S z≢y ∋z)

-- Substitution

subst : ∀ {Γ x N V A B}
      → ∅ ⊢ V ⦂ A
      → Γ , x ⦂ A ⊢ N ⦂ B
      → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes   _ = weaken ⊢V
... |  no x≢y = ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... |  no    _ = ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl = ⊢ƛ (drop ⊢N)
... |  no  x≢y = ⊢ƛ (subst ⊢V (swap (≢-sym x≢y) ⊢N))
subst ⊢V (⊢L · ⊢M) = subst ⊢V ⊢L · subst ⊢V ⊢M
subst ⊢V ⊢zero = ⊢zero
subst ⊢V (⊢suc ⊢M) = ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... |  no  x≢y = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap (≢-sym x≢y) ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl = ⊢μ (drop ⊢M)
... |  no  x≢y = ⊢μ (subst ⊢V (swap (≢-sym x≢y) ⊢M))

-- Preservation

preserve : ∀ {M N A}
         → ∅ ⊢ M ⦂ A
         → M ⟶ N
         → ∅ ⊢ N ⦂ A
preserve               (⊢L · ⊢M)   (ξ-·₁ L⟶L′) = preserve ⊢L L⟶L′ · ⊢M
preserve            (⊢ƛ ⊢L · ⊢M) (ξ-·₂ _ M⟶M′) = ⊢ƛ ⊢L · preserve ⊢M M⟶M′
preserve            (⊢ƛ ⊢L · ⊢M)       (β-ƛ _) = subst ⊢M ⊢L
preserve               (⊢suc ⊢M)  (ξ-suc M⟶M′) = ⊢suc (preserve ⊢M M⟶M′)
preserve        (⊢case ⊢L ⊢M ⊢N) (ξ-case L⟶L′) = ⊢case (preserve ⊢L L⟶L′) ⊢M ⊢N
preserve     (⊢case ⊢zero ⊢M ⊢N)        β-zero = ⊢M
preserve (⊢case (⊢suc ⊢L) ⊢M ⊢N)         β-suc = subst ⊢L ⊢N
preserve                 (⊢μ ⊢M)           β-μ = subst (⊢μ ⊢M) ⊢M
