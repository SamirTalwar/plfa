module plfa.part2.Bisimulation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import plfa.part2.More

infix 4 _~_
infix 5 ~ƛ_
infix 7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ~` : ∀ {Γ A} {x : Γ ∋ A}
    → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
    → `let M N ~ (ƛ N†) · M†

~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
  → Value M†
~val (~ƛ _) V-ƛ = V-ƛ

~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
  → Value M
~val⁻¹ (~ƛ _) V-ƛ = V-ƛ

~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ ~`           = ~`
~rename ρ (~ƛ ~N)      = ~ƛ ~rename (ext ρ) ~N
~rename ρ (~L ~· ~M)   = ~rename ρ ~L ~· ~rename ρ ~M
~rename ρ (~let ~M ~N) = ~let (~rename ρ ~M) (~rename (ext ρ) ~N)

~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A}   → (x : Γ     ∋ A) →      σ x ~      σ† x)
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z     = ~`
~exts ~σ (S x) = ~rename S_ (~σ x)

~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x}) = ~σ x
~subst ~σ (~ƛ ~N)      = ~ƛ ~subst (~exts ~σ) ~N
~subst ~σ (~L ~· ~M)   = ~subst ~σ ~L ~· ~subst ~σ ~M
~subst ~σ (~let ~M ~N) = ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)

~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z     = ~M
  ~σ (S _) = ~`

data Leg {Γ A} (M† N : Γ ⊢ A) : Set where
  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
    → Leg M† N

sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
  → Leg M† N
sim (~L ~· ~M) (ξ-·₁ L—→L′)
  with sim ~L L—→L′
... | leg ~L′ L†—→N† = leg (~L′ ~· ~M) (ξ-·₁ L†—→N†)
sim (~L ~· ~M) (ξ-·₂ VL M—→M′)
  with sim ~M M—→M′
... | leg ~M′ M†—→N† = leg (~L ~· ~M′) (ξ-·₂ (~val ~L VL) M†—→N†)
sim ((~ƛ ~N) ~· ~M) (β-ƛ VM) = leg (~sub ~N ~M) (β-ƛ (~val ~M VM))
sim (~let ~M ~N) (ξ-let M—→M′)
  with sim ~M M—→M′
... | leg ~M′ M†—→N† = leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→N†)
sim (~let ~M ~N) (β-let VM) = leg (~sub ~N ~M) (β-ƛ (~val ~M VM))
