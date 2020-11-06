module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

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
