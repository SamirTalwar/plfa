module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Nullary using (¬_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

-- Universals

∀-elim : ∀ {A : Set} {B : A → Set}
       → (L : ∀ (x : A) → B x)
       → (M : A)
       → B M
∀-elim L M = L M

∀-distribute-× : ∀ {A : Set} {B C : A → Set}
               → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distribute-× =
  record
    { to   = λ f → (λ a → proj₁ (f a)) , (λ a → proj₂ (f a))
    ; from = λ{ (g , h) → λ a → (g a , h a) }
    ; from∘to = λ f →
        begin
          (λ a → (proj₁ (f a) , proj₂ (f a)))
        ≡⟨⟩
          f
        ∎
    ; to∘from = λ{ (g , h) → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
              → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
              → (∀ (x : A) → B x ⊎ C x)
⊎∀-implies-∀⊎ (inj₁ f) x = inj₁ (f x)
⊎∀-implies-∀⊎ (inj₂ g) x = inj₂ (g x)


-- This does not hold because the two returned functions will be partial,
-- i.e. they do not hold for all (x : A).
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set}
--               → (∀ (x : A) → B x ⊎ C x)
--               → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀extensionality : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
                  → (∀ (x : A) → f x ≡ g x)
                  → f ≡ g

tri-isomorphism : ∀ {B : Tri → Set}
                → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
tri-isomorphism =
  record
    { to   = λ f → f aa , f bb , f cc
    ; from = λ{ (a , b , c) → λ{ aa → a ; bb → b ; cc → c } }
    ; from∘to = λ f → ∀extensionality λ{ aa → refl ; bb → refl ; cc → refl }
    ; to∘from = λ{ (a , b , c) → refl }
    }

-- Existentials

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂' : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
       → (∀ x → B x → C)
       → ∃[ x ] B x
       → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
            → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to   = λ{ f ⟨ a , b ⟩ → f a b }
    ; from = λ g a b → g ⟨ a , b ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ{ ⟨ a , b ⟩ → refl }
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
            → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to   = λ{ ⟨ x , inj₁ b ⟩ → inj₁ ⟨ x , b ⟩ ; ⟨ x , inj₂ c ⟩ → inj₂ ⟨ x , c ⟩ }
    ; from = λ{ (inj₁ ⟨ x , b ⟩) → ⟨ x , inj₁ b ⟩ ; (inj₂ ⟨ x , c ⟩) → ⟨ x , inj₂ c ⟩ }
    ; from∘to = λ{ ⟨ x , inj₁ b ⟩ → refl ; ⟨ x , inj₂ c ⟩ → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , b ⟩) → refl ; (inj₂ ⟨ x , c ⟩) → refl }
    }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
              → ∃[ x ] (B x × C x)
              → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , (b , c) ⟩ = ⟨ x , b ⟩ , ⟨ x , c ⟩


-- This does not hold because we cannot know which of `a₁` or `a₂` should be used.
-- ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set}
--               → (∃[ x ] B x) × (∃[ x ] C x)
--               → ∃[ x ] (B x × C x)
-- ×∃-implies-∃× (⟨ a₁ , b ⟩ , ⟨ a₂ , c ⟩) = {!!}

∃-⊎ : ∀ {B : Tri → Set}
    → (∃[ x ] B x) ≃ (B aa ⊎ B bb ⊎ B cc)
∃-⊎ =
  record
    { to   = λ{ ⟨ aa , b ⟩ → inj₁ b ; ⟨ bb , b ⟩ → inj₂ (inj₁ b) ; ⟨ cc , b ⟩ → inj₂ (inj₂ b) }
    ; from = λ{ (inj₁ b) → ⟨ aa , b ⟩ ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩ ; (inj₂ (inj₂ b)) → ⟨ cc , b ⟩ }
    ; from∘to = λ{ ⟨ aa , b ⟩ → refl ; ⟨ bb , b ⟩ → refl ; ⟨ cc , b ⟩ → refl }
    ; to∘from = λ{ (inj₁ b) → refl ; (inj₂ (inj₁ b)) → refl ; (inj₂ (inj₂ b)) → refl }
    }

-- An existential example

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃   even-zero  = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e) with even-∃ e
...                  | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩)

≤→∃+ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
≤→∃+  {zero}     {z}      z≤n  = ⟨ z , +-identityʳ z ⟩
≤→∃+ {suc y} {suc z} (s≤s y≤z) with ≤→∃+ y≤z
...                               | ⟨ m , refl ⟩ = ⟨ m , +-suc m y ⟩

∃+→≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃+→≤ {zero} {z} ⟨ x , refl ⟩ = z≤n
∃+→≤ {suc y} {z} ⟨ zero , refl ⟩ = s≤s (∃+→≤ ⟨ zero , refl ⟩)
∃+→≤ {suc y} {suc z} ⟨ suc x , refl ⟩ = s≤s (∃+→≤ ⟨ suc x , sym (+-suc x y) ⟩)

-- Existentials, Universals, and Negation

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
      → (¬ ∃[ x ] B x) ≃ (∀ x → ¬ B x)
¬∃≃∀¬ =
  record
    { to   = λ ¬∃ x b → ¬∃ ⟨ x , b ⟩
    ; from = λ{ ∀¬ ⟨ x , b ⟩ → ∀¬ x b }
    ; from∘to = λ ¬∃ → extensionality λ{ ⟨ x , b ⟩ → refl }
    ; to∘from = λ ∀¬ → refl
    }

∃¬→¬∀ : ∀ {A : Set} {B : A → Set}
      → (∃[ x ] (¬ B x))
      → ¬ (∀ x → B x)
∃¬→¬∀ ⟨ x , ¬b ⟩ ∀x→Bx = ¬b (∀x→Bx x)

-- This does not hold because while the negation of a forall *does* imply the existence of a negation,
-- we cannot know the value of `x` that proves it.
-- ¬∀→∃¬ : ∀ {A : Set} {B : A → Set}
--       → ¬ (∀ x → B x)
--       → (∃[ x ] (¬ B x))
-- ¬∀→∃¬ ¬∀ = ⟨ {!!} , {!!} ⟩
