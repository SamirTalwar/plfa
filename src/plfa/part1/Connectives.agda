module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
open import plfa.part1.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

-- Conjunction is product

data _x_ (A B : Set) : Set where
  ⟨_,_⟩ : A
        → B
        → A x B

proj₁ : ∀ {A B : Set}
      → A x B
      → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀ {A B : Set}
      → A x B
      → B
proj₂ ⟨ _ , y ⟩ = y

η-x : ∀ {A B : Set} (w : A x B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-x ⟨ _ , _ ⟩ = refl

infixr 2 _x_

record _x′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _x′_

η-x′ : ∀ {A B : Set} (w : A x′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-x′ w = refl

data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

x-count : Bool x Tri → ℕ
x-count ⟨ true  , aa ⟩ = 1
x-count ⟨ true  , bb ⟩ = 2
x-count ⟨ true  , cc ⟩ = 3
x-count ⟨ false , aa ⟩ = 4
x-count ⟨ false , bb ⟩ = 5
x-count ⟨ false , cc ⟩ = 6

x-comm : ∀ {A B : Set} → A x B ≃ B x A
x-comm =
  record
    { to   = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ{ ⟨ x , y ⟩ → refl }
    ; to∘from = λ{ ⟨ y , x ⟩ → refl }
    }

x-assoc : ∀ {A B C : Set} → (A x B) x C ≃ A x (B x C)
x-assoc =
  record
    { to   = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to =  λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃x : ∀ {A B : Set} → (A ⇔ B) ≃ ((A → B) x (B → A))
⇔≃x =
  record
    { to   = λ x → ⟨ _⇔_.to x , _⇔_.from x ⟩
    ; from = λ{ ⟨ y₁ , y₂ ⟩ →
        record
          { to   = y₁
          ; from = y₂
          }
      }
    ; from∘to = λ{ record { to = to ; from = from } → refl }
    ; to∘from = λ{ ⟨ y₁ , y₂ ⟩ → refl }
    }

-- Truth is unit

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

truth′ : ⊤′
truth′ = _

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ x A ≃ A
⊤-identityˡ =
  record
    { to   = λ{ ⟨ tt , x ⟩ → x }
    ; from = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → A x ⊤ ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A x ⊤)
  ≃⟨ x-comm ⟩
    (⊤ x A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- Disjunction is sum

data _⊎_ (A B : Set) : Set where
  inj₁ : A
       → A ⊎ B

  inj₂ : B
       → A ⊎ B

case-⊎ : {A B C : Set}
       → (A → C)
       → (B → C)
       → (A ⊎ B)
       → C
case-⊎ f _ (inj₁ x) = f x
case-⊎ _ g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ _) = refl
η-⊎ (inj₂ _) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B)
       → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ _) = refl
uniq-⊎ h (inj₂ _) = refl

infixr 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)  = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa)    = 3
⊎-count (inj₂ bb)    = 4
⊎-count (inj₂ cc)    = 5

double-swap-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₂ inj₁ (case-⊎ inj₂ inj₁ w) ≡ w
double-swap-⊎ (inj₁ _) = refl
double-swap-⊎ (inj₂ _) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to   = case-⊎ inj₂ inj₁
    ; from = case-⊎ inj₂ inj₁
    ; from∘to = double-swap-⊎
    ; to∘from = double-swap-⊎
    }

⊎-assoc-to : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-to (inj₁ (inj₁ x)) = inj₁ x
⊎-assoc-to (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎-assoc-to (inj₂ z) = inj₂ (inj₂ z)

⊎-assoc-from : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-from (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc-from (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
⊎-assoc-from (inj₂ (inj₂ z)) = inj₂ z

⊎-assoc-from∘to : ∀ {A B C : Set} (w : (A ⊎ B) ⊎ C) → ⊎-assoc-from (⊎-assoc-to w) ≡ w
⊎-assoc-from∘to (inj₁ (inj₁ x)) = refl
⊎-assoc-from∘to (inj₁ (inj₂ y)) = refl
⊎-assoc-from∘to (inj₂ z) = refl

⊎-assoc-to∘from : ∀ {A B C : Set} (w : A ⊎ (B ⊎ C)) → ⊎-assoc-to (⊎-assoc-from w) ≡ w
⊎-assoc-to∘from (inj₁ x) = refl
⊎-assoc-to∘from (inj₂ (inj₁ y)) = refl
⊎-assoc-to∘from (inj₂ (inj₂ z)) = refl

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to   = ⊎-assoc-to
    ; from = ⊎-assoc-from
    ; from∘to = ⊎-assoc-from∘to
    ; to∘from = ⊎-assoc-to∘from
    }

-- False is empty

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
       → ⊥
       → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to   = case-⊎ ⊥-elim id
    ; from = inj₂
    ; from∘to = λ{ (inj₂ x) → refl }
    ; to∘from = λ y → refl
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ =
  record
    { to   = case-⊎ id ⊥-elim
    ; from = inj₁
    ; from∘to = λ{ (inj₁ x) → refl }
    ; to∘from = λ y → refl
    }

-- Implication is function

→-elim : ∀ {A B : Set}
       → (A → B)
       → A
       → B
→-elim f x = f x

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
...          |     aa |      aa = 1
...          |     aa |      bb = 2
...          |     aa |      cc = 3
...          |     bb |      aa = 4
...          |     bb |      bb = 5
...          |     bb |      cc = 6
...          |     cc |      aa = 7
...          |     cc |      bb = 8
...          |     cc |      cc = 9

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A x B → C)
currying =
  record
    { to   = λ{ f ⟨ a , b ⟩ → f a b }
    ; from = λ f a b → f ⟨ a , b ⟩
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ{ ⟨ a , b ⟩ → refl }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) x (B → C))
→-distrib-⊎ =
  record
    { to   = λ f → ⟨ (λ x → f (inj₁ x)) , (λ y → f (inj₂ y)) ⟩
    ; from = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x; (inj₂ y) → h y } }
    ; from∘to = λ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-x : ∀ {A B C : Set} → (A → B x C) ≃ ((A → B) x (A → C))
→-distrib-x =
  record
    { to   = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
    ; from =  λ{ ⟨ g , h ⟩ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ f → extensionality (η-x ∘ f)
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

-- Distribution

x-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) x C ≃ (A x C) ⊎ (B x C)
x-distrib-⊎ =
  record
    { to   = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩
              ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩
              }
    ; from = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
              ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
              }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-x : ∀ {A B C : Set} → (A x B) ⊎ C ≲ (A ⊎ C) x (B ⊎ C)
⊎-distrib-x =
  record
    { to   = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
              ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
              }
    ; from = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
              ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
              ; ⟨ inj₂ z , _      ⟩ → inj₂ z
              }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z) → refl
                 }
    }

⊎-weak-x : ∀ {A B C : Set} → (A ⊎ B) x C → A ⊎ (B x C)
⊎-weak-x ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-x ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

⊎x-implies-x⊎ : ∀ {A B C D : Set} → (A x B) ⊎ (C x D) → (A ⊎ C) x (B ⊎ D)
⊎x-implies-x⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎x-implies-x⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- x⊎-implies-⊎x : ∀ {A B C D : Set} → (A ⊎ B) x (C ⊎ D) → (A x C) ⊎ (B x D)
-- x⊎-implies-⊎x ⟨ inj₁ a , inj₁ c ⟩ = inj₁ ⟨ a , c ⟩
-- x⊎-implies-⊎x ⟨ inj₁ a , inj₂ d ⟩ = {!!} -- Impossible.
-- x⊎-implies-⊎x ⟨ inj₂ b , inj₁ c ⟩ = {!!} -- Impossible.
-- x⊎-implies-⊎x ⟨ inj₂ b , inj₂ d ⟩ = inj₂ ⟨ b , d ⟩

-- import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
-- import Data.Unit using (⊤; tt)
-- import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- import Data.Empty using (⊥; ⊥-elim)
-- import Function.Equivalence using (_⇔_)
