module plfa.part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (step-≡; _≡⟨⟩_) renaming (begin_ to ≡-begin_; _∎ to _≡∎)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import plfa.part1.Isomorphism using (_≲_)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
           ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
          ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
          ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · (` "n" · ` "s" · ` "z") · ` "z"

-- Primed

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′     _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc     _ ⇒ _ ] = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′     _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

infix  5 ƛ′_⇒_
infix  5 μ′_⇒_

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n)
            ]
  where
  + = ` "+"
  m = ` "m"
  n = ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ `zero
            |suc m ⇒ + · n · (* · m · n)
            ]
  where
  + = ` "+"
  * = ` "*"
  m = ` "m"
  n = ` "n"

-- Values

data Value : Term → Set where
  V-ƛ : ∀ {x N}
      → Value (ƛ x ⇒ N)

  V-zero : Value `zero

  V-suc : ∀ {V}
        → Value V
        → Value (`suc V)

-- Substitution

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no  _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no  _ = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- Quiz: the answer is #3.
_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

infix 9 _[_:=_]′
_[_:=_]′ : Term → Id → Term → Term

infix 9 _[?_≠_:=_?]′
_[?_≠_:=_?]′ : Term → Id → Id → Term → Term

(` x) [ y := V ]′ with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ N [? y ≠ x := V ?]′
(L · M) [ y := V ]′ = L [ y := V ]′ · M [ y := V ]′
(`zero) [ y := V ]′ = `zero
(`suc M) [ y := V ]′ = `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ = case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ N [? y ≠ x := V ?]′ ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ N [? y ≠ x := V ?]′

N [? y ≠ x := V ?]′ with x ≟ y
... | yes _ = N
... | no  _ = N [ y := V ]′

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′ ≡ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z"))
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ ƛ "y" ⇒ ` "y"
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]′ ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl


-- Reduction

infix 4 _⟶_

data _⟶_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M}
       → L ⟶ L′
       → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {V M M′}
       → Value V
       → M ⟶ M′
       → V · M ⟶ V · M′

  β-ƛ : ∀ {x N V}
      → Value V
      → (ƛ x ⇒ N) · V ⟶ N [ x := V ]

  ξ-suc : ∀ {M M′}
        → M ⟶ M′
        → `suc M ⟶ `suc M′

  ξ-case : ∀ {x L L′ M N}
         → L ⟶ L′
         → case L [zero⇒ M |suc x ⇒ N ] ⟶ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
         → case `zero [zero⇒ M |suc x ⇒ N ] ⟶ M

  β-suc : ∀ {x V M N}
        → case `suc V [zero⇒ M |suc x ⇒ N ] ⟶ N [ x := V ]

  β-μ : ∀ {x M}
      → μ x ⇒ M ⟶ M [ x := μ x ⇒ M ]

-- Quiz: The answer is #1.
_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ⟶ ƛ "x" ⇒ ` "x"
_ = β-ƛ V-ƛ

-- Quiz: The answer is #2.
_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") ⟶ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

-- Quiz: The answer is #2.
_ : twoᶜ · sucᶜ · `zero ⟶ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)

infix  2 _-↠_
infix  1 begin_
infixr 2 _⟶⟨_⟩_
infixr 2 _-↠⟨_⟩_
infix  3 _∎

data _-↠_ : Term → Term → Set where
  _∎ : ∀ M
     → M -↠ M

  _⟶⟨_⟩_ : ∀ L {M N}
         → L ⟶ M
         → M -↠ N
         → L -↠ N

begin_ : ∀ {M N}
       → M -↠ N
       → M -↠ N
begin m-↠n = m-↠n

_-↠⟨_⟩_ : ∀ L {M N}
        → L -↠ M
        → M -↠ N
        → L -↠ N
L -↠⟨ L ∎ ⟩ MN = MN
_-↠⟨_⟩_ K {M} {N} (_⟶⟨_⟩_ K {L} KL LM) MN =
  K ⟶⟨ KL ⟩ L -↠⟨ LM ⟩ MN

data _-↠′_ : Term → Term → Set where
  refl′ : ∀ {M}
        → M -↠′ M

  step′ : ∀ {M N}
        → M ⟶ N
        → M -↠′ N

  trans′ : ∀ {L M N}
         → L -↠′ M
         → M -↠′ N
         → L -↠′ N

-↠≲-↠′ : ∀ M N
       → M -↠ N ≲ M -↠′ N
-↠≲-↠′ M N =
  record
    { to   = to M N
    ; from = from M N
    ; from∘to = from∘to M N
    -- ; We cannot implement `to∘from` because reducing `trans′ X refl′` to `X`
    --   requires a postulate.
    }
  where
  to : ∀ M N
     → M -↠ N
     → M -↠′ N
  to M M (M ∎) = refl′
  to L N (_⟶⟨_⟩_ L {M} {N} LM MN) = trans′ (step′ LM) (to M N MN)

  from : ∀ M N
       → M -↠′ N
       → M -↠ N
  from M M refl′ = begin M ∎
  from M N (step′ MN) = begin M ⟶⟨ MN ⟩ N ∎
  from L N (trans′ {L} {M} {N} LM MN) =
    L -↠⟨ from L M LM ⟩ (from M N MN)

  from∘to : ∀ M N
          → (x : M -↠ N)
          → from M N (to M N x) ≡ x
  from∘to M M (M ∎) = refl
  from∘to L N (_⟶⟨_⟩_ L {M} {N} LM MN) =
    ≡-begin
      from L N (to L N (L ⟶⟨ LM ⟩ MN))
    ≡⟨⟩
      from L N (trans′ (step′ LM) (to M N MN))
    ≡⟨⟩
      (L -↠⟨ from L M (step′ LM) ⟩ (from M N (to M N MN)))
    ≡⟨⟩
      (L -↠⟨ L ⟶⟨ LM ⟩ M ∎ ⟩ (from M N (to M N MN)) )
    ≡⟨⟩
      (L ⟶⟨ LM ⟩ M -↠⟨ M ∎ ⟩ (from M N (to M N MN)))
    ≡⟨⟩
      (L ⟶⟨ LM ⟩ (from M N (to M N MN)))
    ≡⟨ cong (L ⟶⟨ LM ⟩_) (from∘to M N MN) ⟩
      (L ⟶⟨ LM ⟩ MN)
    ≡∎
