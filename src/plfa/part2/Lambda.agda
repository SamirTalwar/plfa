module plfa.part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning using (step-≡; _≡⟨⟩_) renaming (begin_ to ≡-begin_; _∎ to _≡∎)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import plfa.part1.Isomorphism using (_≃_; _≲_)

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
         ` "m" · (` "n" · ` "s") · ` "z"

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
infixr 2 _⟶⟨⟩_
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

_⟶⟨⟩_ : ∀ M {N}
      → M -↠ N
      → M -↠ N
M ⟶⟨⟩ MN = MN

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

-- Confluence

postulate
  confluence : ∀ {L M N}
             → ((L -↠ M) × (L -↠ N))
             → ∃[ P ] ((M -↠ P) × (N -↠ P))

  diamond : ∀ {L M N}
          → (L ⟶ M × L ⟶ N)
          → ∃[ P ] (M ⟶ P × N ⟶ P)

  deterministic : ∀ {L M N}
                → L ⟶ M
                → L ⟶ N
                → M ≡ N

_ : twoᶜ · sucᶜ · `zero -↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  ⟶⟨⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) · (ƛ "n" ⇒ `suc (` "n")) · `zero
  ⟶⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  ⟶⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · (`suc `zero)
  ⟶⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎

_ : plus · two · two -↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  ⟶⟨⟩
    (μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])
      · `suc `suc `zero
      · `suc `suc `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
      · `suc `suc `zero
      · `suc `suc `zero
  ⟶⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
         case (`suc `suc `zero)
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
           ])
      · `suc `suc `zero
  ⟶⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case `suc `suc `zero
      [zero⇒ `suc `suc `zero
      |suc "m" ⇒ `suc (plus · ` "m" · `suc `suc `zero)
      ]
  ⟶⟨ β-suc ⟩
    `suc (plus · `suc `zero · `suc `suc `zero)
  ⟶⟨⟩
    `suc (
      (μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])
        · `suc `zero
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `suc `zero
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc (
      (ƛ "n" ⇒
        case `suc `zero
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (
      case `suc `zero
        [zero⇒ `suc `suc `zero
        |suc "m" ⇒ `suc (plus · ` "m" · `suc `suc `zero)
        ]
    )
  ⟶⟨ ξ-suc β-suc ⟩
    `suc `suc (plus · `zero · `suc `suc `zero)
  ⟶⟨⟩
    `suc `suc (
      (μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])
        · `zero
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `zero
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc (
      (ƛ "n" ⇒
        case `zero
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `suc `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (
      case `zero
        [zero⇒ `suc `suc `zero
        |suc "m" ⇒ `suc (plus · ` "m" · `suc `suc `zero)
        ]
    )
  ⟶⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc `suc `suc `suc `zero
  ∎

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero -↠ `suc `suc `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
  ⟶⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
  ⟶⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
  ⟶⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
  ⟶⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc `suc `zero)
  ⟶⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · (`suc `suc `suc `zero)
  ⟶⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

one : Term
one = `suc `zero

plus-example : plus · one · one -↠ two
plus-example =
  begin
    plus · one · one
  ⟶⟨⟩
    (μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])
      · `suc `zero
      · `suc `zero
  ⟶⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m"
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
        ])
      · `suc `zero
      · `suc `zero
  ⟶⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case `suc `zero
        [zero⇒ ` "n"
        |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
        ])
      · `suc `zero
  ⟶⟨ β-ƛ (V-suc V-zero) ⟩
    case `suc `zero
      [zero⇒ `suc `zero
      |suc "m" ⇒ `suc (plus · ` "m" · `suc `zero)
      ]
  ⟶⟨ β-suc ⟩
    `suc (plus · `zero · `suc `zero)
  ⟶⟨⟩
    `suc (
      (μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])
        · `zero
        · `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc (
      (ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `zero
        · `suc `zero
    )
  ⟶⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc (
      (ƛ "n" ⇒
        case `zero
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc (plus · ` "m" · ` "n")
          ])
        · `suc `zero
    )
  ⟶⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (
      case `zero
        [zero⇒ `suc `zero
        |suc "m" ⇒ `suc (plus · ` "m" · `suc `zero)
        ]
    )
  ⟶⟨ ξ-suc β-zero ⟩
    `suc `suc `zero
  ⟶⟨⟩
    two
  ∎

-- Types

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Quiz: the type of:
--   ƛ "s" ⇒ ` "s" · (` "s"  · `zero)
-- is:
--   2. (`ℕ ⇒ `ℕ) ⇒ `ℕ

-- Quiz: the type of:
--   (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ
-- is:
--   6. `ℕ

-- Typing

infixl 5 _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

Context-≃ : Context ≃ List (Id × Type)
Context-≃ =
  record
    { to   = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
  to : Context → List (Id × Type)
  to ∅ = []
  to (Γ , x ⦂ A) = (x , A) ∷ to Γ

  from : List (Id × Type) → Context
  from [] = ∅
  from ((x , A) ∷ Γ) = (from Γ) , x ⦂ A

  from∘to : (x : Context) → from (to x) ≡ x
  from∘to ∅ = refl
  from∘to (Γ , x ⦂ A) =
    ≡-begin
      from (to (Γ , x ⦂ A))
    ≡⟨⟩
      from (to Γ) , x ⦂ A
    ≡⟨ cong (_, x ⦂ A) (from∘to Γ) ⟩
      Γ , x ⦂ A
    ≡∎

  to∘from : (y : List (Id × Type)) → to (from y) ≡ y
  to∘from [] = refl
  to∘from ((x , A) ∷ Γ) =
    ≡-begin
      to (from ((x , A) ∷ Γ))
    ≡⟨⟩
      (x , A) ∷ to (from Γ)
    ≡⟨ cong ((x , A) ∷_) (to∘from Γ) ⟩
      (x , A) ∷ Γ
    ≡∎

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    → Γ , y ⦂ B ∋ x ⦂ A

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
   → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} Γ = S (toWitnessFalse x≢y) Γ

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
  -- Axiom
  ⊢` : ∀ {Γ x A}
     → Γ ∋ x ⦂ A
     → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
     → Γ , x ⦂ A ⊢ N ⦂ B
     → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ⦂ A ⇒ B
      → Γ ⊢ M ⦂ A
      → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
        → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
       → Γ ⊢ M ⦂ `ℕ
       → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
        → Γ ⊢ L ⦂ `ℕ
        → Γ ⊢ M ⦂ A
        → Γ , x ⦂ `ℕ ⊢ N ⦂ A
        → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
     → Γ , x ⦂ A ⊢ M ⦂ A
     → Γ ⊢ μ x ⇒ M ⦂ A

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero

∋-injective : ∀ {Γ x A B}
            → Γ ∋ x ⦂ A
            → Γ ∋ x ⦂ B
            → A ≡ B
∋-injective           Z            Z  = refl
∋-injective           Z  (S x≢x    _) = ⊥-elim (x≢x refl)
∋-injective (S x≢x    _)           Z  = ⊥-elim (x≢x refl)
∋-injective (S   _ ∋x⦂A) (S   _ ∋x⦂B) = ∋-injective ∋x⦂A ∋x⦂B

nope₁ : ∀ {Γ A} → ¬ (Γ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` Z · ⊢` ∋x)) = contradiction (∋-injective Z ∋x)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

-- Quiz 1: A ≡ `ℕ
quiz₁ : ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ `ℕ
quiz₁ = ⊢` (S′ Z) · ⊢` Z

-- Quiz 2: no such A
quiz₂ : ∀ {A} → ¬ (∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A)
quiz₂ (⊢` (S x≢x _) · _) = x≢x refl

-- Quiz 3: A ≡ `ℕ ⇒ `ℕ
quiz₃ : ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ `ℕ ⇒ `ℕ
quiz₃ = ⊢ƛ ((⊢` (S′ Z)) · ⊢` Z)

-- Quiz 4 : no such A and B
quiz₄ : ∀ {A B} → ¬ (∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B)
quiz₄ (⊢` Z · ⊢` (S x≢x _)) = x≢x refl

-- Quiz 5: A ≡ B ≡ C ≡ `ℕ ⇒ `ℕ
quiz₅ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ `ℕ ⇒ `ℕ
quiz₅ = ⊢ƛ ((⊢` (S′ (S′ Z))) · ((⊢` (S′ Z)) · (⊢` Z)))

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S′ Z)) ⊢zero (⊢plus · ⊢` (S′ Z) · (⊢` (S′ (S′ (S′ Z))) · ⊢` Z · ⊢` (S′ Z))))))

⊢mulᶜ : ∀ {Γ A} → Γ ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` (S′ (S′ (S′ Z))) · (⊢` (S′ (S′ Z)) · ⊢` (S′ Z)) · ⊢` Z))))
