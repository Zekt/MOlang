open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
--open import Category.Monad.State
--open import Level

module main where


infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_
infix  9  _[_:=_]

Id : Set
Id = String

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

data Value : Term → Set where
  V-ƛ    : ∀ {x N}         → Value (ƛ x ⇒ N)
  V-zero :                   Value `zero
  V-suc  : ∀ {V} → Value V → Value (`suc V)

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  ƛ x ⇒ N
... | no  _          =  ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   =  L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   =  `zero
(`suc M) [ y := V ]  =  `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _          =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          =  μ x ⇒ N
... | no  _          =  μ x ⇒ N [ y := V ]

--Typing Judgement
infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

infixl 5 _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
  -----------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y → Γ ∋ x ⦂ A
  -----------------------
    → Γ , y ⦂ B ∋ x ⦂ A

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢` : ∀ {Γ x A}
     → Γ ∋ x ⦂ A
     -------------
     → Γ ⊢ ` x ⦂ A

  ⊢ƛ : ∀ {Γ x N A B}
     → Γ , x ⦂ A ⊢ N ⦂ B
     --------------------
     → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
     -- ⇒-E
  _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ⦂ A ⇒ B
      → Γ ⊢ M ⦂ A
      -------------
      → Γ ⊢ L · M ⦂ B
  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
        --------------
        → Γ ⊢ `zero ⦂ `ℕ
  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
       → Γ ⊢ M ⦂ `ℕ
       ---------------
       → Γ ⊢ `suc M ⦂ `ℕ
  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
        → Γ ⊢ L ⦂ `ℕ
        → Γ ⊢ M ⦂ A
        → Γ , x ⦂ `ℕ ⊢ N ⦂ A
        -------------------------------------
        → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A
  ⊢μ : ∀ {Γ x M A}
     → Γ , x ⦂ A ⊢ M ⦂ A
     -----------------
     → Γ ⊢ μ x ⇒ M ⦂ A
