open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (id)
--open import Category.Monad.State
--open import Level

module main where

infix  4 _⁏_⊢_
infix  5 _⊗_↪_
infix  4 _∋_
infix  4 _∋ₛ_
infix  4 _∋ₘ_↪_
infix  5 _,_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_
infix  4 _∥_
--infix  9 _[_:=_]

Id : Set
Id = String

data Type : Set where
  _⇒_  : Type → Type → Type
  `ℕ   : Type
  `Cmd : Type

data CType : Set where
  ok : CType

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
    → Γ , A ∋ A

  S : ∀ {Γ A B}
    → Γ ∋ A → Γ , B ∋ A

data Store : Set where
  ∅   : Store
  _,_ : Store → Id → Store

data _∋ₛ_ : Store → Id → Set where
  Z : ∀ {Σ a}            → Σ , a ∋ₛ a
  S : ∀ {Σ a b} → Σ ∋ₛ a → Σ , b ∋ₛ a

mutual
  data _⁏_⊢_ : Store → Context → Type → Set where
    `_ : ∀ {Σ Γ A}
       → Γ ∋ A
       ------------
       → Σ ⁏ Γ ⊢ A

    ƛ : ∀ {Σ Γ A B}
       → Σ ⁏ Γ , A ⊢ B
       --------------------
       → Σ ⁏ Γ ⊢ A ⇒ B
    -- ⇒-E
    _·_ : ∀ {Σ Γ A B}
        → Σ ⁏ Γ ⊢ A ⇒ B   → Σ ⁏ Γ ⊢ A
        ------------------------------
        → Σ ⁏ Γ ⊢ B
    -- ℕ-I₁
    `zero : ∀ {Σ Γ}
          --------------
          → Σ ⁏ Γ ⊢ `ℕ
    -- ℕ-I₂
    `suc_ : ∀ {Σ Γ}
          → Σ ⁏ Γ ⊢ `ℕ
          ---------------
          → Σ ⁏ Γ ⊢ `ℕ
    -- ℕ-E
    case : ∀ {Σ Γ A}
         → Σ ⁏ Γ ⊢ `ℕ   → Σ ⁏ Γ ⊢ A   → Σ ⁏ Γ , `ℕ ⊢ A
         ----------------------------------------------
         → Σ ⁏ Γ ⊢ A

    μ_ : ∀ {Σ Γ A}
       → Σ ⁏ Γ , A ⊢ A
       -----------------
       → Σ ⁏ Γ ⊢ A

    cmd : ∀ {Σ Γ}
        → Σ ⁏ Γ ⊩ ok
        → Σ ⁏ Γ ⊢ `Cmd

  data _⁏_⊩_ : Store → Context → CType → Set where
    ret : ∀ {Σ Γ}
        → Σ ⁏ Γ ⊢ `ℕ
        → Σ ⁏ Γ ⊩ ok
    bnd : ∀ {Σ Γ}
        → Σ ⁏ Γ ⊢ `Cmd → Σ ⁏ Γ , `ℕ ⊩ ok
        → Σ ⁏ Γ ⊩ ok
    dcl : ∀ {Σ Γ}
        → (a : Id) → Σ ⁏ Γ ⊢ `ℕ → (Σ , a) ⁏ Γ ⊩ ok
        → Σ ⁏ Γ ⊩ ok
    get : ∀ {Σ Γ}
        → (a : Id) → Σ ∋ₛ a
        → Σ ⁏ Γ ⊩ ok
    set : ∀ {Σ Γ}
        → (a : Id) → Σ ∋ₛ a → Σ ⁏ Γ ⊢ `ℕ
        → Σ ⁏ Γ ⊩ ok

lookup : Context → ℕ → Type
lookup (Γ , A) zero    = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = Z
count {Γ , _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Σ Γ} → (n : ℕ) → Σ ⁏ Γ ⊢ lookup Γ n
# n = ` (count n)

ext : ∀ {Γ Δ}
    → (∀ {A}   → Γ ∋ A     → Δ ∋ A)
    -----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

ext' : ∀ {Σ Ω}
     → (∀ {a}   → Σ ∋ₛ a     → Ω ∋ₛ a)
     -----------------------------------
     → (∀ {a b} → Σ , b ∋ₛ a → Ω , b ∋ₛ a)
ext' ρ Z     = Z
ext' ρ (S x) = S (ρ x)

--ext' : ∀ {Σ Γ A a}
--     → Σ ⁏ Γ ⊢ A → (Σ , a) ⁏ Γ ⊢ A
--ext' (` x) = ` x
--ext' (ƛ N) = ƛ (ext' N)
--ext' (L · M) = (ext' L) · (ext' M)
--ext' `zero = `zero
--ext' (`suc M) = `suc (ext' M)
--ext' (case L M N) = case (ext' L) (ext' M) (ext' N)
--ext' (μ M) = μ (ext' M)
--ext' (cmd C) = cmd {!!}

mutual
  rename : ∀ {Σ Ω Γ Δ}
         → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
         → (∀ {A} → Γ ∋ A  → Δ ∋ A)
         ----------------------------------
         → (∀ {A} → Σ ⁏ Γ ⊢ A → Ω ⁏ Δ ⊢ A)
  rename τ ρ (` w)        = ` (ρ w)
  rename τ ρ (ƛ N)        = ƛ (rename τ (ext ρ) N)
  rename τ ρ (L · M)      = (rename τ ρ L) · (rename τ ρ M)
  rename τ ρ `zero        = `zero
  rename τ ρ (`suc M)     = `suc (rename τ ρ M)
  rename τ ρ (case L M N) = case (rename τ ρ L) (rename τ ρ M) (rename τ (ext ρ) N)
  rename τ ρ (μ M)        = μ (rename τ (ext ρ) M)
  rename τ ρ (cmd C)      = cmd (rename' τ ρ C)

--For now, A in _⁏_⊩_ must be ok.
  rename' : ∀ {Σ Ω Γ Δ}
          → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
          → (∀ {A} → Γ ∋ A  → Δ ∋ A)
          → (∀ {A} → Σ ⁏ Γ ⊩ A → Ω ⁏ Δ ⊩ A)
  rename' τ ρ (ret M)      = ret (rename τ ρ M)
  rename' τ ρ (bnd M C)    = bnd (rename τ ρ M) (rename' τ (ext ρ) C)
  rename' τ ρ (dcl x M C)  = dcl x (rename τ ρ M) (rename' (ext' τ) ρ C)
  rename' τ ρ (get x ∋x)   = get x (τ ∋x)
  rename' τ ρ (set x ∋x M) = set x (τ ∋x) (rename τ ρ M)

exts : ∀ {Σ Γ Δ}
     → (∀ {A}   →     Γ ∋ A → Σ ⁏ Δ ⊢ A)
     → (∀ {A B} → Γ , B ∋ A → Σ ⁏ Δ , B ⊢ A)
exts ρ Z     = ` Z
exts ρ (S x) = rename id S (ρ x)

exts' : ∀ {Σ Γ Δ}
      → (∀ {A}   → Γ ∋ A → Σ ⁏ Δ ⊢ A)
      → (∀ {A a} → Γ ∋ A → Σ , a ⁏ Δ ⊢ A)
exts' ρ ∋A = rename S id (ρ ∋A)

mutual
  subst : ∀ {Σ Ω Γ Δ}
        → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
        → (∀ {A} → Γ ∋ A  → Ω ⁏ Δ ⊢ A)
        -------------------------
        → (∀ {A} → Σ ⁏ Γ ⊢ A → Ω ⁏ Δ ⊢ A)
  subst τ σ (` x)        = σ x
  subst τ σ (ƛ N)        = ƛ (subst τ (exts σ) N)
  subst τ σ (L · M)      = (subst τ σ L) · (subst τ σ M)
  subst τ σ `zero        = `zero
  subst τ σ (`suc N)     = `suc (subst τ σ N)
  subst τ σ (case L M N) = case (subst τ σ L) (subst τ σ M) (subst τ (exts σ) N)
  subst τ σ (μ N)        = μ (subst τ (exts σ) N)
  subst τ σ (cmd C)      = cmd (subst' τ σ C)

--For now, A in _⁏_⊩_ must be ok.
  subst' : ∀ {Σ Ω Γ Δ}
         → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
         → (∀ {A} → Γ ∋ A → Ω ⁏ Δ ⊢ A)
         → (∀ {A} → Σ ⁏ Γ ⊩ A → Ω ⁏ Δ ⊩ A)
  subst' τ σ (ret M)      = ret (subst τ σ M)
  subst' τ σ (bnd M C)    = bnd (subst τ σ M) (subst' τ (exts σ) C)
  subst' τ σ (dcl x M C)  = dcl x (subst τ σ M) (subst' (ext' τ) (exts' σ) C)
  subst' τ σ (get x ∋x)   = get x (τ ∋x)
  subst' τ σ (set x ∋x M) = set x (τ ∋x) (subst τ σ M)


_[_] : ∀ {Σ Γ A B}
     → Σ ⁏ Γ , B ⊢ A → Σ ⁏ Γ ⊢ B
     -------------------
     → Σ ⁏ Γ ⊢ A
_[_] {Σ} {Γ} {A} {B} N M = subst {Σ} {Σ} {Γ , B} {Γ} id σ N
  where
    σ : ∀ {A} → Γ , B ∋ A → Σ ⁏ Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

_[_]c : ∀ {Σ Γ A B}
      → Σ ⁏ Γ , B ⊩ A → Σ ⁏ Γ ⊢ B
      → Σ ⁏ Γ ⊩ A
_[_]c {Σ} {Γ} {A} {B} C M = subst' {Σ} {Σ} {Γ , B} {Γ} id σ C
  where
    σ : ∀ {A} → Γ , B ∋ A → Σ ⁏ Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

data Value (Σ : Store) : ∀ {Γ A} → Σ ⁏ Γ ⊢ A → Set where
  V-ƛ    : ∀ {Γ A B} {N : Σ ⁏ Γ , A ⊢ B} → Value Σ (ƛ N)
  V-zero : ∀ {Γ} → Value Σ (`zero {Σ} {Γ})
  V-suc  : ∀ {Γ} {V : Σ ⁏ Γ ⊢ `ℕ} → Value Σ V → Value Σ (`suc V)
  V-cmd  : ∀ {Γ m} → Value Σ (cmd {Σ} {Γ} m)

infix 2 _—→_

data Step : ∀ {Σ Γ A} → (Σ ⁏ Γ ⊢ A) → (Σ ⁏ Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Σ Γ A B} {L L' : Σ ⁏ Γ ⊢ A ⇒ B} {M : Σ ⁏ Γ ⊢ A}
       → Step L L'
       → Step (L · M) (L' · M)

  ξ-·₂ : ∀ {Σ Γ A B} {V : Σ ⁏ Γ ⊢ A ⇒ B} {M M' : Σ ⁏ Γ ⊢ A}
       → Value Σ V
       → Step M M'
       → Step (V · M) (V · M')

  β-ƛ : ∀ {Σ Γ A B} {N : Σ ⁏ Γ , A ⊢ B} {W : Σ ⁏ Γ ⊢ A}
       → Value Σ W
       --------------------
       → Step ((ƛ N) · W) (N [ W ])

  ξ-suc : ∀ {Σ Γ} {M M′ : Σ ⁏ Γ ⊢ `ℕ}
        → Step M M′
        -----------------
        → Step (`suc M) (`suc M′)

  ξ-case : ∀ {Σ Γ A} {L L′ : Σ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
         → Step L L′
           -------------------------
         → Step (case L M N) (case L′ M N)

  β-zero :  ∀ {Σ Γ A} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
         -------------------
         → Step (case `zero M N) M

  β-suc : ∀ {Σ Γ A} {V : Σ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
        → Value Σ V
        ----------------------------
        → Step (case (`suc V) M N) (N [ V ])

  β-μ : ∀ {Σ Γ A} {N : Σ ⁏ Γ , A ⊢ A}
      ----------------
      → Step (μ N) (N [ μ N ])

_—→_ : ∀ {Σ Γ A} → (Σ ⁏ Γ ⊢ A) → (Σ ⁏ Γ ⊢ A) → Set
L —→ M = Step L M

data Map : Set where
  ∅     : Map
  _⊗_↪_ : ∀ {Σ Γ A} → Map → Id → Σ ⁏ Γ ⊢ A → Map

data _∋ₘ_↪_ : ∀ {Σ Γ A} → Map → Id → Σ ⁏ Γ ⊢ A → Set where
  Z : ∀ {μ x Σ Γ A} {M : Σ ⁏ Γ ⊢ A}
    → μ ⊗ x ↪ M ∋ₘ x ↪ M
  S : ∀ {μ x y Σ Γ A Ω Δ B} {M : Σ ⁏ Γ ⊢ A} {N : Ω ⁏ Δ ⊢ B}
    → μ ∋ₘ x ↪ M
    → μ ⊗ y ↪ N ∋ₘ x ↪ M

--lookupₘ : ∀ {Σ Γ A} → Map → Id → Σ ⁏ Γ ⊢ A
--lookupₘ (m ⊗ x ↪ M) y with x ≟ y
--...                      | yes _ = {!M!}
--...                      | no  _ = lookupₘ m y
--lookupₘ ∅ _ = ⊥-elim impossible
--                where postulate impossible : ⊥

data _⦂_ : Map → Store → Set where
  dom⊇ : ∀ {μ Σ}
        → (∀ {a Γ} → Σ ∋ₛ a → Σ[ V ∈ ∅ ⁏ Γ ⊢ `ℕ ] (μ ∋ₘ a ↪ V × Value ∅ V))
        → μ ⦂ Σ

data State : Set where
  _∥_ : ∀ {Σ Γ a} → Σ ⁏ Γ ⊩ a → Map → State

data Ok (Σ : Store) : State → Set where
  ok : ∀ {Γ μ} → (C : Σ ⁏ Γ ⊩ ok) → μ ⦂ Σ
     → Ok Σ (C ∥ μ)

data Final (Σ : Store) : ∀ {Γ A} → Σ ⁏ Γ ⊩ A → Map → Set where
  F-ret : ∀ {Γ V μ} → Value Σ {Γ} V → Final Σ (ret V) μ

data StepC : Store → State → State → Set where
  ξ-ret  : ∀ {Σ Γ M M' μ}
         → Step {Σ} {Γ} M M'
         → StepC Σ (ret M ∥ μ) (ret M' ∥ μ)

  ξ-bnd  : ∀ {Σ Γ M M' C μ}
         → Step {Σ} {Γ} M M'
         → StepC Σ (bnd M C ∥ μ) (bnd M' C ∥ μ)

  β-bndret : ∀ {Σ Γ V C μ}
           → Value Σ {Γ} V
           → StepC Σ (bnd (cmd (ret V)) C ∥ μ) ((C [ V ]c) ∥ μ)
  --??
  ξ-bndcmd : ∀ {Σ Γ μ μ' n} → (m m' : Σ ⁏ Γ ⊩ ok)
           → StepC Σ (m ∥ μ) (m' ∥ μ')
           → StepC Σ (bnd (cmd m) n ∥ μ) (bnd (cmd m') n ∥ μ')

  β-get : ∀ {Σ Γ μ x} {E : Σ ⁏ Γ ⊢ `ℕ}
        → {∋x : Σ ∋ₛ x} → {∋ₘx : μ ∋ₘ x ↪ E}
        → StepC Σ (get {Σ} {Γ} x ∋x ∥ μ) (ret E ∥ μ)

  ξ-set : ∀ {Σ Γ x μ} {E E' : Σ ⁏ Γ ⊢ `ℕ} → {∋x : Σ ∋ₛ x}
        → Step E E'
        → StepC Σ (set x ∋x E ∥ μ) (set x ∋x E' ∥ μ)

  β-setret : ∀ {Σ Γ x μ} {E : Σ ⁏ Γ ⊢ `ℕ} → {∋x : Σ ∋ₛ x}
           → Value Σ E
           → StepC Σ (set x ∋x E ∥ μ) (ret E ∥ μ)

  ξ-dcl₁ : ∀ {Σ Γ x μ C} {E E' : Σ ⁏ Γ ⊢ `ℕ}
         → Step E E'
         → StepC Σ (dcl x E C ∥ μ) (dcl x E' C ∥ μ)

  ξ-dcl₂ : ∀ {Σ Γ x μ μ' C C'} {E E' : Σ ⁏ Γ ⊢ `ℕ}
         → {∋x : Σ ∋ₛ x} → {∋ₘx : μ ∋ₘ x ↪ E} → {∋ₘx' : μ' ∋ₘ x ↪ E'}
         → Value Σ E
         → StepC Σ (C ∥ μ) (C' ∥ μ')
         → StepC Σ (dcl x E C ∥ μ) (dcl x E' C' ∥ μ')

  β-dclret : ∀ {Σ Γ x μ} {E : Σ ⁏ Γ ⊢ `ℕ} {E' : (Σ , x) ⁏ Γ ⊢ `ℕ}
           → Value Σ E → Value (Σ , x) E'
           → StepC Σ (dcl x E (ret E') ∥ μ) (ret E' ∥ μ)

--data _∥_—↦_∥_ : State → Store → State → Set where
--  S-ret : ∀ {M M' μ}
--        → M —→ M'
--        ------------
--        → 

--infix  2 _—↠_
--infix  1 begin_
--infixr 2 _—→⟨_⟩_
--infix  3 _∎
--
--data _—↠_ : ∀ {Σ Γ A} → (Σ ⁏ Γ ⊢ A) → (Σ ⁏ Γ ⊢ A) → Set where
--
--  _∎ : ∀ {Σ Γ A} (M : Σ ⁏ Γ ⊢ A)
--     ------
--     → M —↠ M
--
--  _—→⟨_⟩_ : ∀ {Σ Γ A} (L : Σ ⁏ Γ ⊢ A) {M N : Σ ⁏ Γ ⊢ A}
--          → L —→ M
--          → M —↠ N
--          ------
--          → L —↠ N
--
--begin_ : ∀ {Σ Γ A} {M N : Σ ⁏ Γ ⊢ A}
--  → M —↠ N
--  ------
--  → M —↠ N
--begin M—↠N = M—↠N

--data Progress {A} (M : ∅ ⊢ A) : Set where
--  done : Value M → Progress M
--  step : ∀ {N : ∅ ⊢ A} → M —→ N → Progress M
--
--progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
--progress (ƛ N) = done V-ƛ
--progress (L · M) with progress L
--...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
--...    | done V-ƛ with progress M
--...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
--...        | done VM                    =  step (β-ƛ VM)
--progress (`zero)                        =  done V-zero
--progress (`suc M) with progress M
--...    | step M—→M′                     =  step (ξ-suc M—→M′)
--...    | done VM                        =  done (V-suc VM)
--progress (case L M N) with progress L
--...    | step L—→L′                     =  step (ξ-case L—→L′)
--...    | done V-zero                    =  step (β-zero)
--...    | done (V-suc VL)                =  step (β-suc VL)
--progress (μ N)                          =  step (β-μ)
--
--data Gas : Set where
--  gas : ℕ → Gas
--
--
--data Finished {Γ A} (N : Γ ⊢ A) : Set where
--  done       : Value N → Finished N
--  out-of-gas : Finished N
--
--data Steps : ∀ {A} → ∅ ⊢ A → Set where
--  steps : ∀ {A} {L N : ∅ ⊢ A}
--        → L —↠ N → Finished N → Steps L
--
--eval : ∀ {A} → Gas → (L : ∅ ⊢ A) → Steps L
--eval (gas zero) L = steps (L ∎) out-of-gas
--eval (gas (suc x)) L with progress L
--... | done VL   = steps (L ∎) (done VL)
--... | step {M} L—→M with eval (gas x) M
--...   | steps M—↠N fin = steps (L —→⟨ L—→M ⟩ M—↠N) fin

--mutual
--  data Term : Set where
--    `_                   : Id → Term
--    ƛ_⇒_                 : Id → Term → Term
--    _·_                  : Term → Term → Term
--    `zero                : Term
--    `suc_                : Term → Term
--    case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
--    μ_⇒_                 : Id → Term → Term
--    cmd_                 : Cmd → Term
--
--  data Cmd : Set where
--    ret_     : Term → Cmd
--    bnd_←_↷_  : Id → Term → Cmd → Cmd
--    dcl_≔_↷_ : Id → Term → Cmd → Cmd
--    get_     : Id → Cmd
--    set      : Id → Term → Cmd


--Typing Judgement

--data Stat : Set where
--  ok : Stat
--
--infixl 5 _,_⦂_
--
--data Context : Set where
--  ∅     : Context
--  _,_⦂_ : Context → Id → Type → Context
--
--data Signature : Set where
--  ∅   : Signature
--  _,_ : Signature → Id → Signature
--
--data _∋ₛ_⦂_ : Signature → Id → Type → Set where
--
--infix 4 _⍮_⊢_⦂_
--infix 4 _⍮_⊩_⦂_
--
--mutual
--  data _⍮_⊩_⦂_ : Context → Signature → Cmd → Stat → Set where
--
--    ⊩ℕ : ∀ {Γ Σ N}
--       → Γ ⍮ Σ ⊢ N ⦂ `ℕ
--       -------------
--       → Γ ⍮ Σ ⊩ ret N ⦂ ok
--
--    ⊩bnd : ∀ {Γ Σ E x N}
--         → Γ ⍮ Σ ⊢ E ⦂ `Cmd → Γ , x ⦂ `ℕ ⍮ Σ ⊩ N ⦂ ok
--         ----------------------------
--         → Γ ⍮ Σ ⊩ bnd x ← E ↷ N ⦂ ok
--
--    ⊩dcl : ∀ {Γ Σ E x N}
--         → Γ ⍮ Σ ⊢ E ⦂ `Cmd → Γ , x ⦂ `ℕ ⍮ Σ ⊩ N ⦂ ok
--         ----------------------------
--         → Γ ⍮ Σ ⊩ dcl x ≔ E ↷ N ⦂ ok
--
--    ⊩get : ∀ {Γ Σ a} → Γ ⍮ Σ , a ⊩ get a ⦂ ok
--
--    ⊩set : ∀ {Γ Σ a N}
--         → Γ ⍮ Σ , a ⊢ N ⦂ `ℕ
--         ---------------------
--         → Γ ⍮ Σ , a ⊩ set a N ⦂ ok
--
--  data _⍮_⊢_⦂_ : Context → Signature → Term → Type → Set where
--    ⊢` : ∀ {Γ Σ x A}
--       → Γ ∋ x ⦂ A
--       -------------
--       → Γ ⍮ Σ ⊢ ` x ⦂ A
--
--    ⊢ƛ : ∀ {Γ Σ x N A B}
--       → Γ , x ⦂ A ⍮ Σ ⊢ N ⦂ B
--       --------------------
--       → Γ ⍮ Σ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
--    -- ⇒-E
--    _·_ : ∀ {Γ Σ L M A B}
--        → Γ ⍮ Σ ⊢ L ⦂ A ⇒ B
--        → Γ ⍮ Σ ⊢ M ⦂ A
--        -------------
--        → Γ ⍮ Σ ⊢ L · M ⦂ B
--    -- ℕ-I₁
--    ⊢zero : ∀ {Γ Σ}
--          --------------
--          → Γ ⍮ Σ ⊢ `zero ⦂ `ℕ
--    -- ℕ-I₂
--    ⊢suc : ∀ {Γ Σ M}
--         → Γ ⍮ Σ ⊢ M ⦂ `ℕ
--         ---------------
--         → Γ ⍮ Σ ⊢ `suc M ⦂ `ℕ
--    -- ℕ-E
--    ⊢case : ∀ {Γ Σ L M x N A}
--          → Γ ⍮ Σ ⊢ L ⦂ `ℕ
--          → Γ ⍮ Σ ⊢ M ⦂ A
--          → Γ , x ⦂ `ℕ ⍮ Σ ⊢ N ⦂ A
--          -------------------------------------
--          → Γ ⍮ Σ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A
--    ⊢μ : ∀ {Γ Σ x M A}
--       → Γ , x ⦂ A ⍮ Σ ⊢ M ⦂ A
--       -----------------
--       → Γ ⍮ Σ ⊢ μ x ⇒ M ⦂ A
--
--_[_:=_] : Term → Id → Term → Term
--(` x) [ y := V ] with x ≟ y
--...            | yes _ = V
--...            | no  _ = ` x
--(ƛ x ⇒ N) [ y := V ] with x ≟ y
--...                  | yes _ = ƛ x ⇒ N
--...                  | no  _ = ƛ x ⇒ N [ y := V ]
--(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
--(`zero) [ y := V ] = `zero
--(`suc M) [ y := V ] = `suc M [ y := V ]
--(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
--...                                     | yes _ = case L [ y := V ] [zero⇒ M [ y := V ]
--                                                                    |suc x ⇒ N ]
--...                                     | no  _ = case L [ y := V ] [zero⇒ M [ y := V ]
--                                                                    |suc x ⇒ N [ y := V ] ]
--(μ x ⇒ N) [ y := V ] with x ≟ y
--...                | yes _ = μ x ⇒ N
--...                | no  _ = μ x ⇒ N [ y := V ]
--
--infix 4 _—[_]→_
--
--data _—[_]→_ : Term → Signature → Term → Set where
--  ξ-·₁ : ∀ {L L′ M Σ}
--       → L —[ Σ ]→ L′
--       -----------------
--       → L · M —[ Σ ]→ L′ · M
--
--  ξ-·₂ : ∀ {V M M′ Σ}
--       → Value V → M —[ Σ ]→ M′
--       -----------------
--       → V · M —[ Σ ]→ V · M′
--
--  β-ƛ : ∀ {x N V Σ}
--      → Value V
--      ------------------------------
--      → (ƛ x ⇒ N) · V —[ Σ ]→ N [ x := V ]
--
--  ξ-suc : ∀ {M M′ Σ}
--        → M —[ Σ ]→ M′
--        ------------------
--        → `suc M —[ Σ ]→ `suc M′
--
--  ξ-case : ∀ {x L L′ M N Σ}
--         → L —[ Σ ]→ L′
--         -----------------------------------------------------------------
--         → case L [zero⇒ M |suc x ⇒ N ] —[ Σ ]→ case L′ [zero⇒ M |suc x ⇒ N ]
--
--  β-zero : ∀ {x M N Σ}
--         ----------------------------------------
--         → case `zero [zero⇒ M |suc x ⇒ N ] —[ Σ ]→ M
--
--  β-suc : ∀ {x V M N Σ}
--        → Value V
--        ---------------------------------------------------
--        → case `suc V [zero⇒ M |suc x ⇒ N ] —[ Σ ]→ N [ x := V ]
--
--  β-μ : ∀ {x M Σ}
--      ------------------------------
--      → μ x ⇒ M —[ Σ ]→ M [ x := μ x ⇒ M ]
--
--infix  2 _—↠_
--infix  1 begin_
--infixr 2 _—→⟨_⟩_
--infix  3 _∎

--data _—↠_ : Term → Term → Set where
--  _∎ : ∀ M
--     ---------
--     → M —↠ M
--
--  _—→⟨_⟩_ : ∀ L {M N}
--        → L —→ M
--        → M —↠ N
--        ---------
--        → L —↠ N
--
--begin_ : ∀ {M N}
--       → M —↠ N
--       ------
--       → M —↠ N
--begin M—↠N = M—↠N

--infix 4 Canonical_⦂_
--
--data Canonical_⦂_ : Term → Type → Set where
--  C-ƛ : ∀ {x A N B}
--      → ∅ , x ⦂ A ⊢ N ⦂ B
--      → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
--  C-zero : Canonical `zero ⦂ `ℕ
--  C-suc  : ∀ {V} → Canonical V ⦂ `ℕ → Canonical `suc V ⦂ `ℕ
--
--canonical : ∀ {V A}
--          → ∅ ⊢ V ⦂ A
--          → Value V
--          -----------
--          → Canonical V ⦂ A
--canonical (⊢` ())          ()
--canonical (⊢ƛ ⊢N)          V-ƛ        =  C-ƛ ⊢N
--canonical (⊢L · ⊢M)        ()
--canonical ⊢zero            V-zero     =  C-zero
--canonical (⊢suc ⊢V)        (V-suc VV) =  C-suc (canonical ⊢V VV)
--canonical (⊢case ⊢L ⊢M ⊢N) ()
--canonical (⊢μ ⊢M)          ()
--
--value : ∀ {M A}
--      → Canonical M ⦂ A
--      ----------------
--      → Value M
--value (C-ƛ ⊢N)    =  V-ƛ
--value C-zero      =  V-zero
--value (C-suc CM)  =  V-suc (value CM)
--
--typed : ∀ {M A}
--      → Canonical M ⦂ A
--      ---------------
--      → ∅ ⊢ M ⦂ A
--typed (C-ƛ ⊢N)    =  ⊢ƛ ⊢N
--typed C-zero      =  ⊢zero
--typed (C-suc CM)  =  ⊢suc (typed CM)
--
--
--data Progress (M : Term) : Set where
--  step : ∀ {N} → M —→ N → Progress M
--  done : Value M → Progress M
--
--progress : ∀ {M A}
--         → ∅ ⊢ M ⦂ A
--         ----------
--         → Progress M
--progress (⊢` ())
--progress (⊢ƛ ⊢N)                            =  done V-ƛ
--progress (⊢L · ⊢M) with progress ⊢L
--... | step L—→L′                            =  step (ξ-·₁ L—→L′)
--... | done VL with progress ⊢M
--...   | step M—→M′                          =  step (ξ-·₂ VL M—→M′)
--...   | done VM with canonical ⊢L VL
--...     | C-ƛ _                             =  step (β-ƛ VM)
--progress ⊢zero                              =  done V-zero
--progress (⊢suc ⊢M) with progress ⊢M
--...  | step M—→M′                           =  step (ξ-suc M—→M′)
--...  | done VM                              =  done (V-suc VM)
--progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
--... | step L—→L′                            =  step (ξ-case L—→L′)
--... | done VL with canonical ⊢L VL
--...   | C-zero                              =  step β-zero
--...   | C-suc CL                            =  step (β-suc (value CL))
--progress (⊢μ ⊢M)                            =  step β-μ
--
--preserve : ∀ {M N A}
--         → ∅ ⊢ M ⦂ A
--         → M —→ N
--         ----------
--         → ∅ ⊢ N ⦂ A
--preserve (⊢` ())
--preserve (⊢ƛ ⊢N)                 ()
--preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
--preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
--preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
--preserve ⊢zero                   ()
--preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
--preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
--preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
--preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
--preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M
--
--data Gas : Set where
--  gas : ℕ → Gas
--
--data Finished (N : Term) : Set where
--  done       : Value N → Finished N
--  out-of-gas :           Finished N
--
--data Steps (L : Term) : Set where
--  steps : ∀ {N} → L —↠ N → Finished N → Steps L
--
--eval : ∀ {L A}
--     → Gas
--     → ∅ ⊢ L ⦂ A
--     ---------
--     → Steps L
--eval {L} (gas zero)    ⊢L                             =  steps (L ∎) out-of-gas
--eval {L} (gas (suc m)) ⊢L with progress ⊢L
--... | done VL                                         =  steps (L ∎) (done VL)
--... | step L—→M with eval (gas m) (preserve ⊢L L—→M)
--...    | steps M—↠N fin                               =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
