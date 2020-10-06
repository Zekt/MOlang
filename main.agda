open import Relation.Binary.PropositionalEquality as Eq
      using (_≡_; _≢_; refl; cong; cong₂; sym; inspect)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷⁺_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Function using (id; _$_; _∘_)
--open import Category.Monad.State
--open import Level

module main where

--infix 2 _—→_
--infix 2 _⊢→_
infix  4 _⁏_⊢_
infix  4 _∋_
infix  4 _∋ₘ_
infixl 5 _▷_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_

Id : Set
Id = String

data Type : Set
data MType : Type → Set
data Context : Set

data Type where
  _⇒_  : Type → Type → Type
  `ℕ   : Type
  `Cmd : {T : Type} → (MType T) → Type

data MType where
  `ℕ : MType `ℕ

data Memory : Set where
  ∅   : Memory
  _▷_ : {T : Type} → Memory → MType T → Memory

data Context where
  ∅   : Context
  _▷_ : Context → Type → Context

variable
  ℳ 𝒩 : Memory
  Γ Δ : Context
  A B : Type
  MA : MType A
  MB : MType B

data _∋ₘ_ {T} : Memory → MType T → Set where
  Z : ℳ ▷ MA ∋ₘ MA
  S : ℳ ∋ₘ MA → ℳ ▷ MB ∋ₘ MA

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ ▷ A ∋ A
  S : ∀ {Γ A B}
    → Γ ∋ A → Γ ▷ B ∋ A

--liftType : MType → Type
--liftType `ℕ = `ℕ
--
--LiftType : MType → Type → Set
--LiftType `ℕ `ℕ = ⊤
--LiftType `ℕ (A ⇒ A₁) = ⊥
--LiftType `ℕ (`Cmd A) = ⊥


--data _∋ₛ_ : Store → Id → Set where
--  Z : ∀ {Σ a}            → Σ ▷ a ∋ₛ a
--  S : ∀ {Σ a b} → Σ ∋ₛ a → Σ ▷ b ∋ₛ a

extM : (Id → Type) → Id → Type → (Id → Type)
extM ℳ i T j with i ≟ j
extM ℳ i T j | yes _ = T
extM ℳ i T j | no _ = ℳ j

data _⁏_⊢_ : Memory → Context → Type → Set where
  `_ : Γ ∋ A
     → ℳ ⁏ Γ ⊢ A

  ƛ : ℳ ⁏ Γ ▷ A ⊢ B
    → ℳ ⁏ Γ ⊢ A ⇒ B

  -- ⇒-E
  _·_ : ℳ ⁏ Γ ⊢ A ⇒ B
      → ℳ ⁏ Γ ⊢ A
      → ℳ ⁏ Γ ⊢ B

  -- ℕ-I₁
  `zero : ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-I₂
  `suc_ : ℳ ⁏ Γ ⊢ `ℕ → ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-E
  case : ℳ ⁏ Γ ⊢ `ℕ  → ℳ ⁏ Γ ⊢ A  → ℳ ⁏ Γ ▷ `ℕ ⊢ A
       → ℳ ⁏ Γ ⊢ A

  μ_ : ℳ ⁏ Γ ▷ A ⊢ A
     → ℳ ⁏ Γ ⊢ A

  ret : ℳ ⁏ Γ ⊢ A
      → ℳ ⁏ Γ ⊢ `Cmd MA

  bnd : ℳ ⁏ Γ ⊢ `Cmd MA → ℳ ⁏ Γ ▷ A ⊢ `Cmd MB
      → ℳ ⁏ Γ ⊢ `Cmd MB

  dcl : ℳ ⁏ Γ ⊢ A → ℳ ▷ MA ⁏ Γ ⊢ `Cmd MA
      → ℳ ⁏ Γ ⊢ `Cmd MA

  get : ℳ ∋ₘ MA
      → ℳ ⁏ Γ ⊢ `Cmd MA

  set : ℳ ∋ₘ MA
      → ℳ ⁏ Γ ⊢ `ℕ
      → ℳ ⁏ Γ ⊢ `Cmd MA

lookup : Context → ℕ → Type
lookup (Γ ▷ A) zero    = A
lookup (Γ ▷ _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ ▷ _} zero    = Z
count {Γ ▷ _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : (n : ℕ) → ℳ ⁏ Γ ⊢ lookup Γ n

# n = ` (count n)

--ext : (∀ {A}   → Γ ∋ A     → Δ ∋ A)
--      -------------------------------
--    → (∀ {A B} → Γ ▷ B ∋ A → Δ ▷ B ∋ A)
--ext ρ Z     = Z
--ext ρ (S x) = S (ρ x)
--
--extₘ : (∀ {a}   → ℳ ∋ₘ a     → 𝒩 ∋ₘ a)
--     -----------------------------------
--     → (∀ {a b} → ℳ ▷ b ∋ₘ a → 𝒩 ▷ b ∋ₘ a)
--extₘ ρ Z     = Z
--extₘ ρ (S x) = S (ρ x)
--
--rename : (∀ {A} → Γ ∋ A  → Δ ∋ A)
--       ----------------------------------
--       → (∀ {A} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Δ ⊢ A)
--rename ρ (` w)        = ` (ρ w)
--rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
--rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
--rename ρ `zero        = `zero
--rename ρ (`suc M)     = `suc (rename ρ M)
--rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
--rename ρ (μ M)        = μ (rename (ext ρ) M)
--rename ρ (ret N)      = ret (rename ρ N)
--rename ρ (bnd E C)    = bnd (rename ρ E) (rename (ext ρ) C)
--rename ρ (dcl N C)    = dcl (rename ρ N) (rename ρ C)
--rename ρ (get a)      = get a
--rename ρ (set a N)    = set a (rename ρ N)
--
--renameₘ : (∀ {M} → ℳ ∋ₘ M  → 𝒩 ∋ₘ M)
--        ----------------------------------
--        → (∀ {A} → ℳ ⁏ Γ ⊢ A → 𝒩 ⁏ Γ ⊢ A)
--renameₘ σ (` x)        = ` x
--renameₘ σ (ƛ N)        = ƛ (renameₘ σ N)
--renameₘ σ (L · M)      = (renameₘ σ L) · renameₘ σ M
--renameₘ σ `zero        = `zero
--renameₘ σ (`suc M)     = `suc renameₘ σ M
--renameₘ σ (case L M N) = case (renameₘ σ L) (renameₘ σ M) (renameₘ σ N)
--renameₘ σ (μ M)        = μ (renameₘ σ M)
--renameₘ σ (ret N)      = ret (renameₘ σ N)
--renameₘ σ (bnd E C)    = bnd (renameₘ σ E) (renameₘ σ C)
--renameₘ σ (dcl N C)    = dcl (renameₘ σ N) (renameₘ (extₘ σ) C)
--renameₘ σ (get a)      = get (σ a)
--renameₘ σ (set a N)    = set (σ a) (renameₘ σ N)

------For now, A in _⁏_⊩_ must be ok.
----  rename' : ∀ {Σ Ω Γ Δ}
----          → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
----          → (∀ {A} → Γ ∋ A  → Δ ∋ A)
----          → (∀ {A} → Σ ⁏ Γ ⊩ A → Ω ⁏ Δ ⊩ A)
----  rename' τ ρ (ret M)      = ret (rename τ ρ M)
----  rename' τ ρ (bnd M C)    = bnd (rename τ ρ M) (rename' τ (ext ρ) C)
----  rename' τ ρ (dcl x M C)  = dcl x (rename τ ρ M) (rename' (ext' τ) ρ C)
----  rename' τ ρ (get x ∋x)   = get x (τ ∋x)
----  rename' τ ρ (set x ∋x M) = set x (τ ∋x) (rename τ ρ M)
----
--exts : (∀ {A}   →     Γ ∋ A → ℳ ⁏ Δ ⊢ A)
--     → (∀ {A B} → Γ ▷ B ∋ A → ℳ ⁏ Δ ▷ B ⊢ A)
--exts ρ Z     = ` Z
--exts ρ (S x) = rename S (ρ x)
--
--exts' : ∀ {M}
--      → ℳ ⁏ Δ ⊢ A
--      → ℳ ▷ M ⁏ Δ ⊢ A
--exts' σ = renameₘ S σ
--
--extsₘ : (∀ {M}   →     ℳ ∋ₘ M  → 𝒩 ⁏ Γ ⊢ `Cmd M)
--      → (∀ {M N} → ℳ ▷ N ∋ₘ M  → 𝒩 ▷ N ⁏ Γ ⊢ `Cmd M)
--extsₘ σ Z = get Z
--extsₘ σ (S x) = renameₘ S (σ x)
--
--subst : (∀ {A} → Γ ∋ A → ℳ ⁏ Δ ⊢ A)
--       ------------------------
--      → (∀ {A} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Δ ⊢ A)
--subst σ (` x)        = σ x
--subst σ (ƛ N)        = ƛ (subst (exts σ) N)
--subst σ (L · M)      = (subst σ L) · (subst σ M)
--subst σ `zero        = `zero
--subst σ (`suc N)     = `suc (subst σ N)
--subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
--subst σ (μ N)        = μ (subst (exts σ) N)
--subst σ (ret N)      = ret (subst σ N)
--subst σ (bnd C D)    = bnd (subst σ C) (subst (exts σ) D)
--subst σ (dcl N C)    = dcl (subst σ N) (subst (exts' ∘ σ) C)
--subst σ (get a)      = get a
--subst σ (set a N)    = set a (subst σ N)
--
--_[_] : ℳ ⁏ Γ ▷ B ⊢ A → ℳ ⁏ Γ ⊢ B
--     → ℳ ⁏ Γ ⊢ A
--_[_] {ℳ} {Γ} {B} {A} N M = subst σ N
--  where
--    σ : ∀ {A} → Γ ▷ B ∋ A → ℳ ⁏ Γ ⊢ A
--    σ Z     = M
--    σ (S x) = ` x
--
--data Value : ℳ ⁏ Γ ⊢ A → Set where
--  V-ƛ    : {N : ℳ ⁏ Γ ▷ A ⊢ B} → Value N → Value (ƛ N)
--  V-zero : Value {ℳ} {Γ} `zero
--  V-suc  : {V : ℳ ⁏ Γ ⊢ `ℕ} → Value V → Value (`suc V)
--  V-ret  : {V : ℳ ⁏ Γ ⊢ A} → Value V → Value (ret V)
--
--shrink : (E : ℳ ▷ `ℕ ⁏ Γ ⊢ A) → Value E → ℳ ⁏ Γ ⊢ A
--shrink (ƛ E) (V-ƛ VE) = ƛ (shrink E VE)
--shrink `zero VE = `zero
--shrink (`suc E) (V-suc VE) = shrink E VE
--shrink (ret E) (V-ret VE) = ret (shrink E VE)
--
--data Step : {ℳ : Memory} {Γ : Context} {A : Type} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Γ ⊢ A → Set where
--  ξ-·₁ : {L L' : ℳ ⁏ Γ ⊢ A ⇒ B} {M : ℳ ⁏ Γ ⊢ A}
--       → Step L L'
--       → Step (L · M) (L' · M)
--
--  ξ-·₂ : {V : ℳ ⁏ Γ ⊢ A ⇒ B} {M M' : ℳ ⁏ Γ ⊢ A}
--       → Value V
--       → Step M M'
--       → Step (V · M) (V · M')
--
--  β-ƛ : ∀ {N : ℳ ⁏ Γ ▷ A ⊢ B} {W : ℳ ⁏ Γ ⊢ A}
--      → Value W
--      → Step ((ƛ N) · W) (N [ W ])
--
--  ξ-ƛ : ∀ {M M' : ℳ ⁏ Γ ▷ A ⊢ B}
--      → Step M M'
--      → Step (ƛ M) (ƛ M')
--
--  ξ-suc : {M M′ : ℳ ⁏ Γ ⊢ `ℕ}
--        → Step M M′
--        → Step (`suc M) (`suc M′)
--
--  ξ-case : {L L′ : ℳ ⁏ Γ ⊢ `ℕ} {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
--         → Step L L′
--         → Step (case L M N) (case L′ M N)
--
--  β-zero :  {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
--         → Step (case `zero M N) M
--
--  β-suc : {V : ℳ ⁏ Γ ⊢ `ℕ} {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
--        → Value V
--        → Step (case (`suc V) M N) (N [ V ])
--
--  β-μ : {N : ℳ ⁏ Γ ▷ A ⊢ A}
--      → Step (μ N) (N [ μ N ])
--
--  ξ-ret  : ∀ {M M' : ℳ ⁏ Γ ⊢ A}
--         → Step M M'
--         → Step (ret M) (ret M')
--
--  ξ-bnd  : ∀ {M M' : ℳ ⁏ Γ ⊢ `Cmd E} {C : ℳ ⁏ Γ ▷ A ⊢ `Cmd F}
--         → Step M M'
--         → Step (bnd M C) (bnd M' C)
--
--  β-bndret : ∀ {V : ℳ ⁏ Γ ⊢ A} {C : ℳ ⁏ Γ ▷ A ⊢ `Cmd E}
--           → Value V
--           → Step (bnd (ret V) C) (C [ V ])
--
--  β-get : ∀ {x} {E}
--        → Step (get x) (ret {ℳ} {Γ} {A} E)
--
--  ξ-set : ∀ {Eₘ} {x : ℳ ∋ₘ Eₘ} {E} {E'}
--        → Step {ℳ} {Γ} E E'
--        → Step (set x E) (set x E')
--
--  β-setret : ∀ {x} {E}
--           → Step {ℳ} {Γ} (set x E) (ret E)
--
--  ξ-dcl₁ : ∀ {E E' C}
--         → Step {ℳ} {Γ} E E'
--         → Step (dcl E C) (dcl E' C)
--
--  ξ-dcl₂ : ∀ {C C' E₁ E₂}
--         → Step C C'
--         → Step {ℳ} {Γ} (dcl E₁ C) (dcl E₂ C')
--
--  β-dclret : ∀ {E : ℳ ⁏ Γ ⊢ A} {E' : ℳ ▷ `ℕ ⁏ Γ ⊢ `ℕ}
--           → (VE' : Value E')
--           → Step (dcl E (ret E')) (ret (shrink E' VE'))
--
--_—→_ : ∀ (L M : ℳ ⁏ Γ ⊢ A) → Set
--L —→ M = Step L M
--
--data Progress (M : ℳ ⁏ Γ ⊢ A) : Set where
--  done : Value M → Progress M
--  step : ∀ {M' : ℳ ⁏ Γ ⊢ A}
--       → Step M M'
--       → Progress M
--
--progress : (M : ℳ ⁏ Γ ⊢ A) → Progress M
--
--progress (ƛ M) with progress M
--... | step M→M' = step (ξ-ƛ M→M')
--... | done VM = done (V-ƛ VM)
--
--
--progress (L · M) with progress L
--... | step L—→L′        = step (ξ-·₁ L—→L′)
--... | done (V-ƛ VL) with progress M
--...   | step M—→M′      = step (ξ-·₂ (V-ƛ VL) M—→M′)
--...   | done VM = step (β-ƛ VM)
--
--progress `zero = done V-zero
--
--progress (`suc M) with progress M
--... | step M—→M′ = step (ξ-suc M—→M′)
--... | done VM    = done (V-suc VM)
--
--progress (case L M N) with progress L
--... | step L—→L′      = step (ξ-case L—→L′)
--... | done V-zero     = step β-zero
--... | done (V-suc VL) = step (β-suc VL)
--
--progress (μ M) = step β-μ
--
--progress (ret M) with progress M
--... | step M—→M′ = step (ξ-ret M—→M′)
--... | done VM    = done (V-ret VM)
--
--progress (bnd C₁ C₂) with progress C₁
--... | step C₁—→C₁′    = step (ξ-bnd C₁—→C₁′)
--... | done (V-ret VE) = {!!}
--
--progress (dcl E C) with progress E
--... | step E—→E' = step (ξ-dcl₁ E—→E')
--... | done VE with progress C
--...   | step C—→C'      = step (ξ-dcl₂ C—→C')
--...   | done (V-ret VC) = step {!β-dclret VC!}
--with weakenM {a = a} {VE = VE} C—→C'
--...     | _ , _ , _ , VE₂ , ∋ₘa , stp
--          = step (ξ-dcl₂ {VE₁ = VE} {VE₂ = VE₂} (EqV-eq VE) (EqV-eq VE₂) ∋ₘa stp)
-- step (ξ-dcl₂ {VE₁ = {!!}} {!!} {!!} C—→C')

--progress (get a) m = {!!} --let ⟨ E , VE ⟩ = lookupₘ m a
                      ----in step (β-get {VE = VE} (EqV-eq VE))
--
--progress (set a E) m with progress E m
--... | step E—→E′      = step (ξ-set E—→E′)
--... | done (F-val VE) = step (β-setret {VE' = VE} VE (EqV-eq VE))
--
--infix  2 _—↠_ _—↣_
--infix  1 start_
--infixr 2 _—→⟨_⟩_
--infixr 2 _—↦⟨_⟩_
--infix  3 _end
--
--data _—↠_ : ∀ {Σ Γ A} → (Σ ⁏ Γ ⊢ A) → (Σ ⁏ Γ ⊢ A) → Set where
--
--  _end : ∀ {Σ Γ A} (M : Σ ⁏ Γ ⊢ A)
--       ------
--       → M —↠ M
--
--  _—→⟨_⟩_ : ∀ {Σ Γ A} (L : Σ ⁏ Γ ⊢ A) {M N : Σ ⁏ Γ ⊢ A}
--          → L —→ M
--          → M —↠ N
--          ------
--          → L —↠ N
--
--start_ : ∀ {Σ Γ A} {M N : Σ ⁏ Γ ⊢ A}
--       → M —↠ N
--       ------
--       → M —↠ N
--start M—↠N = M—↠N
--
--data _—↣_ : ∀ {Σ Γ A} → State Σ Γ A → State Σ Γ A → Set where
--  _stop : ∀ {Σ Γ A} (S : State Σ Γ A)
--        → S —↣ S
--
--
--          → StepS Σ S T
--          → T —↣ U
--          → S —↣ U
--
--run_ : ∀ {Σ Γ A} {S T : State Σ Γ A}
--     → S —↣ T
--     → S —↣ T
--run S—↣T = S—↣T
--
--data Gas : Set where
--  gas : ℕ → Gas
--
--
--data Finished {Σ Γ A} (N : Σ ⁏ Γ ⊢ A) : Set where
--  done       : Value Σ N → Finished N
--  out-of-gas : Finished N
--
--data Finished' {Σ Γ A} (S : State Σ Γ A) : Set where
--  done       : Final Σ S → Finished' S
--  out-of-gas : Finished' S
--
--data Steps : ∀ {Σ A} → Σ ⁏ ∅ ⊢ A → Set where
--  steps : ∀ {Σ A} {L N : Σ ⁏ ∅ ⊢ A}
--        → L —↠ N → Finished N → Steps L
--
--data Steps' : ∀ {Σ A} → State Σ ∅ A → Set where
--  steps : ∀ {Σ A} {S T : State Σ ∅ A}
--        → S —↣ T → Finished' T → Steps' S
--
--data EvalTo : ∀ {Σ} → State Σ ∅ ok → State Σ ∅ ok → Set where
--  evalto : ∀ {Σ} → {S T : State Σ ∅ ok} → S —↣ T → Final Σ T → EvalTo S T
--
--eval : ∀ {Σ A} → Gas → (L : Σ ⁏ ∅ ⊢ A) → Steps L
--eval (gas zero) L = steps (L end) out-of-gas
--eval (gas (suc x)) L with progress L
--... | done VL   = steps (L end) (done VL)
--... | step {M} L—→M with eval (gas x) M
--...   | steps M—↠N fin = steps (L —→⟨ L—→M ⟩ M—↠N) fin
--
--eval' : ∀ {Σ} → Gas → (S : State Σ ∅ ok) → Steps' S
--eval' (gas zero) s = steps (s stop) out-of-gas
--eval' (gas (suc x)) s@(C ⟪ prf ⟫ m) with progress' C prf m
--... | done FS = steps (s stop) (done FS)
--... | step {C' = C'} {μ' = μ'} {Σ⊆Ω' = Σ⊆Ω'} S—↦T with eval' (gas x) (C' ⟪ Σ⊆Ω' ⟫ μ')
--...   | steps T—↣U fin = steps (s —↦⟨ S—↦T ⟩ T—↣U) fin
--
----data ProgramList (Σ : Store) : Set where
----  single : ∀ {Ω Γ a} → State Σ Γ a → ProgramList Σ
----  multi  : ∀ {Ω Γ a} → State Σ Γ a →
--
--ProgramList : Store → Set
--ProgramList Σ = List (Σ ⁏ ∅ ⊩ ok)
--
----Concurrent States
--data CState (Σ : Store) : Set where
--  _⟦_⟧_ : ∀ {Ω} → ProgramList Σ → Σ ⊆ Ω → Map Ω → CState Σ
--
--data StepCS {Σ : Store} : CState Σ → CState Σ → Set where
--  head : {C C' : Σ ⁏ ∅ ⊩ ok} {μ μ' : Map Σ} {Cs : ProgramList Σ}
--       → StepS Σ (C ⟪ id ⟫ μ) (C' ⟪ id ⟫ μ')
--       → StepCS ((C ∷ Cs) ⟦ id ⟧ μ) ((C' ∷ Cs) ⟦ id ⟧ μ')
--  tail : ∀ {C : Σ ⁏ ∅ ⊩ ok} {μ μ' : Map Σ} {Cs Cs' : ProgramList Σ}
--       → StepCS (Cs ⟦ id ⟧ μ) (Cs' ⟦ id ⟧ μ')
--       → StepCS ((C ∷ Cs) ⟦ id ⟧ μ) ((C ∷ Cs') ⟦ id ⟧ μ')
--
--
--data StepCS* : ∀ {Σ} → CState Σ → CState Σ → Set where
--  _stop : ∀ {Σ} (S : CState Σ)
--        → StepCS* S S
--
--  _—↦⟨_⟩_ : ∀ {Σ} (S : CState Σ) → {T U : CState Σ}
--          → StepCS S T
--          → StepCS* T U
--          → StepCS* S U
--
--data Final* (Σ : Store) : CState Σ → Set where
--  onedone : ∀ {C : Σ ⁏ ∅ ⊩ ok} {μ : Map Σ}
--          → Final  Σ (C ⟪ id ⟫ μ)
--          → Final* Σ ((C ∷ []) ⟦ id ⟧ μ)
--  alldone : ∀ {C : Σ ⁏ ∅ ⊩ ok} {Cs : ProgramList Σ} {μ : Map Σ}
--          → Final  Σ (C ⟪ id ⟫ μ) → Final* Σ (Cs ⟦ id ⟧ μ)
--          → Final* Σ ((C ∷ Cs) ⟦ id ⟧ μ)
