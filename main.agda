open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; cong₂; sym) renaming (subst to subsT)
open Eq.≡-Reasoning using (begin_; _≡⟨_⟩_; _≡⟨⟩_; _∎)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
open import Data.List.NonEmpty using (List⁺; _∷⁺_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (id; _$_; _∘_)
--open import Category.Monad.State
--open import Level

module main where

infix 2 _—→_
--infix 2 _⊢→_
infix  4 _⊢_
infix  5 _⊗_↪_
infix  4 _∋_
infix  4 _∋ₛ_
infix  4 _∋ₘ_↪_
infixl 5 _,_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_
infix  4 _⟪_⟫_
--infix  9 _[_:=_]


Id : Set
Id = String

data CType : Set where
  ok : CType

data Type : Set
data Context : Set
data _⊢_ : Context → Type → Set

data Context where
  ∅   : Context
  _,_ : Context → Type → Context

data Type where
  _⇒_  : Type → Type → Type
  `ℕ   : Type
  `Cmd : (Id → ∅ ⊢ `ℕ) → Type → Type


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

extM : (Id → ∅ ⊢ `ℕ) → Id → ∅ ⊢ `ℕ → (Id → ∅ ⊢ `ℕ)
extM ℳ i T j with i ≟ j
extM ℳ i T j | yes _ = ℳ i
extM ℳ i T j | no _ = T

data _⊢_  where
  `_ : ∀ {Γ A}
     → Γ ∋ A
     ------------
     → Γ ⊢ A

  ƛ : ∀ {Γ A B}
     → Γ , A ⊢ B
     --------------------
     → Γ ⊢ A ⇒ B
  -- ⇒-E
  _·_ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B   → Γ ⊢ A
      ------------------------------
      → Γ ⊢ B
  -- ℕ-I₁
  `zero : ∀ {Γ}
        --------------
        → Γ ⊢ `ℕ
  -- ℕ-I₂
  `suc_ : ∀ {Γ}
        → Γ ⊢ `ℕ
        ---------------
        → Γ ⊢ `ℕ
  -- ℕ-E
  case : ∀ {Γ A}
       → Γ ⊢ `ℕ   → Γ ⊢ A   → Γ , `ℕ ⊢ A
       ------------------------------------------
       → Γ ⊢ A

  μ_ : ∀ {Γ A}
     → Γ , A ⊢ A
     -------------
     → Γ ⊢ A

  ret : ∀ {Γ ℳ}
     → Γ ⊢ `ℕ
     → Γ ⊢ `Cmd ℳ `ℕ

  bnd : ∀ {Γ ℳ}
      → Γ ⊢ `Cmd ℳ `ℕ → Γ , `ℕ ⊢ `Cmd ℳ `ℕ
      → Γ ⊢ `Cmd ℳ `ℕ

  dcl : ∀ {Γ ℳ}
      → (a : Id) → (E : {!!} ⊢ `ℕ) → Γ ⊢ `Cmd ℳ `ℕ
      → Γ ⊢ `Cmd (extM ℳ a E) `ℕ

  get : ∀ {Γ ℳ}
      → (a : Id) --→ Σ ∋ₛ a
      → Γ ⊢ `Cmd ℳ `ℕ

  set : ∀ {Γ ℳ}
      → (a : Id) → (E : ∅ ⊢ `ℕ)
      → Γ ⊢ `Cmd (extM ℳ a E) `ℕ

--    cmd : ∀ {Σ Γ}
--         → Σ ⁏ Γ ⊩ ok
--         → Σ ⁏ Γ ⊢ `Cmd ok

--  data _⁏_⊩_ : Store → Context → CType → Set where
--    par : ∀ {Σ Γ}
--        → Σ ⁏ Γ ⊩ ok → Σ ⁏ Γ ⊩ ok
--        → Σ ⁏ Γ ⊩ ok

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

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n

# n = ` (count n)

ext : ∀ {Γ Δ}
    → (∀ {A}   → Γ ∋ A     → Δ ∋ A)
    -----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

--ext' : ∀ {Σ Ω}
--     → (∀ {a}   → Σ ∋ₛ a     → Ω ∋ₛ a)
--     -----------------------------------
--     → (∀ {a b} → Σ , b ∋ₛ a → Ω , b ∋ₛ a)
--ext' ρ Z     = Z
--ext' ρ (S x) = S (ρ x)
--
--mutual
rename : ∀ {Γ Δ}
       → (∀ {A} → Γ ∋ A  → Δ ∋ A)
       ----------------------------------
       → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` w)        = ` (ρ w)
rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
rename ρ `zero        = `zero
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ M)        = μ (rename (ext ρ) M)
rename ρ (ret N) = ret (rename ρ N)
rename ρ (bnd E C) = bnd (rename ρ E) (rename (ext ρ) C)
rename ρ (dcl a N C) = {!!}
rename ρ (get a) = {!!}
rename ρ (set a N) = {!!}
--rename ρ (cmd C)      = cmd (rename' ρ C)
--
----For now, A in _⁏_⊩_ must be ok.
--  rename' : ∀ {Σ Ω Γ Δ}
--          → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
--          → (∀ {A} → Γ ∋ A  → Δ ∋ A)
--          → (∀ {A} → Σ ⁏ Γ ⊩ A → Ω ⁏ Δ ⊩ A)
--  rename' τ ρ (ret M)      = ret (rename τ ρ M)
--  rename' τ ρ (bnd M C)    = bnd (rename τ ρ M) (rename' τ (ext ρ) C)
--  rename' τ ρ (dcl x M C)  = dcl x (rename τ ρ M) (rename' (ext' τ) ρ C)
--  rename' τ ρ (get x ∋x)   = get x (τ ∋x)
--  rename' τ ρ (set x ∋x M) = set x (τ ∋x) (rename τ ρ M)
--
--exts : ∀ {Σ Γ Δ}
--     → (∀ {A}   →     Γ ∋ A → Σ ⁏ Δ ⊢ A)
--     → (∀ {A B} → Γ , B ∋ A → Σ ⁏ Δ , B ⊢ A)
--exts ρ Z     = ` Z
--exts ρ (S x) = rename id S (ρ x)
--
--exts' : ∀ {Σ Γ Δ}
--      → (∀ {A}   → Γ ∋ A → Σ ⁏ Δ ⊢ A)
--      → (∀ {A a} → Γ ∋ A → Σ , a ⁏ Δ ⊢ A)
--exts' ρ ∋A = rename S id (ρ ∋A)
--
--mutual
--  subst : ∀ {Σ Ω Γ Δ}
--        → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
--        → (∀ {A} → Γ ∋ A  → Ω ⁏ Δ ⊢ A)
--        -------------------------
--        → (∀ {A} → Σ ⁏ Γ ⊢ A → Ω ⁏ Δ ⊢ A)
--  subst τ σ (` x)        = σ x
--  subst τ σ (ƛ N)        = ƛ (subst τ (exts σ) N)
--  subst τ σ (L · M)      = (subst τ σ L) · (subst τ σ M)
--  subst τ σ `zero        = `zero
--  subst τ σ (`suc N)     = `suc (subst τ σ N)
--  subst τ σ (case L M N) = case (subst τ σ L) (subst τ σ M) (subst τ (exts σ) N)
--  subst τ σ (μ N)        = μ (subst τ (exts σ) N)
--  subst τ σ (cmd C)      = cmd (subst' τ σ C)
--
----For now, A in _⁏_⊩_ must be ok.
--  subst' : ∀ {Σ Ω Γ Δ}
--         → (∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a)
--         → (∀ {A} → Γ ∋ A → Ω ⁏ Δ ⊢ A)
--         → (∀ {A} → Σ ⁏ Γ ⊩ A → Ω ⁏ Δ ⊩ A)
--  subst' τ σ (ret M)      = ret (subst τ σ M)
--  subst' τ σ (bnd M C)    = bnd (subst τ σ M) (subst' τ (exts σ) C)
--  subst' τ σ (dcl x M C)  = dcl x (subst τ σ M) (subst' (ext' τ) (exts' σ) C)
--  subst' τ σ (get x ∋x)   = get x (τ ∋x)
--  subst' τ σ (set x ∋x M) = set x (τ ∋x) (subst τ σ M)
--
--
--_[_] : ∀ {Σ Γ A B}
--     → Σ ⁏ Γ , B ⊢ A → Σ ⁏ Γ ⊢ B
--     -------------------
--     → Σ ⁏ Γ ⊢ A
--_[_] {Σ} {Γ} {A} {B} N M = subst {Σ} {Σ} {Γ , B} {Γ} id σ N
--  where
--    σ : ∀ {A} → Γ , B ∋ A → Σ ⁏ Γ ⊢ A
--    σ Z     = M
--    σ (S x) = ` x
--
--_[_]c : ∀ {Σ Γ A B}
--        → Σ ⁏ Γ , B ⊩ A → Σ ⁏ Γ ⊢ B
--      → Σ ⁏ Γ ⊩ A
--_[_]c {Σ} {Γ} {A} {B} C M = subst' {Σ} {Σ} {Γ , B} {Γ} id σ C
--  where
--    σ : ∀ {A} → Γ , B ∋ A → Σ ⁏ Γ ⊢ A
--    σ Z     = M
--    σ (S x) = ` x
--
data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ    : ∀ {Γ A B} {N : Γ , A ⊢ B} → Value (ƛ N)
  V-zero : ∀ {Γ} → Value (`zero {Γ})
  V-suc  : ∀ {Γ} {V : Γ ⊢ `ℕ} → Value V → Value (`suc V)
  --V-cmd  : ∀ {Γ m} → Value Σ (cmd {Σ} {Γ} m)


data Step : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ξ-·₁ : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
       → Step L L'
       → Step (L · M) (L' · M)

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
       → Value V
       → Step M M'
       → Step (V · M) (V · M')

--  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
--       → Value W
--       --------------------
--       → Step ((ƛ N) · W) (N [ W ])
--
--  ξ-suc : ∀ {Σ Γ} {M M′ : Σ ⁏ Γ ⊢ `ℕ}
--        → Step M M′
--        -----------------
--        → Step (`suc M) (`suc M′)
--
--  ξ-case : ∀ {Σ Γ A} {L L′ : Σ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
--         → Step L L′
--           -------------------------
--         → Step (case L M N) (case L′ M N)
--
--  β-zero :  ∀ {Σ Γ A} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
--         -------------------
--         → Step (case `zero M N) M
--
--  β-suc : ∀ {Σ Γ A} {V : Σ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ Γ ⊢ A} {N : Σ ⁏ Γ , `ℕ ⊢ A}
--        → Value Σ V
--        ----------------------------
--        → Step (case (`suc V) M N) (N [ V ])
--
--  β-μ : ∀ {Σ Γ A} {N : Σ ⁏ Γ , A ⊢ A}
--      ----------------
--      → Step (μ N) (N [ μ N ])
--
--_—→_ : ∀ {Σ Γ A} → (Σ ⁏ Γ ⊢ A) → (Σ ⁏ Γ ⊢ A) → Set
--L —→ M = Step L M
--
--data Map : Store → Set where
--  ∅     : Map ∅
--  _⊗_↪_ : ∀ {Σ} → Map Σ → (x : Id) → Σ[ E ∈ (Σ , x) ⁏ ∅ ⊢ `ℕ ] Value (Σ , x) E → Map (Σ , x)
--
--_⊆_ : Store → Store → Set
--Σ ⊆ Ω = ∀ {a} → Σ ∋ₛ a → Ω ∋ₛ a
--
--renameN : ∀ {Σ Ω Γ} → Σ[ E ∈ Σ ⁏ Γ ⊢ `ℕ ] Value Σ E → Σ[ E' ∈ Ω ⁏ Γ ⊢ `ℕ ] Value Ω E'
--renameN ⟨ `zero , V-zero ⟩ = ⟨ `zero , V-zero ⟩
--renameN ⟨ `suc E , V-suc VE ⟩ with renameN ⟨ E , VE ⟩
--... | ⟨ E' , VE' ⟩ = ⟨ `suc E' , V-suc VE' ⟩
--
--ide : ∀ {Σ Ω : Store} {Γ : Context} {EVE : Σ[ E ∈ Σ ⁏ Γ ⊢ `ℕ ] Value Σ E}
--    → renameN {Ω} {Σ} {Γ} (renameN {Σ} {Ω} {Γ} EVE) ≡ EVE
--ide {EVE = ⟨ `zero , V-zero ⟩} = refl
--ide {Σ} {Ω} {Γ} {EVE = ⟨ `suc E , V-suc VE ⟩}
--           = let EVE' = renameN {Σ} {Ω} {Γ} ⟨ E , VE ⟩
--                 ⟨ E'' , VE'' ⟩ = renameN {Ω} {Σ} {Γ} EVE'
--             in  begin
--                  ⟨ `suc E'' , V-suc VE'' ⟩
--                 ≡⟨ cong (λ {(⟨ e , ve ⟩) → ⟨ `suc e , V-suc ve ⟩}) (ide {Σ = Σ} {Ω = Ω} {EVE = ⟨ E , VE ⟩})  ⟩
--                  ⟨ `suc E , V-suc VE ⟩
--                 ∎
--
--eqN : ∀ {Σ Ω Γ} {E : Ω ⁏ Γ ⊢ `ℕ} {VE : Value Ω E}
--    → renameN {Σ} {Ω} {Γ} ⟨ (proj₁ $ renameN {Ω} {Σ} {Γ} ⟨ E , VE ⟩) , (proj₂ $ renameN {Ω} {Σ} {Γ} ⟨ E , VE ⟩) ⟩ ≡ ⟨ E , VE ⟩
--eqN {Σ} {Ω} {Γ} {E} {VE} = let ⟨ E' , VE' ⟩ = renameN {Ω} {Σ} {Γ} ⟨ E , VE ⟩
--                               ⟨ E'' , VE'' ⟩ = renameN {Σ} {Ω} {Γ} ⟨ E' , VE' ⟩
--                           in begin ⟨ E'' , VE'' ⟩ ≡⟨ ide ⟩ ⟨ E , VE ⟩ ∎
--
--data _∋ₘ_↪_ : ∀ {Σ} → Map Σ → (x : Id) →  Σ[ E ∈ Σ ⁏ ∅ ⊢ `ℕ ] Value Σ E → Set where
--  Z : ∀ {x Σ} {μ : Map Σ} { EVE : Σ[ E ∈ (Σ , x) ⁏ ∅ ⊢ `ℕ ] Value (Σ , x) E}
--    → μ ⊗ x ↪ EVE ∋ₘ x ↪ EVE
--  S : ∀ {x y Σ} {μ : Map Σ} {MVM : Σ[ M ∈ Σ ⁏ ∅ ⊢ `ℕ ] Value Σ M} → {NVN : Σ[ N ∈ (Σ , y) ⁏ ∅ ⊢ `ℕ ] Value (Σ , y) N}
--    → μ ∋ₘ x ↪ MVM
--    → μ ⊗ y ↪ NVN ∋ₘ x ↪ renameN MVM
--
--force : ∀ {Σ x y} → Σ , y ∋ₛ x → ¬ x ≡ y → Σ ∋ₛ x
--force Z np       = ⊥-elim (np refl)
--force (S ∋ₛx) np = ∋ₛx
--
--here : ∀ {x y Σ} {μ : Map Σ} {EVE : ∃[ E ] Value (Σ , y) E} → x ≡ y → _⊗_↪_ {Σ} μ y EVE ∋ₘ x ↪ EVE
--here refl = Z
--
--lookupₘ : ∀ {Σ} → (μ : Map Σ) → (x : Id) → (∋x : Σ ∋ₛ x)
--        →  Σ[ E ∈ Σ ⁏ ∅ ⊢ `ℕ ] Σ[ VE ∈ Value Σ E ] μ ∋ₘ x ↪ ⟨ E , VE ⟩
--
--lookupₘ (_⊗_↪_ {Σ} m y ⟨ E , VE ⟩) x ∋x with x ≟ y
--... | yes p = ⟨ E , ⟨ VE , here p ⟩ ⟩
--... | no np with lookupₘ m x (force ∋x np)
--... | ⟨ E' , ⟨ VE' , ∋ₘx ⟩ ⟩ = let ⟨ E'' , VE'' ⟩ = renameN ⟨ E' , VE' ⟩
--                               in  ⟨ E'' , ⟨ VE'' , (S ∋ₘx) ⟩ ⟩
--
--data State (Σ : Store) (Γ : Context) (a : CType) : Set where
--  _⟪_⟫_ : ∀ {Ω} → Σ ⁏ Γ ⊩ a → Σ ⊆ Ω → Map Ω → State Σ Γ a
--
--data Final : ∀ {Σ Γ a} → Store → State Γ a Σ → Set where
--  F-ret : ∀ {Σ Ω Γ} {V : Σ ⁏ Γ ⊢ `ℕ} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω}
--        → Value Σ V → Final Σ (ret V ⟪ Σ⊆Ω ⟫ μ)
--
--data StepS : ∀ {Γ a} → (Σ : Store) → State Σ Γ a → State Σ Γ a → Set where
--  ξ-ret  : ∀ {Σ Ω Γ M M'} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω}
--         → Step {Σ} {Γ} M M'
--         → StepS Σ (ret M ⟪ Σ⊆Ω ⟫ μ) (ret M' ⟪ Σ⊆Ω ⟫ μ)
--
--  ξ-bnd  : ∀ {Σ Ω Γ M M' C} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω}
--         → Step {Σ} {Γ} M M'
--         → StepS Σ (bnd M C ⟪ Σ⊆Ω ⟫ μ) (bnd M' C ⟪ Σ⊆Ω ⟫ μ)
--
--  β-bndret : ∀ {Σ Ω Γ V C} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω}
--           → Value Σ {Γ} V
--           → StepS Σ (bnd (cmd (ret V)) C ⟪ Σ⊆Ω ⟫ μ) ((C [ V ]c) ⟪ Σ⊆Ω ⟫ μ)
--  --??
--  ξ-bndcmd : ∀ {Σ Ω Ω' Γ n} {μ : Map Ω} {μ' : Map Ω'} {Σ⊆Ω : Σ ⊆ Ω} {Σ⊆Ω' : Σ ⊆ Ω'} → {m m' : Σ ⁏ Γ ⊩ ok}
--           → StepS Σ (m ⟪ Σ⊆Ω ⟫ μ) (m' ⟪ Σ⊆Ω' ⟫ μ')
--           → StepS Σ (bnd (cmd m) n ⟪ Σ⊆Ω ⟫ μ) (bnd (cmd m') n ⟪ Σ⊆Ω' ⟫ μ')
--
--  β-get : ∀ {Σ Ω x} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω} {E : Ω ⁏ ∅ ⊢ `ℕ} {VE : Value Ω E}
--        → {∋x : Σ ∋ₛ x} → {∋ₘx : μ ∋ₘ x ↪ ⟨ E , VE ⟩} --extᵥ Σ⊆Ω VE
--        → StepS Σ (get x ∋x ⟪ Σ⊆Ω ⟫ μ) (ret (proj₁ $ renameN ⟨ E , VE ⟩) ⟪ Σ⊆Ω ⟫ μ)
--
--  ξ-set : ∀ {Σ Ω Γ x} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω} {E E' : Σ ⁏ Γ ⊢ `ℕ} → {∋x : Σ ∋ₛ x}
--        → Step E E'
--        → StepS Σ (set x ∋x E ⟪ Σ⊆Ω ⟫ μ) (set x ∋x E' ⟪ Σ⊆Ω ⟫ μ)
--
--  β-setret : ∀ {Σ Ω x} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω} {E : Σ ⁏ ∅ ⊢ `ℕ} → {∋x : Σ ∋ₛ x}
--           → (VE : Value Σ E)
--           → StepS Σ (set x ∋x E ⟪ Σ⊆Ω ⟫ μ) (ret E ⟪ S ∘ Σ⊆Ω ⟫ μ ⊗ x ↪ (renameN ⟨ E , VE ⟩))
--
--  ξ-dcl₁ : ∀ {Σ Ω Γ x C} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω} {E E' : Σ ⁏ Γ ⊢ `ℕ}
--         → Step E E'
--         → StepS Σ (dcl x E C ⟪ Σ⊆Ω ⟫ μ) (dcl x E' C ⟪ Σ⊆Ω ⟫ μ)
--
--  ξ-dcl₂ : ∀ {Σ Ω Ω' x C C'} {μ : Map Ω} {μ' : Map Ω'} {Σ⊆Ω : Σ ⊆ Ω} {Σx⊆Ω' : (Σ , x) ⊆ Ω'}
--             {E E' : Σ ⁏ ∅ ⊢ `ℕ} {VE : Value Σ E} {VE' : Value Σ E'}
--             {∋x : Ω' ∋ₛ x} {∋ₘVE' : μ' ∋ₘ x ↪ renameN ⟨ E' , VE' ⟩}
--         → StepS (Σ , x) (C ⟪ ext' Σ⊆Ω ⟫ μ ⊗ x ↪ renameN ⟨ E , VE ⟩) (C' ⟪ Σx⊆Ω' ⟫ μ')
--         → StepS Σ       (dcl x E C ⟪ Σ⊆Ω ⟫ μ)  (dcl x E' C' ⟪ (Σx⊆Ω' ∘ S)  ⟫ μ')
--
--  β-dclret : ∀ {Σ Ω Γ x} {μ : Map Ω} {Σ⊆Ω : Σ ⊆ Ω} {E : Σ ⁏ Γ ⊢ `ℕ} {E' : (Σ , x) ⁏ Γ ⊢ `ℕ}
--           → {VE : Value Σ E} → {VE' : Value (Σ , x) E'}
--           → StepS Σ (dcl x E (ret E') ⟪ Σ⊆Ω ⟫ μ) (ret (proj₁ $ renameN ⟨ E' , VE' ⟩) ⟪ Σ⊆Ω ⟫ μ)
--
--data Progress {Σ A} (M : Σ ⁏ ∅ ⊢ A) : Set where
--  done : Value Σ M → Progress M
--  step : {N : Σ ⁏ ∅ ⊢ A} → M —→ N → Progress M
--
--data Progress' {Σ Ω} (C : Σ ⁏ ∅ ⊩ ok) (Σ⊆Ω : Σ ⊆ Ω) (μ : Map Ω) : Set where
--  done : Final Σ (C ⟪ Σ⊆Ω ⟫ μ) → Progress' C Σ⊆Ω μ
--  step : ∀ {Ω'} {C' : Σ ⁏ ∅ ⊩ ok} {μ' : Map Ω'} {Σ⊆Ω' : Σ ⊆ Ω'}
--       → StepS Σ (C ⟪ Σ⊆Ω ⟫ μ) (C' ⟪ Σ⊆Ω' ⟫ μ')
--       → Progress' C Σ⊆Ω μ
--
--progress : ∀ {Σ A} → (M : Σ ⁏ ∅ ⊢ A) → Progress M
--progress (ƛ N) = done V-ƛ
--progress (L · M) with progress L
--...    | step L—→L′                     = step (ξ-·₁ L—→L′)
--...    | done V-ƛ with progress M
--...        | step M—→M′                 = step (ξ-·₂ V-ƛ M—→M′)
--...        | done VM                    = step (β-ƛ VM)
--progress (`zero)                        = done V-zero
--progress (`suc M) with progress M
--...    | step M—→M′                     = step (ξ-suc M—→M′)
--...    | done VM                        = done (V-suc VM)
--progress (case L M N) with progress L
--...    | step L—→L′                     = step (ξ-case L—→L′)
--...    | done V-zero                    = step (β-zero)
--...    | done (V-suc VL)                = step (β-suc VL)
--progress (μ N)                          = step (β-μ)
--progress (cmd C)                        = done V-cmd
--
--progress' : ∀ {Σ Ω} → (C : Σ ⁏ ∅ ⊩ ok) → (Σ⊆Ω : Σ ⊆ Ω) → (μ : Map Ω) → Progress' C Σ⊆Ω μ
--
--progress' (ret E) Σ⊆Ω m with progress E
--...                            | done VE   = done (F-ret VE)
--...                            | step E—→N = step (ξ-ret E—→N)
--
--progress' (bnd E C) Σ⊆Ω m with progress E
--progress' (bnd E C) Σ⊆Ω m | step E—→N = step (ξ-bnd E—→N)
--progress' (bnd (cmd C₁) C₂) Σ⊆Ω m | done VE with progress' C₁ Σ⊆Ω m
--progress' (bnd (cmd C₁) C₂) Σ⊆Ω m | done VE | step C₁⊢→C' = step (ξ-bndcmd C₁⊢→C')
--progress' (bnd (cmd (ret E₁)) C₂) Σ⊆Ω m | done VE | done FC₁ with progress E₁
--progress' (bnd (cmd (ret E₁)) C₂) Σ⊆Ω m | done VE | done FC₁ | step E₁—→N = step (ξ-bndcmd (ξ-ret E₁—→N))
--progress' (bnd (cmd (ret E₁)) C₂) Σ⊆Ω m | done VE | done FC₁ | done VE₁ = step (β-bndret VE₁)
--
--progress' (get x ∋x) Σ⊆Ω m with lookupₘ m x (Σ⊆Ω ∋x)
--... | ⟨ E  , ⟨ VE , ∋ₘVE ⟩ ⟩ = step (β-get {μ = m} {E = E} {VE = VE} {∋ₘx = ∋ₘVE})
--
--progress' (set x ∋x E) Σ⊆Ω m with progress E
--...                                 | step E—→N = step (ξ-set E—→N)
--...                                 | done VE = step (β-setret VE)
--
--progress' (dcl x E C) Σ⊆Ω m with progress E
--...                                 | step E—→N = step (ξ-dcl₁ E—→N)
--...                                 | done VE with progress' C (ext' Σ⊆Ω) (m ⊗ x ↪ renameN ⟨ E , VE ⟩)
--... | step {μ' = μ'} {Σx⊆Ω'} C⊢→C' with lookupₘ μ' x (Σx⊆Ω' Z)
--...   | ⟨ E' , ⟨ VE' , ∋ₘx ⟩ ⟩ with subsT (λ x₁ → μ' ∋ₘ x ↪ x₁) (sym eqN) ∋ₘx
--...     | ∋ₘx' = let ⟨ E'' , VE'' ⟩ = renameN ⟨ E' , VE' ⟩
--                 in step (ξ-dcl₂ {E' = E''} {VE' = VE''} {∋x = Σx⊆Ω' Z} {∋ₘVE' = ∋ₘx'} C⊢→C')
--
--progress' (dcl x E (ret E')) Σ⊆Ω m | done VE | done (F-ret VE') = step (β-dclret {VE = VE} {VE' = VE'})
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
--  _—↦⟨_⟩_ : ∀ {Σ Γ A} (S : State Σ Γ A) → {T U : State Σ Γ A}
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
