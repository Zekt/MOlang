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

data MType : Set
data Type : Set
data Context : Set

data MType where
  `ℕ : MType

data Type where
  _⇒_  : Type → Type → Type
  `ℕ   : Type
  `Cmd : MType → Type

data Memory : Set where
  ∅   : Memory
  _▷_ : Memory → MType → Memory

data Context where
  ∅   : Context
  _▷_ : Context → Type → Context

data _∋ₘ_ : Memory → MType → Set where
  Z : ∀ {Γ A}
    → Γ ▷ A ∋ₘ A
  S : ∀ {Γ A B}
    → Γ ∋ₘ A → Γ ▷ B ∋ₘ A

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ ▷ A ∋ A
  S : ∀ {Γ A B}
    → Γ ∋ A → Γ ▷ B ∋ A

variable
  ℳ 𝒩 : Memory
  Γ Δ : Context
  A B : Type
  E F : MType

liftType : MType → Type
liftType `ℕ = `ℕ

LiftType : MType → Type → Set
LiftType `ℕ `ℕ = ⊤
LiftType `ℕ (A ⇒ A₁) = ⊥
LiftType `ℕ (`Cmd A) = ⊥


--data _∋ₛ_ : Store → Id → Set where
--  Z : ∀ {Σ a}            → Σ ▷ a ∋ₛ a
--  S : ∀ {Σ a b} → Σ ∋ₛ a → Σ ▷ b ∋ₛ a

extM : (Id → Type) → Id → Type → (Id → Type)
extM ℳ i T j with i ≟ j
extM ℳ i T j | yes _ = T
extM ℳ i T j | no _ = ℳ j

data _⁏_⊢_ : Memory → Context → Type → Set where
  `_ : Γ ∋ A
     ------------
     → ℳ ⁏ Γ ⊢ A

  ƛ : ℳ ⁏ Γ ▷ A ⊢ B
     --------------------
    → ℳ ⁏ Γ ⊢ A ⇒ B

  -- ⇒-E
  _·_ : ℳ ⁏ Γ ⊢ A ⇒ B
      → ℳ ⁏ Γ ⊢ A
      ------------------------------
      → ℳ ⁏ Γ ⊢ B

  -- ℕ-I₁
  `zero : ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-I₂
  `suc_ : ℳ ⁏ Γ ⊢ `ℕ → ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-E
  case : ℳ ⁏ Γ ⊢ `ℕ  → ℳ ⁏ Γ ⊢ A  → ℳ ⁏ Γ ▷ `ℕ ⊢ A
       ------------------------------------------
       → ℳ ⁏ Γ ⊢ A

  μ_ : ℳ ⁏ Γ ▷ A ⊢ A
     -------------
     → ℳ ⁏ Γ ⊢ A

  ret : ℳ ⁏ Γ ⊢ A
      → ℳ ⁏ Γ ⊢ `Cmd `ℕ

  bnd : ℳ ⁏ Γ ⊢ `Cmd E → ℳ ⁏ Γ ▷ `ℕ ⊢ `Cmd F
      → ℳ ⁏ Γ ⊢ `Cmd F

  dcl : ℳ ⁏ Γ ⊢ `ℕ → ℳ ▷ `ℕ ⁏ Γ ⊢ `Cmd `ℕ
      → ℳ ⁏ Γ ⊢ `Cmd `ℕ

  get : ℳ ∋ₘ E
      → ℳ ⁏ Γ ⊢ `Cmd E

  set : ℳ ∋ₘ E
      → ℳ ⁏ Γ ⊢ `ℕ
      → ℳ ⁏ Γ ⊢ `Cmd E

--    cmd : ∀ {Σ Γ}
--         → Σ ⁏ Γ ⊩ ok
--         → Σ ⁏ Γ ⊢ `Cmd ok

--  data _⁏_⊩_ : Store → Context → CType → Set where
--    par : ∀ {Σ Γ}
--        → Σ ⁏ Γ ⊩ ok → Σ ⁏ Γ ⊩ ok
--        → Σ ⁏ Γ ⊩ ok

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

ext : (∀ {A}   → Γ ∋ A     → Δ ∋ A)
      -------------------------------
    → (∀ {A B} → Γ ▷ B ∋ A → Δ ▷ B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

extₘ : (∀ {a}   → ℳ ∋ₘ a     → 𝒩 ∋ₘ a)
     -----------------------------------
     → (∀ {a b} → ℳ ▷ b ∋ₘ a → 𝒩 ▷ b ∋ₘ a)
extₘ ρ Z     = Z
extₘ ρ (S x) = S (ρ x)

rename : (∀ {A} → Γ ∋ A  → Δ ∋ A)
       ----------------------------------
       → (∀ {A} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Δ ⊢ A)
rename ρ (` w)        = ` (ρ w)
rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
rename ρ `zero        = `zero
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ M)        = μ (rename (ext ρ) M)
rename ρ (ret N)      = ret (rename ρ N)
rename ρ (bnd E C)    = bnd (rename ρ E) (rename (ext ρ) C)
rename ρ (dcl N C)    = dcl (rename ρ N) (rename ρ C)
rename ρ (get a)      = get a
rename ρ (set a N)    = set a (rename ρ N)

renameₘ : (∀ {M} → ℳ ∋ₘ M  → 𝒩 ∋ₘ M)
        ----------------------------------
        → (∀ {A} → ℳ ⁏ Γ ⊢ A → 𝒩 ⁏ Γ ⊢ A)
renameₘ σ (` x)        = ` x
renameₘ σ (ƛ N)        = ƛ (renameₘ σ N)
renameₘ σ (L · M)      = (renameₘ σ L) · renameₘ σ M
renameₘ σ `zero        = `zero
renameₘ σ (`suc M)     = `suc renameₘ σ M
renameₘ σ (case L M N) = case (renameₘ σ L) (renameₘ σ M) (renameₘ σ N)
renameₘ σ (μ M)        = μ (renameₘ σ M)
renameₘ σ (ret N)      = ret (renameₘ σ N)
renameₘ σ (bnd E C)    = bnd (renameₘ σ E) (renameₘ σ C)
renameₘ σ (dcl N C)    = dcl (renameₘ σ N) (renameₘ (extₘ σ) C)
renameₘ σ (get a)      = get (σ a)
renameₘ σ (set a N)    = set (σ a) (renameₘ σ N)

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
exts : (∀ {A}   →     Γ ∋ A → ℳ ⁏ Δ ⊢ A)
     → (∀ {A B} → Γ ▷ B ∋ A → ℳ ⁏ Δ ▷ B ⊢ A)
exts ρ Z     = ` Z
exts ρ (S x) = rename S (ρ x)

exts' : ∀ {M}
      → ℳ ⁏ Δ ⊢ A
      → ℳ ▷ M ⁏ Δ ⊢ A
exts' σ = renameₘ S σ

extsₘ : (∀ {M}   →     ℳ ∋ₘ M  → 𝒩 ⁏ Γ ⊢ `Cmd M)
      → (∀ {M N} → ℳ ▷ N ∋ₘ M  → 𝒩 ▷ N ⁏ Γ ⊢ `Cmd M)
extsₘ σ Z = get Z
extsₘ σ (S x) = renameₘ S (σ x)

subst : (∀ {A} → Γ ∋ A → ℳ ⁏ Δ ⊢ A)
       ------------------------
      → (∀ {A} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Δ ⊢ A)
subst σ (` x)        = σ x
subst σ (ƛ N)        = ƛ (subst (exts σ) N)
subst σ (L · M)      = (subst σ L) · (subst σ M)
subst σ `zero        = `zero
subst σ (`suc N)     = `suc (subst σ N)
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)        = μ (subst (exts σ) N)
subst σ (ret N)      = ret (subst σ N)
subst σ (bnd C D)    = bnd (subst σ C) (subst (exts σ) D)
subst σ (dcl N C)    = dcl (subst σ N) (subst (exts' ∘ σ) C)
subst σ (get a)      = get a
subst σ (set a N)    = set a (subst σ N)

_[_] : ℳ ⁏ Γ ▷ B ⊢ A → ℳ ⁏ Γ ⊢ B
     → ℳ ⁏ Γ ⊢ A
_[_] {ℳ} {Γ} {B} {A} N M = subst σ N
  where
    σ : ∀ {A} → Γ ▷ B ∋ A → ℳ ⁏ Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

data Value : ℳ ⁏ Γ ⊢ A → Set where
  V-ƛ    : {N : ℳ ⁏ Γ ▷ A ⊢ B} → Value N → Value (ƛ N)
  V-zero : Value {ℳ} {Γ} `zero
  V-suc  : {V : ℳ ⁏ Γ ⊢ `ℕ} → Value V → Value (`suc V)
  V-ret  : {V : ℳ ⁏ Γ ⊢ `ℕ} → Value V → Value (ret V)

shrink : (E : ℳ ▷ `ℕ ⁏ Γ ⊢ A) → Value E → ℳ ⁏ Γ ⊢ A
shrink (ƛ E) (V-ƛ VE) = ƛ (shrink E VE)
shrink `zero VE = `zero
shrink (`suc E) (V-suc VE) = shrink E VE
shrink (ret E) (V-ret VE) = ret (shrink E VE)

data Step : {ℳ : Memory} {Γ : Context} {A : Type} → ℳ ⁏ Γ ⊢ A → ℳ ⁏ Γ ⊢ A → Set where
  ξ-·₁ : {L L' : ℳ ⁏ Γ ⊢ A ⇒ B} {M : ℳ ⁏ Γ ⊢ A}
       → Step L L'
       → Step (L · M) (L' · M)

  ξ-·₂ : {V : ℳ ⁏ Γ ⊢ A ⇒ B} {M M' : ℳ ⁏ Γ ⊢ A}
       → Value V
       → Step M M'
       → Step (V · M) (V · M')

  β-ƛ : ∀ {N : ℳ ⁏ Γ ▷ A ⊢ B} {W : ℳ ⁏ Γ ⊢ A}
      → Value W
      → Step ((ƛ N) · W) (N [ W ])

  ξ-ƛ : ∀ {M M' : ℳ ⁏ Γ ▷ A ⊢ B}
      → Step M M'
      → Step (ƛ M) (ƛ M')

  ξ-suc : {M M′ : ℳ ⁏ Γ ⊢ `ℕ}
        → Step M M′
        → Step (`suc M) (`suc M′)

  ξ-case : {L L′ : ℳ ⁏ Γ ⊢ `ℕ} {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
         → Step L L′
         → Step (case L M N) (case L′ M N)

  β-zero :  {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
         → Step (case `zero M N) M

  β-suc : {V : ℳ ⁏ Γ ⊢ `ℕ} {M : ℳ ⁏ Γ ⊢ A} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ A}
        → Value V
        → Step (case (`suc V) M N) (N [ V ])

  β-μ : {N : ℳ ⁏ Γ ▷ A ⊢ A}
      → Step (μ N) (N [ μ N ])

  ξ-ret  : ∀ {M M' : ℳ ⁏ Γ ⊢ `Cmd `ℕ}
         → Step M M'
         → Step (ret M) (ret M')

  ξ-bnd  : ∀ {M M' : ℳ ⁏ Γ ⊢ `Cmd `ℕ} {C : ℳ ⁏ Γ ▷ `ℕ ⊢ `Cmd F}
         → Step M M'
         → Step (bnd M C) (bnd M' C)

  β-bndret : ∀ {V : ℳ ⁏ Γ ⊢ `ℕ} {C : ℳ ⁏ Γ ▷ `ℕ ⊢ `Cmd F}
           → Value V
           → Step (bnd (ret V) C) (C [ V ])

  ξ-bndcmd : ∀ {M M' : ℳ ⁏ Γ ⊢ `Cmd `ℕ} {N : ℳ ⁏ Γ ▷ `ℕ ⊢ `Cmd F}
           → Step M M'
           → Step (bnd M N) (bnd M' N)

  β-get : ∀ {x} {E}
        → Step (get x) (ret {ℳ} {Γ} {A} E)

  ξ-set : ∀ {Eₘ} {x : ℳ ∋ₘ Eₘ} {E} {E'}
        → Step {ℳ} {Γ} E E'
        → Step (set x E) (set x E')

  β-setret : ∀ {x} {E}
           → Step {ℳ} {Γ} (set x E) (ret E)

  ξ-dcl₁ : ∀ {E E' C}
         → Step {ℳ} {Γ} E E'
         → Step (dcl E C) (dcl E' C)

  ξ-dcl₂ : ∀ {C C' E₁ E₂}
         → Step C C'
         → Step {ℳ} {Γ} (dcl E₁ C) (dcl E₂ C')

  β-dclret : ∀ {E : ℳ ⁏ Γ ⊢ `ℕ} {E' : ℳ ▷ `ℕ ⁏ Γ ⊢ `ℕ}
           → (VE' : Value E')
           → Step (dcl E (ret E')) (ret (shrink E' VE'))

--data Map : Set where
  --∅     : Map
  --_⊗_↪_ : ∀ {E : ∅ ⊢ `ℕ} → Map → Id → Value E → Map
--
--data _∋ₘ_↪_ : ∀ {E} → Map → Id → Value {∅} {`ℕ} E → Set where
--    Z : ∀ {m a E} {VE : Value E}
--      → m ⊗ a ↪ VE ∋ₘ a ↪ VE
--    S : ∀ {m a E a' E'} {VE : Value E} {VE' : Value E'}
--      → m            ∋ₘ a ↪ VE
--      → m ⊗ a' ↪ VE' ∋ₘ a ↪ VE
--
--lookupₘ : (m : Map) → (x : Id) → ∃[ E ] (Σ[ VE ∈ Value E ] m ∋ₘ x ↪ VE)
--lookupₘ (_⊗_↪_ m x VE) y with x ≟ y
--... | yes refl = _ , VE , Z
--... | no _ with lookupₘ m y
--...   | _ , VE' , ∋ₘy = _ , VE' , S ∋ₘy
--lookupₘ ∅ _ = ⊥-elim impossible
  --where postulate impossible : ⊥
----
----flex : ∀ {Γ Δ} → (E : Γ ⊢ `ℕ) → Value E → Δ ⊢ `ℕ
----flex `zero VE = `zero
----flex (`suc E) (V-suc VE) = `suc flex E VE
----
--data State (Γ : Context) (A : Type) : Set where
  --_∥_ : Γ ⊢ A → Map → State Γ A
--
--data Final : ∀ {Γ A} → State Γ A → Set where
  --F-ret : ∀ {Γ ℳ} {V : Γ ⊢ `ℕ} {μ : Map}
        --→ Value V → Final (ret {Γ} {ℳ} V ∥ μ)
  --F-val : ∀ {Γ A} {V : Γ ⊢ A} {μ : Map}
        --→ Value V → Final (V ∥ μ)
--
--EqV : ∀ {Γ Δ E E'} → Value {Γ} {`ℕ} E → Value {Δ} {`ℕ} E' → Set
--EqV V-zero V-zero = ⊤
--EqV V-zero (V-suc VE') = ⊥
--EqV (V-suc VE) V-zero = ⊥
--EqV (V-suc VE) (V-suc VE') = EqV VE VE'
--
--extV : ∀ {Γ} {E : ∅ ⊢ `ℕ} → (VE : Value E) → ∃[ E' ] (Σ[ VE' ∈ Value {Γ} {`ℕ} E' ] EqV VE' VE)
--extV {E = .`zero} V-zero = `zero , V-zero , tt
--extV {E = `suc E} (V-suc VE) with extV {E = E} VE
--... | E' , VE' , eqv = `suc E' , V-suc VE' , eqv
--
--EqV-eq : ∀ {Γ} {E : Γ ⊢ `ℕ} (VE : Value E) → EqV VE VE
--EqV-eq V-zero = tt
--EqV-eq (V-suc VE) = EqV-eq VE
--
--EqV-sym : ∀ {Γ Δ E E'} {VE : Value {Γ} E} {VE' : Value {Δ} E'} → EqV {Γ} {Δ} VE VE' → EqV VE' VE
--EqV-sym {VE = V-zero} {V-zero} VE=VE' = VE=VE'
--EqV-sym {VE = V-suc VE} {V-suc VE'} VE=VE' = EqV-sym {VE = VE} {VE' = VE'} VE=VE'
--
--remove : ∀ {E} {VE : Value E} → (m : Map) → (a : Id) → m ∋ₘ a ↪ VE → Map
--remove (m ⊗ a ↪ _) a Z = m
--remove (m ⊗ _ ↪ _) a (S ∋ₘa) = remove m a ∋ₘa
--
--data Remove {a E} {VE : Value E} : (m : Map) → (m' : Map) → m ∋ₘ a ↪ VE → Set where
  --Z : ∀ {m} → Remove (m ⊗ a ↪ VE) m Z
  --S : ∀ {m m' ∋ₘa a' E'} {VE' : Value E'} → Remove m m' ∋ₘa → Remove (m ⊗ a' ↪ VE') (m' ⊗ a' ↪ VE') (S ∋ₘa)

--Steps with State
--data Step : {Γ : Context} {A : Type} → State Γ A → State Γ A → Set where
--  ξ-·₁ : ∀ {Γ A B m m'} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
--       → Step (L ∥ m) (L' ∥ m')
--       → Step (L · M ∥ m) (L' · M ∥ m')
--
--  ξ-·₂ : ∀ {Γ A B m m'} {V : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
--       → Value V
--       → Step (M ∥ m) (M' ∥ m')
--       → Step (V · M ∥ m) (V · M' ∥ m')
--
--  β-ƛ : ∀ {Γ A B} {N : Γ ▷ A ⊢ B} {W : Γ ⊢ A}
--      → Value W
--      --------------------
--      → (∀ {m} → Step ((ƛ N) · W ∥ m) (N [ W ] ∥ m))
--
--  ξ-suc : ∀ {Γ m m'} {M M′ : Γ ⊢ `ℕ}
--        → Step (M ∥ m) (M′ ∥ m')
--        -----------------
--        → Step (`suc M ∥ m) (`suc M′ ∥ m')
--
--  ξ-case : ∀ {Γ A m m'} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
--         → Step (L ∥ m) (L′ ∥ m')
--         -------------------------
--         → Step (case L M N ∥ m) (case L′ M N ∥ m')
--
--  β-zero :  ∀ {Γ A m} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
--         -------------------
--         → Step (case `zero M N ∥ m) (M ∥ m)
--
--  β-suc : ∀ {Γ A m} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ▷ `ℕ ⊢ A}
--        → Value V
--        ----------------------------
--        → Step (case (`suc V) M N ∥ m) (N [ V ] ∥ m)
--
--  β-μ : ∀ {Γ A m} {N : Γ ▷ A ⊢ A}
--      ----------------
--      → Step (μ N ∥ m) (N [ μ N ] ∥ m)
--
--  ξ-ret  : ∀ {Γ ℳ M M' m m'}
--         → Step (M ∥ m) (M' ∥ m')
--         → Step (ret {Γ} {ℳ} M ∥ m) (ret {Γ} {ℳ} M' ∥ m')
--
--  ξ-bnd  : ∀ {Γ ℳ M M' C m m'}
--         → Step (M ∥ m) (M' ∥ m')
--         → Step (bnd {Γ} {ℳ} M C ∥ m) (bnd M' C ∥ m')
--
--  β-bndret : ∀ {Γ ℳ V C} {m : Map}
--           → Value {Γ} V
--           → Step (bnd {Γ} {ℳ} (ret V) C ∥ m) ((C [ V ]) ∥ m)
--
--  ξ-bndcmd : ∀ {Γ ℳ N} {m m' : Map} → {M M' : Γ ⊢ `Cmd ℳ `ℕ}
--           → Step (M ∥ m) (M' ∥ m')
--           → Step (bnd M N ∥ m) (bnd M' N ∥ m')
--
--  β-get : ∀ {x Γ ℳ E E' m} {VE : Value E} {VE' : Value E'}
--        --→ EqV VE (proj₂ $ lookupₘ m x)
--        → EqV VE VE'
--        → m ∋ₘ x ↪ VE'
--        → Step (get {Γ} {ℳ} x ∥ m) (ret E ∥ m)
--
--  ξ-set : ∀ {Γ ℳ x m m'} {E E' : Γ ⊢ `ℕ}
--        → Step (E ∥ m) (E' ∥ m')
--        → Step (set {Γ} {ℳ} x E ∥ m) (set x E' ∥ m')
--
--  β-setret : ∀ {x Γ ℳ m E E'} {VE' : Value E'}
--           → (VE : Value E)
--           → EqV VE VE'
--           → Step (set {Γ} {ℳ} x E ∥ m) (ret E ∥ (m ⊗ x ↪ VE'))
--
--  ξ-dcl₁ : ∀ {Γ ℳ x C m m'} {E E' : Γ ⊢ `ℕ}
--         → Step (E ∥ m) (E' ∥ m')
--         → Step (dcl {Γ} {ℳ} x E C ∥ m) (dcl x E' C ∥ m')
--
--  ξ-dcl₂ : ∀ {Γ ℳ x C C' m m' m'' E₁ E₂ E₁' E₂'}
--             {VE₁ : Value E₁} {VE₂ : Value E₂} {VE₁' : Value E₁'} {VE₂' : Value E₂'}
--         → EqV VE₁ VE₁'
--         → EqV VE₂ VE₂'
--         → (∋ₘx : m' ∋ₘ x ↪ VE₂')
--         → Remove m' m'' ∋ₘx
--         → Step (C ∥ m ⊗ x ↪ VE₁') (C' ∥ m')
--         → Step (dcl {Γ} {ℳ} x E₁ C ∥ m) (dcl x E₂ C' ∥ m'')
--
--  β-dclret : ∀ {Γ ℳ x} {m : Map} {E E' : Γ ⊢ `ℕ}
--           → Step (dcl {Γ} {ℳ} x E (ret E') ∥ m) (ret E' ∥ m)
--
--find : ∀ {Γ A C C' m m' x E} {VE : Value E}
--     → m ∋ₘ x ↪ VE → Step {Γ} {A} (C ∥ m) (C' ∥ m')
--     → ∃[ E' ] (Σ[ VE' ∈ Value E' ] m' ∋ₘ x ↪ VE')
--find ∋ₘx (ξ-·₁ Π) = find ∋ₘx Π
--find ∋ₘx (ξ-·₂ x Π) =  find ∋ₘx Π
--find ∋ₘx (β-ƛ x) = _ , _ , ∋ₘx
--find ∋ₘx (ξ-suc Π) =  find ∋ₘx Π
--find ∋ₘx (ξ-case Π) =  find ∋ₘx Π
--find ∋ₘx β-zero =  _ , _ , ∋ₘx
--find ∋ₘx (β-suc x) =  _ , _ , ∋ₘx
--find ∋ₘx β-μ =  _ , _ , ∋ₘx
--find ∋ₘx (ξ-ret Π) =  find ∋ₘx Π
--find ∋ₘx (ξ-bnd Π) =  find ∋ₘx Π
--find ∋ₘx (β-bndret x) =  _ , _ , ∋ₘx
--find ∋ₘx (ξ-bndcmd Π) =  find ∋ₘx Π
--find ∋ₘx (β-get x x₁) = {!!}
--find ∋ₘx (ξ-set Π) =  find ∋ₘx Π
--find ∋ₘx (β-setret VE x₁) =  _ , _ , S ∋ₘx
--find ∋ₘx (ξ-dcl₁ Π) =  find ∋ₘx Π
--find {x = x} ∋ₘx (ξ-dcl₂ {x = a} eqv₁ eqv₂ Z Z Π) with find (S ∋ₘx) Π
--find {x = x} Z (ξ-dcl₂ {x = x} eqv₁ eqv₂ Z Z Π) | E' , VE' , Z = E' , VE' , {!!}
--find {x = x} (S ∋ₘx) (ξ-dcl₂ {x = x} eqv₁ eqv₂ Z Z Π) | E' , VE' , Z = {!!} , {!!} , {!!}
--find {x = x} ∋ₘx (ξ-dcl₂ {x = a} eqv₁ eqv₂ Z Z Π) | E' , VE' , S ∋ₘx' = {!!} , {!!} , {!!}
--find {x = x} ∋ₘx (ξ-dcl₂ {x = a} eqv₁ eqv₂ ∋ₘa (S rm) Π) = {!!}
--find ∋ₘx β-dclret =  _ , _ , ∋ₘx
--
--
--_—→_ : ∀ {Γ A} → State Γ A → State Γ A → Set
--L —→ M = Step L M
--
--data Progress {A} (M : ∅ ⊢ A) (m : Map) : Set where
--  done : Final (M ∥ m) → Progress M m
--  step : ∀ {M' : ∅ ⊢ A} {m' : Map}
--       → Step (M ∥ m) (M' ∥ m')
--       → Progress M m
--
--progress : ∀ {A} → (M : ∅ ⊢ A) → (m : Map) → Progress M m
--
--progress (ƛ M) m = done (F-val V-ƛ)
--
--progress (L · M) m with progress L m
--... | step L—→L′        = step (ξ-·₁ L—→L′)
--... | done (F-val V-ƛ) with progress M m
--...   | step M—→M′      = step (ξ-·₂ V-ƛ M—→M′)
--...   | done (F-val VM) = step (β-ƛ VM)
--...   | done (F-ret VV) = step (β-ƛ (V-ret VV))
--
--progress `zero m = done (F-val V-zero)
--
--progress (`suc M) m with progress M m
--... | step M—→M′      = step (ξ-suc M—→M′)
--... | done (F-val VM) = done (F-val (V-suc VM))
--
--progress (case L M N) m with progress L m
--... | step L—→L′              = step (ξ-case L—→L′)
--... | done (F-val V-zero)     = step β-zero
--... | done (F-val (V-suc VL)) = step (β-suc VL)
--
--progress (μ M) m = step β-μ
--
--progress (ret M) m with progress M m
--... | step M—→M′      = step (ξ-ret M—→M′)
--... | done (F-val VM) = done (F-ret VM)
--
--progress (bnd C₁ C₂) m with progress C₁ m
--... | step C₁—→C₁′            = step (ξ-bnd C₁—→C₁′)
--... | done (F-ret VE)         = step (β-bndret VE)
--... | done (F-val (V-ret VE)) = step (β-bndret VE)
--
--progress (dcl a E C) m with progress E m
--... | step E—→E'               = step (ξ-dcl₁ E—→E')
--... | done (F-val VE) with progress C (m ⊗ a ↪ VE)
--...   | done (F-ret _)         = step β-dclret
--...   | done (F-val (V-ret _)) = step β-dclret
--...   | step {m' = m'} C—→C' with find Z C—→C'
--...     | _ , VE' , ∋ₘa = step (ξ-dcl₂ {VE₁ = VE} {VE₂ = VE'} (EqV-eq VE) (EqV-eq VE') ∋ₘa {!!} C—→C')
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
