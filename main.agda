open import Relation.Binary.PropositionalEquality as Eq
      using (_≡_; _≢_; refl; cong; cong₂; sym; inspect)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.List using (List; _∷_; []; all; map)
open import Data.List.All using (All)
open import Data.List.NonEmpty using (List⁺; _∷⁺_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Function using (id; _$_; _∘_) 
--open import Category.Monad.State
--open import Level

module main where

--infix 2 _—→_
--infix 2 _⊢→_
infix  4 _⁏_⁏_⊢_
infix  4 _∋_
infix  4 _∋ₘ_
infix  4 _∋ₛ_
infix  4 _∥_ _⟫_
infixl 5 _▷_
infixr 7 _⇒_
infixl 7 _·_
infix  7 _⊕_ _⊕ᶜ_ _∷ᶜ_ _∷ᵖ_
infix  8 `suc_ get_ §ᶜ_ §ᵖ_
infix  9 `_
infix  9 #_

Id : Set
Id = String

data Type : Set
data MType : Type → Set
data Context : Set

data Type where
  _⇒_     : Type → Type → Type
  `ℕ      : Type
  `Cmd    : {T : Type} → (MType T) → Type
  Hand_⇛_ : {T U : Type} → MType T → MType U → Type

data MType where
  `ℕ : MType `ℕ


data Memory : Set where
  ∅   : Memory
  _▷_ : {T : Type} → Memory → MType T → Memory

data Shared : Set where
  ∅   : Shared
  _▷_ : {T : Type} → Shared → MType T → Shared

data Context where
  ∅   : Context
  _▷_ : Context → Type → Context

variable
  ℳ 𝒩 : Memory
  Σ Ω : Shared
  Γ Δ : Context
  A B : Type
  MA : MType A
  MB : MType B

data _∋ₘ_ {T} : Memory → MType T → Set where
  Z : ℳ ▷ MA ∋ₘ MA
  S : ℳ ∋ₘ MA → ℳ ▷ MB ∋ₘ MA

data _∋ₛ_ {T} : Shared → MType T → Set where
  Z : Σ ▷ MA ∋ₛ MA
  S : Σ ∋ₛ MA → Σ ▷ MB ∋ₛ MA

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ ▷ A ∋ A
  S : ∀ {Γ A B}
    → Γ ∋ A → Γ ▷ B ∋ A

--liftType : MType → Type

--data _∋ₛ_ : Store → Id → Set where
--  Z : ∀ {Σ a}            → Σ ▷ a ∋ₛ a
--  S : ∀ {Σ a b} → Σ ∋ₛ a → Σ ▷ b ∋ₛ a

extM : (Id → Type) → Id → Type → (Id → Type)
extM ℳ i T j with i ≟ j
extM ℳ i T j | yes _ = T
extM ℳ i T j | no _  = ℳ j

--Shared is the shared memory between threads,
--Memory the local memory of declared variables,
--and Context the common logical context.
data MemoryOrder : Set where
  Weak : MemoryOrder
  SC : MemoryOrder

data _⁏_⁏_⊢_ : Shared → Memory → Context → Type → Set where
  `_ : Γ ∋ A
     → Σ ⁏ ℳ ⁏ Γ ⊢ A

  ƛ : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ B
    → Σ ⁏ ℳ ⁏ Γ     ⊢ A ⇒ B

  -- ⇒-E
  _·_ : Σ ⁏ ℳ ⁏ Γ ⊢ A ⇒ B
      → Σ ⁏ ℳ ⁏ Γ ⊢ A
      → Σ ⁏ ℳ ⁏ Γ ⊢ B

  -- ℕ-I₁
  `zero : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-I₂
  `suc_ : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ
        → Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ

  -- ℕ-E
  case : Σ ⁏ ℳ ⁏ Γ      ⊢ `ℕ
       → Σ ⁏ ℳ ⁏ Γ      ⊢ A
       → Σ ⁏ ℳ ⁏ Γ ▷ `ℕ ⊢ A
       → Σ ⁏ ℳ ⁏ Γ      ⊢ A

  μ_ : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ A
     → Σ ⁏ ℳ ⁏ Γ     ⊢ A

  -- □-intro?
  -- It's more likely ⋄-intro, since computations can be seem as possibly-something.
  -- E.g. to get an int can be seem as a witness to "possible int".
  -- Since we have A, A is definitely possible.
  ret : ∀ {A} {MA : MType A}
      → Σ ⁏ ℳ ⁏ Γ ⊢ A
      → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA

  -- Modus ponens for modality. Possible A and that A implies possible B derives possible B.
  bnd : ∀ {A B} {MA : MType A} {MB : MType B}
     → Σ ⁏ ℳ ⁏ Γ     ⊢ `Cmd MA
     → Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MB
     → Σ ⁏ ℳ ⁏ Γ     ⊢ `Cmd MB

  --□-elim? □-elimₚ?
  --A, A ⊢ ⋄B ∣ ⋄B, what's the difference?
  dcl : ∀ {A B} {MA : MType A} {MB : MType B}
     → Σ ⁏      ℳ ⁏ Γ ⊢ A
     → Σ ⁏ ℳ ▷ MA ⁏ Γ ⊢ `Cmd MB
     → Σ ⁏      ℳ ⁏ Γ ⊢ `Cmd MB

  --"possible" something
  get_ : ∀ {A} {MA : MType A}
       → ℳ ∋ₘ MA
       → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA

  getₛ : ∀ {A} {MA : MType A}
       → Σ ∋ₛ MA
       → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA

  setₛ : ∀ {A} {MA : MType A}
       → Σ ∋ₛ MA
       → Σ ⁏ ℳ ⁏ Γ ⊢ A
       → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA

  handle : ∀ {A B} {MA : MType A} {MB : MType B}
         → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA
         → Σ ⁏ ℳ ⁏ Γ ⊢ Hand MA ⇛ MB
         → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MB

  handler : MemoryOrder
          → Σ ⁏ ℳ ⁏ Γ ⊢ Hand MA ⇛ MB

--The result of MA is available in MB
--Continuation of MA is ...
--Scheme : ...
--Scheme Σ ℳ Γ = ∀ {A B} {MA : MType A} {MB : MType B}
--             → List (Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA × Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MB)


--_≟ₛ_ : ∀ (E F : Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA) → Dec (E ≡ F)

--lookupₕ : Scheme Σ ℳ Γ → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA
--lookupₕ ss a with ss
--lookupₕ ss a | [] = a
--lookupₕ ss a | (a' , b) ∷ xs with ?

--data Handler {A B} (MA : MType A) (MB : MType B) : Set where 
--  ∅ : Handler MA MB
--  _,_↝_ : Handler MA MB → ∅ ⁏ ∅ ⁏ ∅ ⊢ `Cmd MA → ∅ ⁏ ∅ ⁏ ∅ ⊢ `Cmd MB → Handler MA MB


lookup : Context → ℕ → Type
lookup (Γ ▷ A) zero    = A
lookup (Γ ▷ _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

lookupₘ : Memory → ℕ → ∃[ A ] MType A
lookupₘ (_▷_ {A} ℳ MA) zero = A , MA
lookupₘ (ℳ ▷ MA) (suc n) = lookupₘ ℳ n
lookupₘ ∅ _ = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ ▷ _} zero    = Z
count {Γ ▷ _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

countₘ : ∀ {ℳ} → (n : ℕ) → ℳ ∋ₘ proj₂ (lookupₘ ℳ n)
countₘ {ℳ ▷ _} zero    = Z
countₘ {ℳ ▷ _} (suc n) = S (countₘ n)
countₘ {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : (n : ℕ) → Σ ⁏ ℳ ⁏ Γ ⊢ lookup Γ n
# n = ` (count n)

#ₘ : (n : ℕ) → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd (proj₂ (lookupₘ ℳ n))
#ₘ n = get (countₘ n)

ext : (∀ {A}   → Γ ∋ A     → Δ ∋ A)
      -------------------------------
    → (∀ {A B} → Γ ▷ B ∋ A → Δ ▷ B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

extₘ : (∀ {A}   {MA : MType A}                →      ℳ ∋ₘ MA →      𝒩 ∋ₘ MA)
     → (∀ {A B} {MA : MType A} {MB : MType B} → ℳ ▷ MB ∋ₘ MA → 𝒩 ▷ MB ∋ₘ MA)
extₘ ρ Z     = Z
extₘ ρ (S x) = S (ρ x)

{-# TERMINATING #-}
rename : (∀ {A} → Γ ∋ A  → Δ ∋ A)
       → (∀ {A} → Σ ⁏ ℳ ⁏ Γ ⊢ A → Σ ⁏ ℳ ⁏ Δ ⊢ A)

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
rename ρ (getₛ x)     = getₛ x
rename ρ (setₛ x E)   = setₛ x (rename ρ E)
rename ρ (handle E H) = handle (rename ρ E) (rename ρ H)
rename ρ (handler Hs) = {!!} -- handler (map (λ {(a , b) → rename ρ a , rename (ext ρ) b}) Hs)

{-# TERMINATING #-}
renameₘ : (∀ {A} {MA : MType A} → ℳ ∋ₘ MA  → 𝒩 ∋ₘ MA)
        ----------------------------------
        → (∀ {A} → Σ ⁏ ℳ ⁏ Γ ⊢ A → Σ ⁏ 𝒩 ⁏ Γ ⊢ A)
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
renameₘ σ (getₛ x)     = getₛ x
renameₘ σ (setₛ x E)   = setₛ x (renameₘ σ E)
renameₘ σ (handle E H) = handle (renameₘ σ E) (renameₘ σ H)
renameₘ σ (handler Hs) = {!!} -- handler (map (λ {(a , b) → renameₘ σ a , renameₘ σ b}) Hs)
--renameₘ σ (set a N)    = set (σ a) (renameₘ σ N)

{-# TERMINATING #-}
renameₛ : (∀ {A} {MA : MType A} → Σ ∋ₛ MA       → Ω ∋ₛ MA)
        → (∀ {A}                → Σ ⁏ ℳ ⁏ Γ ⊢ A → Ω ⁏ ℳ ⁏ Γ ⊢ A)
renameₛ τ (` x) = ` x
renameₛ τ (ƛ N) = ƛ (renameₛ τ N)
renameₛ τ (L · M) = (renameₛ τ L) · (renameₛ τ M)
renameₛ τ `zero = `zero
renameₛ τ (`suc M) = `suc (renameₛ τ M)
renameₛ τ (case L M N) = case (renameₛ τ L) (renameₛ τ M) (renameₛ τ N)
renameₛ τ (μ M) = μ (renameₛ τ M)
renameₛ τ (ret N) = ret (renameₛ τ N)
renameₛ τ (bnd E C) = bnd (renameₛ τ E) (renameₛ τ C)
renameₛ τ (dcl N C) = dcl (renameₛ τ N) (renameₛ τ C)
renameₛ τ (get a) = get a
renameₛ τ (getₛ x) = getₛ (τ x)
renameₛ τ (setₛ x E) = setₛ (τ x) (renameₛ τ E)
renameₛ τ (handle E H) = handle (renameₛ τ E) (renameₛ τ H)
renameₛ τ (handler Hs) = {!!} -- handler (map (λ {(a , b) → renameₛ τ a , renameₛ τ b}) Hs)
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
--
ext- : Σ ⁏ ℳ ⁏ Γ ⊢ A
     → Σ ⁏ ℳ ⁏ Γ ▷ B ⊢ A
ext- N = rename S N

exts : (∀ {A}   →     Γ ∋ A → Σ ⁏ ℳ ⁏     Δ ⊢ A)
     → (∀ {A B} → Γ ▷ B ∋ A → Σ ⁏ ℳ ⁏ Δ ▷ B ⊢ A)
exts ρ Z     = ` Z
exts ρ (S x) = rename S (ρ x)

exts' : Σ ⁏ ℳ ⁏ Δ ⊢ A
      → Σ ⁏ ℳ ▷ MB ⁏ Δ ⊢ A
exts' N = renameₘ S N

extsₘ : (∀ {A}   {MA : MType A}                →      ℳ ∋ₘ MA  → Σ ⁏      𝒩 ⁏ Γ ⊢ `Cmd MA)
      → (∀ {A B} {MA : MType A} {MB : MType B} → ℳ ▷ MB ∋ₘ MA  → Σ ⁏ 𝒩 ▷ MB ⁏ Γ ⊢ `Cmd MA)
extsₘ σ Z = get Z
extsₘ σ (S x) = renameₘ S (σ x)

{-# TERMINATING #-}
subst : (∀ {A} → Γ ∋ A         → Σ ⁏ ℳ ⁏ Δ ⊢ A)
       ------------------------
      → (∀ {A} → Σ ⁏ ℳ ⁏ Γ ⊢ A → Σ ⁏ ℳ ⁏ Δ ⊢ A)
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
subst σ (getₛ x)     = getₛ x
subst σ (setₛ x E)   = setₛ x (subst σ E)
subst σ (handle E H) = handle (subst σ E) (subst σ H)
subst σ (handler Hs) = {!!} -- handler (map (λ {(a , b) → subst σ a , subst (exts σ) b}) Hs)
--subst σ (set a N)    = set a (subst σ N)

{-# TERMINATING #-}
substₘ : (∀ {A} {MA : MType A} → ℳ ∋ₘ MA       → Σ ⁏ 𝒩 ⁏ Γ ⊢ `Cmd MA)
       → (∀ {A}                → Σ ⁏ ℳ ⁏ Γ ⊢ A → Σ ⁏ 𝒩 ⁏ Γ ⊢ A)
substₘ ρ (` x) = ` x
substₘ ρ (ƛ N) = ƛ (substₘ (ext- ∘ ρ) N)
substₘ ρ (L · M) = substₘ ρ L · substₘ ρ M
substₘ ρ `zero = `zero
substₘ ρ (`suc N) = `suc (substₘ ρ N)
substₘ ρ (case L M N) = case (substₘ ρ L) (substₘ ρ M) (substₘ (ext- ∘ ρ) N)
substₘ ρ (μ N) = μ (substₘ (ext- ∘ ρ) N)
substₘ ρ (ret N) = ret (substₘ ρ N)
substₘ ρ (bnd C D) = bnd (substₘ ρ C) (substₘ (ext- ∘ ρ) D)
substₘ ρ (dcl N C) = dcl (substₘ ρ N) (substₘ (λ {Z → get Z ; (S x) → exts' (ρ x)}) C)
substₘ ρ (get x) = ρ x
substₘ ρ (getₛ x) = getₛ x
substₘ ρ (setₛ x E) = setₛ x (substₘ ρ E)
substₘ ρ (handle E H) = handle (substₘ ρ E) (substₘ ρ H)
substₘ ρ (handler Hs) = {!!} --handler (map (λ {(a , b) → (substₘ ρ a , substₘ (ext- ∘ ρ) b)}) Hs)
--substₘ ρ (set x N) = {!!}

_[_] : Σ ⁏ ℳ ⁏ Γ ▷ B ⊢ A → Σ ⁏ ℳ ⁏ Γ ⊢ B
     → Σ ⁏ ℳ ⁏ Γ ⊢ A
_[_] {Σ} {ℳ} {Γ} {B} {A} N M = subst σ N
  where
    σ : ∀ {A} → Γ ▷ B ∋ A → Σ ⁏ ℳ ⁏ Γ ⊢ A
    σ Z     = M
    σ (S x) = ` x

_[_]' : ∀ {A B} {MA : MType A} {MB : MType B}
      → Σ ⁏ ℳ ▷ MB ⁏ Γ ⊢ `Cmd MA → Σ ⁏ ℳ ⁏ Γ ⊢ B
      → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA
_[_]' {Σ} {ℳ} {Γ} {A} {B} {MA} {MB} C D = substₘ ρ C
  where
    ρ : ∀ {A} {MA : MType A} → ℳ ▷ MB ∋ₘ MA → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA
    ρ Z = ret D
    ρ (S x) = get x

Handleable : Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA → Set
Handleable (bnd E con) = Handleable E
Handleable (getₛ x) = ⊤
Handleable (setₛ x term) = ⊤
Handleable (ret term) = ⊤
Handleable _ = ⊥

handup : ∀ {A B} {MA : MType A} {MB : MType B} → MemoryOrder → (E : Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA) → Handleable E → Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MA
handup M (ret E) H = {!!}
handup Weak (bnd E C) H with handup Weak E H
... | res = {!!}
handup SC (bnd E C) H = {!!}
handup M (getₛ x) H = {!!}
handup M (setₛ x E) H = {!!}

data Value : Σ ⁏ ℳ ⁏ Γ ⊢ A → Set where
  V-ƛ    : {N : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ B} → Value (ƛ N)
  V-zero : Value {Σ} {ℳ} {Γ} `zero
  V-suc  : {V : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ} → Value V → Value (`suc V)
  V-ret  : {V : Σ ⁏ ℳ ⁏ Γ ⊢ A}  → (MA : MType A) → Value V → Value (ret {MA = MA} V)

--shrink : (E : ℳ ▷ MB ⁏ Γ ⊢ A) → Value E → ℳ ⁏ Γ ⊢ A
--shrink (ƛ E) (V-ƛ) = ƛ (shrink E)
--shrink `zero VE = `zero
--shrink (`suc E) (V-suc VE) = shrink E VE
--shrink (ret E) (V-ret MA VE) = ret (shrink E VE)
data Map : Shared → Set where
  ∅   : Map ∅
  _⊗_ : ∀ {A} {MA : MType A} {E : ∅ ⁏ ∅ ⁏ ∅ ⊢ A} → Map Σ → Value E → Map (Σ ▷ MA)

variable
  𝕞 𝕞' 𝕞'' : Map Σ

data State (Σ : Shared) (ℳ : Memory) (Γ : Context) (A : Type) : Set where
  _∥_ : Σ ⁏ ℳ ⁏ Γ ⊢ A → Map Σ → State Σ ℳ Γ A

lookupₛ : ∀ {A} {MA : MType A} → Map Σ → Σ ∋ₛ MA → Ω ⁏ ∅ ⁏ ∅ ⊢ A
lookupₛ (_⊗_ {E = E} 𝕞 VE) Z     = renameₛ (λ ()) E
lookupₛ (_⊗_ {E = E} 𝕞 VE) (S x) = lookupₛ 𝕞 x

shrink : ∀ {A} {MA : MType A} {E : Σ ⁏ ℳ ⁏ Γ ⊢ A} → Value E → Σ[ E' ∈ ∅ ⁏ ∅ ⁏ ∅ ⊢ A ] Value E'
shrink V-zero = `zero , V-zero
shrink (V-suc VE) with shrink {MA = `ℕ} VE
... | E' , VE'  = `suc _ , V-suc VE'

modify : ∀ {A} {MA : MType A} → Map Σ → Σ ∋ₛ MA → {E : Ω ⁏ ℳ ⁏ Γ ⊢ A} → Value E → Map Σ
modify {MA = MA} (𝕞 ⊗ VE) Z VE' = 𝕞 ⊗ (proj₂ $ shrink {MA = MA} VE')
modify (𝕞 ⊗ VE) (S x) VE' = modify 𝕞 x VE' ⊗ VE

data Step : State Σ ℳ Γ A → State Σ ℳ Γ A → Set where
  ξ-·₁ : {L L' : Σ ⁏ ℳ ⁏ Γ ⊢ A ⇒ B} {M : Σ ⁏ ℳ ⁏ Γ ⊢ A}
       → Step (L ∥ 𝕞) (L' ∥ 𝕞')
       → Step (L · M ∥ 𝕞) (L' · M ∥ 𝕞')

  ξ-·₂ : {V : Σ ⁏ ℳ ⁏ Γ ⊢ A ⇒ B} {M M' : Σ ⁏ ℳ ⁏ Γ ⊢ A}
       → Value V
       → Step (M ∥ 𝕞) (M' ∥ 𝕞')
       → Step (V · M ∥ 𝕞) (V · M' ∥ 𝕞')

  β-ƛ : ∀ {N : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ B} {W : Σ ⁏ ℳ ⁏ Γ ⊢ A}
      --→ Value W
      → Step ((ƛ N) · W ∥ 𝕞) (N [ W ] ∥ 𝕞)

--  ξ-ƛ : ∀ {M M' : ℳ ⁏ Γ ▷ A ⊢ B}
--      → Step M M'
--      → Step (ƛ M) (ƛ M')

  ξ-suc : {M M′ : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ}
        → Step (M ∥ 𝕞) (M′ ∥ 𝕞')
        → Step (`suc M ∥ 𝕞) (`suc M′ ∥ 𝕞')

  ξ-case : {L L′ : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ ℳ ⁏ Γ ⊢ A} {N : Σ ⁏ ℳ ⁏ Γ ▷ `ℕ ⊢ A}
         → Step (L ∥ 𝕞) (L′ ∥ 𝕞')
         → Step (case L M N ∥ 𝕞) (case L′ M N ∥ 𝕞')

  β-zero :  {M : Σ ⁏ ℳ ⁏ Γ ⊢ A} {N : Σ ⁏ ℳ ⁏ Γ ▷ `ℕ ⊢ A}
         → Step (case `zero M N ∥ 𝕞) (M ∥ 𝕞)

  β-suc : {V : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ} {M : Σ ⁏ ℳ ⁏ Γ ⊢ A} {N : Σ ⁏ ℳ ⁏ Γ ▷ `ℕ ⊢ A}
        → Value V
        → Step (case (`suc V) M N ∥ 𝕞) (N [ V ] ∥ 𝕞)

  β-μ : {N : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ A}
      → Step (μ N ∥ 𝕞) (N [ μ N ] ∥ 𝕞)

  ξ-ret  : ∀ {M M' : Σ ⁏ ℳ ⁏ Γ ⊢ A}
         → (MA : MType A)
         → Step (M ∥ 𝕞) (M' ∥ 𝕞')
         → Step (ret {MA = MA} M ∥ 𝕞) (ret M' ∥ 𝕞')

  ξ-bnd  : ∀ {M M' : Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA} {C : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MB}
         → Step (M ∥ 𝕞) (M' ∥ 𝕞')
         → Step (bnd M C ∥ 𝕞) (bnd M' C ∥ 𝕞')

  β-bndret : ∀ {A} {B} {MA : MType A} {MB : MType B}
               {V : Σ ⁏ ℳ ⁏ Γ ⊢ A} {C : Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MB}
           → Value V
           → Step (bnd (ret {MA = MA} V) C ∥ 𝕞) (C [ V ] ∥ 𝕞)

  --β-get : ∀ {A} {MA : MType A} {x : ℳ ∋ₘ MA}
  --      → Step (get x ∥ 𝕞) (ret {Σ} {ℳ} {Γ} {A} {!!} ∥ 𝕞)

--  ξ-set : ∀ {x : ℳ ∋ₘ MA} {E} {E'}
--        → Step {ℳ} {Γ} E E'
--        → Step (set x E) (set x E')

--  β-setret : ∀ {x : ℳ ∋ₘ MA} {E}
--           → Step {ℳ} {Γ} (set x E) (ret E)

  ξ-dcl₁ : ∀ {A B} {MA : MType A} {MB : MType B}
           {E E' : Σ ⁏ ℳ ⁏ Γ ⊢ A} {C : Σ ⁏ ℳ ▷ MA ⁏ Γ ⊢ `Cmd MB}
           → Step (E ∥ 𝕞) (E' ∥ 𝕞')
           → Step (dcl E C ∥ 𝕞) (dcl E' C ∥ 𝕞')

  ξ-dcl₂ : ∀ {A B} {MA : MType A} {MB : MType B}
            {E : Σ ⁏ ℳ ⁏ Γ ⊢ A} {C : Σ ⁏ ℳ ▷ MA ⁏ Γ ⊢ `Cmd MB}
         → Value E
         → Step (dcl E C ∥ 𝕞) (C [ E ]' ∥ 𝕞)

  β-getₛ : ∀ {A} {MA : MType A} {x : Σ ∋ₛ MA}
         → Step (getₛ x ∥ 𝕞) (ret (lookupₛ 𝕞 x) ∥ 𝕞)

  ξ-setₛ : ∀ {A} {MA : MType A} {x : Σ ∋ₛ MA} {E E' : Σ ⁏ ℳ ⁏ Γ ⊢ A}
         → Step (E ∥ 𝕞) (E' ∥ 𝕞')
         → Step (setₛ x E ∥ 𝕞) (setₛ x E' ∥ 𝕞')

  β-setₛ : ∀ {A} {MA : MType A} {x : Σ ∋ₛ MA} {E : Σ ⁏ ℳ ⁏ Γ ⊢ A}
         → (VE : Value E)
         → Step (setₛ x E ∥ 𝕞) (ret E ∥ modify 𝕞 x VE)

  ξ-handle : ∀ {A B} {MA : MType A} {MB : MType B} {E E' : Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA} {H : Σ ⁏ ℳ ⁏ Γ ⊢ (Hand MA ⇛ MB)}
           → Step (E ∥ 𝕞) (E' ∥ 𝕞')
           → Step (handle E H ∥ 𝕞) (handle E' H ∥ 𝕞')

  --β-dclret : ∀ {E : Σ ⁏ ℳ ⁏ Γ ⊢ A} {E' : Σ ⁏ ℳ ▷ MA ⁏ Γ ⊢ B}
  --         → (VE' : Value E')
  --         → Step (dcl E (ret {MA = MB} E')) (ret (shrink E' VE'))

data Progress (M : Σ ⁏ ℳ ⁏ Γ ⊢ A) (𝕞 : Map Σ) : Set where
  done : Value M → Progress M 𝕞
  step : ∀ {M' : Σ ⁏ ℳ ⁏ Γ ⊢ A} {𝕞' : Map Σ}
       → Step (M ∥ 𝕞) (M' ∥ 𝕞')
       → Progress M 𝕞

progress : (M : Σ ⁏ ∅ ⁏ ∅ ⊢ A) → (𝕞 : Map Σ) → Progress M 𝕞

progress (` ())

progress (ƛ M) _ = done V-ƛ

progress (L · M) 𝕞 with progress L 𝕞
... | step L—→L′        = step (ξ-·₁ L—→L′)
... | done (V-ƛ) with progress M 𝕞
...   | step M—→M′ = step (ξ-·₂ V-ƛ M—→M′)
...   | done VM    = step β-ƛ

progress `zero _ = done V-zero

progress (`suc M) 𝕞 with progress M 𝕞
... | step M—→M′ = step (ξ-suc M—→M′)
... | done VM    = done (V-suc VM)

progress (case L M N) 𝕞 with progress L 𝕞
... | step L—→L′      = step (ξ-case L—→L′)
... | done V-zero     = step β-zero
... | done (V-suc VL) = step (β-suc VL)

progress (μ M) _ = step β-μ

progress (ret {MA = MA} M) 𝕞 with progress M 𝕞
... | step M—→M′ = step (ξ-ret MA M—→M′)
... | done VM    = done (V-ret MA VM)

progress (bnd C₁ C₂) 𝕞 with progress C₁ 𝕞
... | step C₁—→C₁′       = step (ξ-bnd C₁—→C₁′)
... | done (V-ret MB VC) = step (β-bndret VC)

progress (dcl E C) 𝕞 with progress E 𝕞
... | step E—→E' = step (ξ-dcl₁ E—→E')
... | done VE    = step (ξ-dcl₂ VE)

progress (get ())

progress (getₛ x) 𝕞 = step β-getₛ

progress (setₛ x E) 𝕞 with progress E 𝕞
... | step E—→E′ = step (ξ-setₛ E—→E′)
... | done VE    = step (β-setₛ VE)

progress (handle E H) 𝕞 = {!!}

progress (handler Hs) 𝕞 = {!!}

data ProgramList (Σ : Shared) : Set where
  §ᵖ_  : Σ ⁏ ∅ ⁏ ∅ ⊢ A → ProgramList Σ
  _∷ᵖ_ : ProgramList Σ → Σ ⁏ ∅ ⁏ ∅ ⊢ A → ProgramList Σ

data CState : Map Σ → Set where
  _⟫_ : ProgramList Σ → (𝕞 : Map Σ) → CState 𝕞

data CStates : Set where
  §ᶜ_  : CState 𝕞 → CStates
  _∷ᶜ_ : CStates → CState 𝕞 → CStates

data StateList : ℕ → Set where
  base : CState 𝕞 → StateList zero
  head : ∀ {N} → StateList N → StateList (suc N)
  snoc : ∀ {N} → StateList (suc N) → StateList N → StateList (suc N)

data Allₚ {Σ} (P : ∀ {A} → Σ ⁏ ∅ ⁏ ∅ ⊢ A → Set) : ProgramList Σ → Set where
  §ₚ_  : ∀ {M : Σ ⁏ ∅ ⁏ ∅ ⊢ A}
       → P M
       → Allₚ P (§ᵖ M)
  _⊗ₚ_ : ∀ {M : Σ ⁏ ∅ ⁏ ∅ ⊢ A} {Ms}
       → Allₚ P Ms → P M
       → Allₚ P (Ms ∷ᵖ M)

data Allₛ {M} (P : StateList M → Set) : StateList (suc M) → Set where
  §ₛ_  : {s : StateList M}
       → P s
       → Allₛ P (head s)
  _⊗ₛ_ : {s : StateList M} {ss : StateList (suc M)}
       → Allₛ P ss → P s
       → Allₛ P (snoc ss s)

-- Recursive All for StateList.
data RAll (P : ∀ {Σ} {𝕞 : Map Σ} → CState 𝕞 → Set) : {M : ℕ} → StateList M → Set where
  base : ∀ {Σ} {𝕞 : Map Σ} {cs : CState 𝕞}
       → P cs
       → RAll P (base cs)
  head : ∀ {M} {s : StateList M}
       → RAll P s
       → RAll P (head s)
  snoc : ∀ {M} {s : StateList M} {ss}
       → RAll P ss → RAll P s
       → RAll P (snoc ss s)

data Step' : CState 𝕞 → CState 𝕞' → Set where
  head-β : ∀ {M M' : Σ ⁏ ∅ ⁏ ∅ ⊢ A} {𝕞 𝕞'}
         → Step  (M ∥ 𝕞)  (M' ∥ 𝕞')  → Step' (§ᵖ M ⟫ 𝕞)    (§ᵖ M' ⟫ 𝕞')
  head-ξ : ∀ {M M' : Σ ⁏ ∅ ⁏ ∅ ⊢ A} {𝕞 𝕞' Ms}
         → Step  (M ∥ 𝕞)  (M' ∥ 𝕞')  → Step' (Ms ∷ᵖ M ⟫ 𝕞) (Ms ∷ᵖ M' ⟫ 𝕞')
  tail-ξ : ∀ {M : Σ ⁏ ∅ ⁏ ∅ ⊢ A} {Ms Ms' 𝕞 𝕞'}
         → Step' (Ms ⟫ 𝕞) (Ms' ⟫ 𝕞') → Step' (Ms ∷ᵖ M ⟫ 𝕞) (Ms' ∷ᵖ M ⟫ 𝕞')

data AllStep' : CState 𝕞 → CStates → Set where
  §ₛ   : ∀ {Σ} {𝕞 : Map Σ} {c : CState 𝕞} {c' : CState 𝕞'}
       → Step' c c'
       → AllStep' c (§ᶜ c')
  _⊗ₛ_ : ∀ {Σ Σ'} {𝕞 : Map Σ} {𝕞' : Map Σ'}
           {c : CState 𝕞} {c' : CState 𝕞'} {c's : CStates}
       → Step' c c' → AllStep' c c's
       → AllStep' c (c's ∷ᶜ c')

--data CStep : {M : ℕ} → StateList M → StateList (suc M) → Set where
--  base : ∀ {𝕞 𝕞' : Map Σ} {x : CState 𝕞} {y : CState 𝕞'}
--       → Step' x y → CStep (base x) (head (base y))
--  head : ∀ {M} {s : StateList M} {t : StateList (suc M)}
--       → CStep s t → CStep (head s) (head t)
--  snoc : ∀ {M} {s : StateList M} {t : StateList (suc M)}
--           {ss : StateList (suc M)} {ts}
--       → CStep ss ts → CStep s t → CStep (snoc ss s) (snoc ts t)
--CStep (base x) s+ = Allₛ (λ {(base y) → Step' x y}) s+
--CStep (head s) (head t) = CStep s {!!}
--CStep (cons s ss) s+ = {!!}
AllStateValue : ∀ {M} → StateList M → Set
AllStateValue ss = RAll (λ {(P ⟫ 𝕞) → Allₚ Value P}) ss

allpos : CState 𝕞 → StateList 1
allpos cs@((§ᵖ N) ⟫ 𝕞) with progress N 𝕞
... | done VN = head (base cs)
... | step {M' = N'} {𝕞' = 𝕞'} N→N' = head (base ((§ᵖ N') ⟫ 𝕞'))
allpos ((Ns ∷ᵖ N) ⟫ 𝕞) with allpos (Ns ⟫ 𝕞) | progress N 𝕞
... | cs | done VN  = snoc cs (base (Ns ⟫ 𝕞))-- cs ∷ᶜ ((§ᵖ N) ⟫ 𝕞)
... | cs | step {M' = N'} {𝕞' = 𝕞'} N→N' = snoc cs (base ((§ᵖ N') ⟫ 𝕞')) -- cs ∷ᶜ ((§ᵖ N') ⟫ 𝕞')

-- CStep should be 'full'.
data CStep : ∀ {M : ℕ} → StateList M → StateList (suc M) → Set where
  base : ∀ {Σ} {𝕞 : Map Σ} {cs : CState 𝕞}
       → CStep (base cs) (allpos cs)

  head : ∀ {M} {s : StateList M} {t}
       → CStep s t
       → CStep (head s) (head t)

  snoc : ∀ {M} {s : StateList M} {t ss ts}
       → CStep ss ts → CStep s t
       → CStep (snoc ss s) (snoc ts t)

  init : ∀ {M} {ss : StateList (suc M)} {s ts}
       → CStep ss ts → AllStateValue s
       → CStep (snoc ss s) (snoc ts (head s))

  last : ∀ {M} {ss : StateList (suc M)} {s t}
       → AllStateValue ss → CStep s t
       → CStep (snoc ss s) (snoc (head ss) t)

_—→_ : ∀ (L : CState 𝕞) (M : CState 𝕞') → Set
L —→ M = Step' L M

data Progress' (P : ProgramList Σ) (𝕞 : Map Σ) : Set where
  done : Allₚ Value P → Progress' P 𝕞
  step : ∀ {P' : ProgramList Σ} {𝕞' : Map Σ}
       → Step' (P ⟫ 𝕞) (P' ⟫ 𝕞')
       → Progress' P 𝕞

data Progressₙ {M : ℕ} (s : StateList M) : Set where
  done : AllStateValue s → Progressₙ s
  step : ∀ {t} → CStep s t → Progressₙ s
--  head-step : ∀ {M} {s : StateList M}
--            → Progressₙ s → Progressₙ (head s)
--  snoc-step : ∀ {M} {s : StateList M} {ss}
--            → Progressₙ s → Progressₙ (snoc ss s)

--allprogress : ∀ {N} → (s : StateList N) → Progressₙ s

progress' : (P : ProgramList Σ) → (𝕞 : Map Σ) → Progress' P 𝕞
progress' (§ᵖ M) 𝕞 with progress M 𝕞
... | done VM = done (§ₚ VM)
... | step M—→M' = step (head-β M—→M')
progress' (Ms ∷ᵖ M) 𝕞 with progress' Ms 𝕞
... | step Ms—→Ms' = step (tail-ξ Ms—→Ms')
... | done AVM with progress M 𝕞
...   | done VM = done (AVM ⊗ₚ VM)
...   | step M—→M' = step (head-ξ M—→M')

progressₙ : {M : ℕ} → (s : StateList M) → Progressₙ s
progressₙ (base (P ⟫ 𝕞)) with progress' P 𝕞
... | done AVP = done (base AVP)
... | step P→P' = step base
progressₙ (head s) with progressₙ s
... | done AVs = done (head AVs)
... | step s→t = step (head s→t)
progressₙ (snoc ss s) with progressₙ ss | progressₙ s
progressₙ (snoc ss s) | done V1 | done V2 = done (snoc V1 V2)
progressₙ (snoc ss s) | done Vss | step s→t = step (last Vss s→t)
progressₙ (snoc ss s) | step ss→ | done Vs = step (init ss→ Vs)
progressₙ (snoc ss s) | step ss→ | step s→ = step (snoc ss→ s→)
--progressₙ (base (P ⟫ 𝕞)) with progress' P 𝕞
--... | pg = base-step pg
--progressₙ (head s) with progressₙ s
--... | pg = head-step pg
--progressₙ (snoc ss s) with progressₙ s
--... | pg = snoc-step pg

infix  2 _—↠_
infix  1 start_
infixr 2 _—→⟨_⟩_
infix  3 _end

data _—↠_ : CState 𝕞 → CState 𝕞' → Set where
  _end : (M : CState 𝕞)
       → M —↠ M

  _—→⟨_⟩_ : (L : CState 𝕞) {M : CState 𝕞'} {N : CState 𝕞''}
          → L —→ M
          → M —↠ N
          → L —↠ N

data _⇉_ : ∀ {M N} → StateList M → StateList N → Set where
  _end : ∀ {M} → (s : StateList M) → s ⇉ s
  _⇉⟨_⟩_ : ∀ {M N} → (s : StateList M) → {t : StateList (suc M)} → {u : StateList N}
         → CStep s t
         → t ⇉ u
         → s ⇉ u

data Gas : Set where
  gas : ℕ → Gas

start_ : {M : CState 𝕞} {N : CState 𝕞'}
       → M —↠ N
       → M —↠ N
start M—↠N = M—↠N

data Finished {Σ} {𝕞 : Map Σ} : CState 𝕞 → Set where
  done       : ∀ {Ms} → Allₚ Value Ms → Finished (Ms ⟫ 𝕞)
  out-of-gas : ∀ {N} → Finished N

data Finished' : {M : ℕ} → StateList M → Set where
  done       : ∀ {M} {s : StateList M} → AllStateValue s → Finished' s
  out-of-gas : ∀ {M} {s : StateList M} → Finished' s

data Steps : CState 𝕞 → Set where
  steps : ∀ {L : CState 𝕞} {N : CState 𝕞'}
        → L —↠ N → Finished N → Steps L

data Steps' : {M : ℕ} → StateList M → Set where
  steps : ∀ {M N} {s : StateList M} {t : StateList N}
        → s ⇉ t → Finished' t → Steps' s

eval : Gas → (L : CState 𝕞) → Steps L
eval (gas zero) L = steps (L end) out-of-gas
eval (gas (suc x)) L@(T ⟫ 𝕞)  with progress' T 𝕞
... | done VL   = steps (L end) (done VL)
... | step {M} {𝕞'} L—→M with eval (gas x) (M ⟫ 𝕞')
...   | steps M—↠N fin = steps (L —→⟨ L—→M ⟩ M—↠N) fin

evalₙ : {M : ℕ} → Gas → (s : StateList M) → Steps' s
evalₙ (gas zero) s = steps (s end) out-of-gas
evalₙ (gas (suc x)) s with progressₙ s
... | done AVs = steps (s end) (done AVs)
... | step {t} s→t with evalₙ (gas x) t
...   | steps t→u fin = steps (s ⇉⟨ s→t ⟩ t→u) fin

--data _—↣_ : ∀ {Σ Γ A} → State Σ Γ A → State Σ Γ A → Set where
--  _stop : ∀ {Σ Γ A} (S : State Σ Γ A)
--        → S —↣ S
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
--data Finished' {Σ Γ A} (S : State Σ Γ A) : Set where
--  done       : Final Σ S → Finished' S
--  out-of-gas : Finished' S
--
--
--data Steps' : ∀ {Σ A} → State Σ ∅ A → Set where
--  steps : ∀ {Σ A} {S T : State Σ ∅ A}
--        → S —↣ T → Finished' T → Steps' S
--
--data EvalTo : ∀ {Σ} → State Σ ∅ ok → State Σ ∅ ok → Set where
--  evalto : ∀ {Σ} → {S T : State Σ ∅ ok} → S —↣ T → Final Σ T → EvalTo S T
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
