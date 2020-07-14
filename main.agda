open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
--open import Category.Monad.State
--open import Level

module main where

infix  4 _؛_⊢_
infix  4 _∋_
infix  4 _∋ₛ_
infix  5 _,_
infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_
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
  data _؛_⊢_ : Store → Context → Type → Set where
    ` : ∀ {Σ Γ A}
       → Γ ∋ A
       ------------
       → Σ ؛ Γ ⊢ A

    ƛ : ∀ {Σ Γ A B}
       → Σ ؛ Γ , A ⊢ B
       --------------------
       → Σ ؛ Γ ⊢ A ⇒ B
    -- ⇒-E
    _·_ : ∀ {Σ Γ A B}
        → Σ ؛ Γ ⊢ A ⇒ B   → Σ ؛ Γ ⊢ A
        ------------------------------
        → Σ ؛ Γ ⊢ B
    -- ℕ-I₁
    `zero : ∀ {Σ Γ}
          --------------
          → Σ ؛ Γ ⊢ `ℕ
    -- ℕ-I₂
    `suc : ∀ {Σ Γ}
         → Σ ؛ Γ ⊢ `ℕ
         ---------------
         → Σ ؛ Γ ⊢ `ℕ
    -- ℕ-E
    case : ∀ {Σ Γ A}
         → Σ ؛ Γ ⊢ `ℕ   → Σ ؛ Γ ⊢ A   → Σ ؛ Γ , `ℕ ⊢ A
         ----------------------------------------------
         → Σ ؛ Γ ⊢ A

    μ : ∀ {Σ Γ A}
      → Σ ؛ Γ , A ⊢ A
      -----------------
      → Σ ؛ Γ ⊢ A

    cmd : ∀ {Σ Γ}
        → Σ ؛ Γ ⊩ ok
        → Σ ؛ Γ ⊢ `Cmd

  data _؛_⊩_ : Store → Context → CType → Set where
    ret : ∀ {Σ Γ}
        → Σ ؛ Γ ⊢ `ℕ
        → Σ ؛ Γ ⊩ ok
    bnd : ∀ {Σ Γ}
        → Σ ؛ Γ ⊢ `Cmd → Σ ؛ Γ , `ℕ ⊩ ok
        → Σ ؛ Γ ⊩ ok
    dcl : ∀ {Σ Γ a}
        → Σ ؛ Γ ⊢ `ℕ → (Σ , a) ؛ Γ ⊩ ok
        → Σ ؛ Γ ⊩ ok
    get : ∀ {Σ Γ}
        → (a : Id)
        → (Σ , a) ؛ Γ ⊩ ok
    set : ∀ {Σ Γ}
        → (a : Id) → (Σ , a) ؛ Γ ⊢ `ℕ
        → (Σ , a) ؛ Γ ⊩ ok

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

#_ : ∀ {Σ Γ} → (n : ℕ) → Σ ؛ Γ ⊢ lookup Γ n
# n = ` (count n)

ext : ∀ {Γ Δ}
    → (∀ {A}   → Γ ∋ A     → Δ ∋ A)
    -----------------------------------
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Σ Γ Δ}
       → (∀ {A} → Γ ∋ A → Δ ∋ A)
       ----------------------------------
       → (∀ {A} → Σ ؛ Γ ⊢ A → Σ ؛ Δ ⊢ A)
rename ρ (` w)        = ` (ρ w)
rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
rename ρ `zero        = `zero
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ M)        = μ (rename (ext ρ) M)

exts : ∀ {Σ Γ Δ}
     → (∀ {A}   →     Γ ∋ A → Σ ؛ Δ ⊢ A)
     → (∀ {A B} → Γ , B ∋ A → Σ ؛ Δ , B ⊢ A)
exts ρ Z     = ` Z
exts ρ (S x) = rename S (ρ x)

subst : ∀ {Σ Γ Δ}
      → (∀ {A} → Γ ∋ A → Σ ؛ Δ ⊢ A)
      -------------------------
      → (∀ {A} → Σ ؛ Γ ⊢ A → Σ ؛ Δ ⊢ A)
subst σ (` x) = σ x
subst σ (ƛ N) = ƛ (subst (exts σ) N)
subst σ (L · M) = (subst σ L) · (subst σ M)
subst σ `zero = `zero
subst σ (`suc N) = `suc (subst σ N)
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N) = μ (subst (exts σ) N)

_[_] : ∀ {Σ Γ A B}
     → Σ ؛ Γ , B ⊢ A → Σ ؛ Γ ⊢ B
     -------------------
     → Σ ؛ Γ ⊢ A
_[_] {Σ} {Γ} {A} {B} N M = subst {Σ} {Γ , B} {Γ} σ N
  where
    σ : ∀ {A} → Γ , B ∋ A → Σ ؛ Γ ⊢ A
    σ Z      = M
    σ (S x) = ` x

data Value : ∀ {Σ Γ A} → Σ ؛ Γ ⊢ A → Set where
  V-ƛ    : ∀ {Σ Γ A B} {N : Σ ؛ Γ , A ⊢ B} → Value (ƛ N)
  V-zero : ∀ {Σ Γ} → Value (`zero {Σ} {Γ})
  V-suc  : ∀ {Σ Γ} {V : Σ ؛ Γ ⊢ `ℕ} → Value V → Value (`suc V)

infix 2 _—→_

data _—→_ : ∀ {Σ Γ A} → (Σ ؛ Γ ⊢ A) → (Σ ؛ Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Σ Γ A B} {L L' : Σ ؛ Γ ⊢ A ⇒ B} {M : Σ ؛ Γ ⊢ A}
       → L —→ L'
       → L · M —→ L' · M

  ξ-·₂ : ∀ {Σ Γ A B} {V : Σ ؛ Γ ⊢ A ⇒ B} {M M' : Σ ؛ Γ ⊢ A}
       → Value V
       → M —→ M'
       → V · M —→ V · M'

  β-ƛ : ∀ {Σ Γ A B} {N : Σ ؛ Γ , A ⊢ B} {W : Σ ؛ Γ ⊢ A}
       → Value W
       --------------------
       → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Σ Γ} {M M′ : Σ ؛ Γ ⊢ `ℕ}
        → M —→ M′
        -----------------
        → `suc M —→ `suc M′

  ξ-case : ∀ {Σ Γ A} {L L′ : Σ ؛ Γ ⊢ `ℕ} {M : Σ ؛ Γ ⊢ A} {N : Σ ؛ Γ , `ℕ ⊢ A}
         → L —→ L′
           -------------------------
           → case L M N —→ case L′ M N

  β-zero :  ∀ {Σ Γ A} {M : Σ ؛ Γ ⊢ A} {N : Σ ؛ Γ , `ℕ ⊢ A}
         -------------------
         → case `zero M N —→ M

  β-suc : ∀ {Σ Γ A} {V : Σ ؛ Γ ⊢ `ℕ} {M : Σ ؛ Γ ⊢ A} {N : Σ ؛ Γ , `ℕ ⊢ A}
        → Value V
        ----------------------------
        → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Σ Γ A} {N : Σ ؛ Γ , A ⊢ A}
      ----------------
      → μ N —→ N [ μ N ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Σ Γ A} → (Σ ؛ Γ ⊢ A) → (Σ ؛ Γ ⊢ A) → Set where

  _∎ : ∀ {Σ Γ A} (M : Σ ؛ Γ ⊢ A)
     ------
     → M —↠ M

  _—→⟨_⟩_ : ∀ {Σ Γ A} (L : Σ ؛ Γ ⊢ A) {M N : Σ ؛ Γ ⊢ A}
          → L —→ M
          → M —↠ N
          ------
          → L —↠ N

begin_ : ∀ {Σ Γ A} {M N : Σ ؛ Γ ⊢ A}
  → M —↠ N
  ------
  → M —↠ N
begin M—↠N = M—↠N

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
