open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])
--open import Category.Monad.State
--open import Level

module main where

infix  4 _⊢_
infix  4 _∋_
infix  5 _,_
infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixr 7 _⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 _[_:=_]

data Type : Set where
  _⇒_  : Type → Type → Type
  `ℕ   : Type
  `Cmd : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
    → Γ , A ∋ A

  S : ∀ {Γ A B}
    → Γ ∋ A → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  ` : ∀ {Γ A}
     → Γ ∋ A
     ------------
     → Γ ⊢ A

  ƛ : ∀ {Γ A B}
     → Γ , A ⊢ B
     --------------------
     → Γ ⊢ A ⇒ B
  -- ⇒-E
  _·_ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ A
      -------------
      → Γ ⊢ B
  -- ℕ-I₁
  `zero : ∀ {Γ}
        --------------
        → Γ ⊢ `ℕ
  -- ℕ-I₂
  `suc : ∀ {Γ}
       → Γ ⊢ `ℕ
       ---------------
       → Γ ⊢ `ℕ
  -- ℕ-E
  `case : ∀ {Γ A}
        → Γ ⊢ `ℕ
        → Γ ⊢ A
        → Γ , `ℕ ⊢ A
        -------------
        → Γ ⊢ A

  `μ : ∀ {Γ A}
     → Γ , A ⊢ A
     -----------------
     → Γ ⊢ A

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
--data Value : Term → Set where
--  V-ƛ    : ∀ {x N}         → Value (ƛ x ⇒ N)
--  V-zero :                   Value `zero
--  V-suc  : ∀ {V} → Value V → Value (`suc V)
--  V-cmd  : ∀ {C} → Value (cmd C)
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
--ext : ∀ {Γ Δ}
--    → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
--    -----------------------------------------------------
--    → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
--ext ρ Z           =  Z
--ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)
--
--rename : ∀ {Γ Δ}
--       → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
--       ----------------------------------
--       → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
--rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
--rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
--rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
--rename ρ ⊢zero             =  ⊢zero
--rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
--rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
--rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)
--
--weaken : ∀ {Γ M A}
--  → ∅ ⊢ M ⦂ A
--  ----------
--  → Γ ⊢ M ⦂ A
--weaken {Γ} ⊢M = rename ρ ⊢M
--                where
--                  ρ : ∀ {z C}
--                    → ∅ ∋ z ⦂ C
--                    ---------
--                    → Γ ∋ z ⦂ C
--                  ρ ()
--
--drop : ∀ {Γ x M A B C}
--     → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
--     --------------------------
--     → Γ , x ⦂ B ⊢ M ⦂ C
--drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
--                                  where
--                                    ρ : ∀ {z C}
--                                      → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
--                                      -------------------------
--                                      → Γ , x ⦂ B ∋ z ⦂ C
--                                    ρ Z                 =  Z
--                                    ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
--                                    ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z
--
--swap : ∀ {Γ x y M A B C}
--     → x ≢ y
--     → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
--     --------------------------
--     → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
--swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
--                                          where
--                                            ρ : ∀ {z C}
--                                              → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
--                                              --------------------------
--                                              → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
--                                            ρ Z                   =  S x≢y Z
--                                            ρ (S z≢x Z)           =  Z
--                                            ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
--
--subst : ∀ {Γ x N V A B}
--      → ∅ ⊢ V ⦂ A
--      → Γ , x ⦂ A ⊢ N ⦂ B
--      --------------------
--      → Γ ⊢ N [ x := V ] ⦂ B
--subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
--... | yes _           =  weaken ⊢V
--... | no  x≢y         =  ⊥-elim (x≢y refl)
--subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
--... | yes refl        =  ⊥-elim (x≢y refl)
--... | no  _           =  ⊢` ∋x
--subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
--... | yes refl        =  ⊢ƛ (drop ⊢N)
--... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
--subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
--subst ⊢V ⊢zero        =  ⊢zero
--subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
--subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
--... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
--... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
--subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
--... | yes refl        =  ⊢μ (drop ⊢M)
--... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))
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
