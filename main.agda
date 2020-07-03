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
...            | yes _ = V
...            | no  _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
...                  | yes _ = ƛ x ⇒ N
...                  | no  _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
...                                     | yes _ = case L [ y := V ] [zero⇒ M [ y := V ]
                                                                    |suc x ⇒ N ]
...                                     | no  _ = case L [ y := V ] [zero⇒ M [ y := V ]
                                                                    |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
...                | yes _ = μ x ⇒ N
...                | no  _ = μ x ⇒ N [ y := V ]

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M}
       → L —→ L′
  -----------------
       → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
       → Value V
       → M —→ M′
  -----------------
       → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
      → Value V
  ------------------------------
      → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
        → M —→ M′
  ------------------
        → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
         → L —→ L′
  -----------------------------------------------------------------
         → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
  ----------------------------------------
         → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
        → Value V
  ---------------------------------------------------
        → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
  ------------------------------
      → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
     ---------
     → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
        → L —→ M
        → M —↠ N
        ---------
        → L —↠ N

begin_ : ∀ {M N}
       → M —↠ N
       ------
       → M —↠ N
begin M—↠N = M—↠N


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

infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
      → ∅ , x ⦂ A ⊢ N ⦂ B
      → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)
  C-zero : Canonical `zero ⦂ `ℕ
  C-suc  : ∀ {V} → Canonical V ⦂ `ℕ → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A}
          → ∅ ⊢ V ⦂ A
          → Value V
          -----------
          → Canonical V ⦂ A
canonical (⊢` ())          ()
canonical (⊢ƛ ⊢N)          V-ƛ        =  C-ƛ ⊢N
canonical (⊢L · ⊢M)        ()
canonical ⊢zero            V-zero     =  C-zero
canonical (⊢suc ⊢V)        (V-suc VV) =  C-suc (canonical ⊢V VV)
canonical (⊢case ⊢L ⊢M ⊢N) ()
canonical (⊢μ ⊢M)          ()

value : ∀ {M A}
      → Canonical M ⦂ A
      ----------------
      → Value M
value (C-ƛ ⊢N)    =  V-ƛ
value C-zero      =  V-zero
value (C-suc CM)  =  V-suc (value CM)

typed : ∀ {M A}
      → Canonical M ⦂ A
      ---------------
      → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N)    =  ⊢ƛ ⊢N
typed C-zero      =  ⊢zero
typed (C-suc CM)  =  ⊢suc (typed CM)


data Progress (M : Term) : Set where
  step : ∀ {N} → M —→ N → Progress M
  done : Value M → Progress M

progress : ∀ {M A}
         → ∅ ⊢ M ⦂ A
         ----------
         → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ VL M—→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              =  step β-zero
...   | C-suc CL                            =  step (β-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ

ext : ∀ {Γ Δ}
    → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
    → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
       → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
       ----------------------------------
       → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
  ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
                where
                  ρ : ∀ {z C}
                    → ∅ ∋ z ⦂ C
                    ---------
                    → Γ ∋ z ⦂ C
                  ρ ()

drop : ∀ {Γ x M A B C}
     → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
     --------------------------
     → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
                                  where
                                    ρ : ∀ {z C}
                                      → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
                                      -------------------------
                                      → Γ , x ⦂ B ∋ z ⦂ C
                                    ρ Z                 =  Z
                                    ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
                                    ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z

swap : ∀ {Γ x y M A B C}
     → x ≢ y
     → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
     --------------------------
     → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
                                          where
                                            ρ : ∀ {z C}
                                              → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
                                              --------------------------
                                              → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
                                            ρ Z                   =  S x≢y Z
                                            ρ (S z≢x Z)           =  Z
                                            ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)

subst : ∀ {Γ x N V A B}
      → ∅ ⊢ V ⦂ A
      → Γ , x ⦂ A ⊢ N ⦂ B
      --------------------
      → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           =  weaken ⊢V
... | no  x≢y         =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        =  ⊥-elim (x≢y refl)
... | no  _           =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        =  ⊢ƛ (drop ⊢N)
... | no  x≢y         =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)    =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        =  ⊢zero
subst ⊢V (⊢suc ⊢M)    =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        =  ⊢μ (drop ⊢M)
... | no  x≢y         =  ⊢μ (subst ⊢V (swap x≢y ⊢M))

preserve : ∀ {M N A}
         → ∅ ⊢ M ⦂ A
         → M —→ N
         ----------
         → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

data Gas : Set where
  gas : ℕ → Gas

data Finished (N : Term) : Set where
  done       : Value N → Finished N
  out-of-gas :           Finished N

data Steps (L : Term) : Set where
  steps : ∀ {N} → L —↠ N → Finished N → Steps L

eval : ∀ {L A}
     → Gas
     → ∅ ⊢ L ⦂ A
     ---------
     → Steps L
eval {L} (gas zero)    ⊢L                             =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                         =  steps (L ∎) (done VL)
... | step L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                               =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
