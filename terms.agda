open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (id; _$_; _∘_)
open import Data.List using (List; _∷_; [])
open import main

module terms where

sucμ : ∅ ⁏ ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

M₂ : ∅ ⁏ ∅ ▷ `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ (# 1 · (# 1 · # 0))

M : ∅ ⁏ ∅ ▷ `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M = # 0

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Σ Γ A} → Σ ⁏ Γ ⊢ Ch A
twoᶜ = ƛ (ƛ (# 1 · (# 1 · # 0)))

plusᶜ : ∀ {Σ Γ A} → Σ ⁏ Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ (ƛ (ƛ (ƛ (# 3 · # 1 · (# 2 · # 1 · # 0)))))

sucᶜ : ∀ {Σ Γ} → Σ ⁏ Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ (`suc (# 0))

2+2ᶜ : ∀ {Σ Γ} → Σ ⁏ Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

get&inc : ∀ {ℳ Γ} → ℳ ⁏ Γ ⊢ `Cmd `ℕ
get&inc = dcl {MA = `ℕ} 2+2ᶜ (bnd (get Z) (ret (`suc # 0)))

get&incx : (E : ℳ ⁏ Γ ⊢ `ℕ) → ℳ ⁏ Γ ⊢ `Cmd `ℕ
get&incx E = dcl {MA = `ℕ} E (bnd (get Z) (ret (`suc # 0)))
--
--prf-get&incx : ∀ (E : (∅ , "counter") ⁏ ∅ ⊢ `ℕ) → (VE : Value (∅ , "counter") E)
--             → ∃[ C ] EvalTo (get&incx E VE) (C ⟪ S ⟫ (∅ ⊗ "counter" ↪ ⟨ E , VE ⟩) ⊗ "counter" ↪ (renameN ⟨ `suc E , V-suc VE ⟩) )
--prf-get&incx E VE = ⟨ ret (`suc E) , evalto
--    (bnd (cmd (get "counter" Z)) (set "counter" Z (`suc ` Z)) ⟪(λ {a} x → x) ⟫ ∅ ⊗ "counter" ↪ ⟨ E , VE ⟩
--  —↦⟨ ξ-bndcmd (β-get {!!} {!!}) ⟩
--    bnd (cmd (ret E)) (set "counter" Z (`suc ` Z)) ⟪ (λ {a} x → x)⟫ ∅ ⊗ "counter" ↪ ⟨ E , VE ⟩
--  —↦⟨ β-bndret VE ⟩
--    set "counter" Z (`suc E) ⟪ (λ {a} x → x) ⟫ ∅ ⊗ "counter" ↪ ⟨ E , VE ⟩
--  —↦⟨ β-setret (V-suc VE) ⟩
--    (ret (`suc E) ⟪ (λ {a} x → S x) ⟫ (∅ ⊗ "counter" ↪ ⟨ E , VE ⟩) ⊗ "counter" ↪ renameN (⟨ `suc E , V-suc VE ⟩))
--  stop)
--  (F-ret (V-suc VE)) ⟩
--data IdIs (Σ : Store) : CState Σ → Id → (Σ ⁏ ∅ ⊢ `ℕ) → Set where
--  idis : ∀ {PL : ProgramList Σ} {μ : Map Σ} → (name : Id)
--       → (V : Σ ⁏ ∅ ⊢ `ℕ) → (VE : Value Σ V) → (μ∋i : μ ∋ₘ name ↪ ⟨ V , VE ⟩)
--       → IdIs Σ (PL ⟦ id ⟧ μ) name V
--
--prf-get&inc : ∀ {CS' : CState (∅ , "counter")}
--            → Final* (∅ , "counter") CS'
--            → StepCS* ((get&inc ∷ get&inc ∷ []) ⟦ id ⟧ (∅ ⊗ "counter" ↪ ⟨ `zero , V-zero ⟩)) CS'
--            → IdIs (∅ , "counter") CS' "counter" (`suc `suc `zero)
--prf-get&inc fin stepcs = {!!}
