open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (id; _$_; _∘_)
open import main

module terms where


infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

sucμ : ∅ ⁏ ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

M₂ : ∅ ⁏ ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ (# 1 · (# 1 · # 0))

M : ∅ ⁏ ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
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

cmdᶜ : ∀ {Σ Γ} → (Σ , "x") ⁏ Γ ⊩ ok
cmdᶜ = bnd (cmd (set "x" Z 2+2ᶜ)) (get "x" Z)

S1 : State (∅ , "x") ∅ ok
S1 = cmdᶜ ⟪ id ⟫ (∅ ⊗ "x" ↪ _)


get&inc : ∀ {Σ Γ} → (Σ , "counter") ⁏ Γ ⊩ ok
get&inc = bnd (cmd (get "counter" Z)) (set "counter" Z (`suc # 0))

get&incx : (E : (∅ , "counter") ⁏ ∅ ⊢ `ℕ) → (VE : Value (∅ , "counter") E) → State (∅ , "counter") ∅ ok
get&incx E VE = get&inc ⟪ id ⟫ ∅ ⊗ "counter" ↪ ⟨ E , VE ⟩

prf-get&incx : ∀ (E : (∅ , "counter") ⁏ ∅ ⊢ `ℕ) → (VE : Value (∅ , "counter") E)
             → ∃[ C ] EvalTo (get&incx E VE) (C ⟪ id ⟫ ∅ ⊗ "counter" ↪ ⟨ `suc E , V-suc VE ⟩ )
prf-get&incx E VE = ⟨ {!  !} , evalto {!!} {!!} ⟩
