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

cmdᶜ : ∀ {Σ Γ} → Σ ⁏ Γ ⊩ ok
cmdᶜ = set "x" {!!} 2+2ᶜ
