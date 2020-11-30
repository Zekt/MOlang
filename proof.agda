open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (id; _$_; _∘_)
open import Data.List using (List; _∷_; [])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import main

module proof where

--record Functor (F : Set → Set) : Set₁ where
  --field
    --fmap : ∀ {A B} → (A → B) → F A → F B
--
  --_<$_ : ∀ {A B} → A → F B → F A
  --x <$ fb = fmap (λ _ → x) fb
--
--open Functor
--
--_<$>_ : ∀ {F : Set → Set} {A B} {{FF : Functor F}} → (A → B) → F A → F B
--_<$>_ {{FF = FF}} f fa = fmap FF f fa
--
--Lift : {A : Set} {a : A} {F : A → Set} (P : A → Set) (fa : F a) → Set
--Lift {A} {a} {F} P fa = P a

All : ∀ {L : CState 𝕞} {M : CState 𝕞'} → (∀ {Σ} → Map Σ → Set) → L —↠ M → Set
All P (x ⟫ 𝕞 end) = P 𝕞
All P (x ⟫ 𝕞 —→⟨ L—→M ⟩ M—↠N) = P 𝕞 × All P M—↠N

Always : ∀ {Σ} {𝕞 : Map Σ} → (∀ {Σ} → Map Σ → Set) → CState 𝕞 → Gas → Set
Always P cs g with eval g cs
... | steps L—↠M FN = All P L—↠M

_>>_ : ∀ {A B : Type} {MA : MType A} {MB : MType B}
      → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MA → Σ ⁏ ℳ ⁏ Γ ▷ A ⊢ `Cmd MB
      → Σ ⁏ ℳ ⁏ Γ ⊢ `Cmd MB
M >> N = bnd M N

sucμ : Σ ⁏ ∅ ⁏ ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : Σ ⁏ ℳ ⁏ Γ ⊢ Ch A
twoᶜ = ƛ (ƛ (# 1 · (# 1 · # 0)))

plusᶜ : ∀ {Σ ℳ Γ A} → Σ ⁏ ℳ ⁏ Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ (ƛ (ƛ (ƛ (# 3 · # 1 · (# 2 · # 1 · # 0)))))

sucᶜ : ∀ {Σ ℳ Γ} → Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ (`suc (# 0))

2+2ᶜ : Σ ⁏ ℳ ⁏ Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

get&inc : ∅ ⁏ ∅ ⁏ ∅ ⊢ `Cmd `ℕ
get&inc = dcl {MA = `ℕ} 2+2ᶜ (do get Z
                                 ret (`suc # 0))

get&incₛ : (∅ ▷ `ℕ ▷ `ℕ) ⁏ ∅ ⁏ ∅ ⊢ `Cmd `ℕ
get&incₛ = do getₛ Z
              setₛ Z (`suc # 0)

emptyMap : Map ∅
emptyMap = ∅

oneMap : Map (∅ ▷ `ℕ ▷ `ℕ)
oneMap = (∅ ⊗ V-suc (V-suc V-zero)) ⊗ (V-suc (V-suc V-zero))

cstate = §ᵖ get&inc ⟫ emptyMap

cstate2 = (§ᵖ get&incₛ ∷ᵖ get&incₛ) ∷ᵖ get&incₛ ⟫ oneMap

Has2InMap : ∀ {Σ} → Map Σ → Set
Has2InMap (_⊗_ {E = `suc `suc `zero} M VE) = ⊤
Has2InMap ∅ = ⊥
Has2InMap (_⊗_ {E = _} M VE) = Has2InMap M

Cstate2Has2InMap : Always Has2InMap cstate2 (gas 100)
Cstate2Has2InMap = {!!}
