open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Function using (id; _$_; _∘_)
open import Data.List using (List; _∷_; [])
open import main

module proof where

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ fb = fmap (λ _ → x) fb

open Functor

_<$>_ : ∀ {F : Set → Set} {A B} {{FF : Functor F}} → (A → B) → F A → F B
_<$>_ {{FF = FF}} f fa = fmap FF f fa

record Lift {A : Set} {F : Set → Set} {{FF : Functor F}} (P : A → Set) (fa : F A) : Set where
  field
    witness     : F (Σ[ a ∈ A ] P a)
    corresponds : fa ≡ (proj₁ <$> witness)

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

emptyMap : Map ∅
emptyMap = ∅

cstate = § get&inc ⟫ emptyMap
