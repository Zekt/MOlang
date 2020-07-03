open import main

module terms where

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
        where
          ∋x = Z

⊢ptt : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢ptt = (⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S (λ()) Z)) (⊢` Z) (⊢suc ((⊢` (S (λ()) (S (λ()) (S (λ()) Z))))
     · ⊢` Z · ⊢` (S (λ()) Z)))))) · ⊢suc (⊢suc ⊢zero)) · ⊢suc (⊢suc ⊢zero)
