module Dual.Syntax.Implication where

open import Dual.Syntax.Core
open import Dual.Syntax.Values
open import Dual.Syntax.Substitution

infixr 7 _⇒ⱽ_
infixr 7 _⇒ᴺ_
infix  5 ƛⱽ_
infix  5 ƛᴺ_
infixl 7 _·ⱽ_
infixl 7 _·ᴺ_

_⇒ⱽ_ : Type → Type → Type
A ⇒ⱽ B = `¬ (A `× `¬ B)

_⇒ᴺ_ : Type → Type → Type
A ⇒ᴺ B = `¬ A `+ B

ƛⱽ_ : ∀ {Γ Θ A B}
  → Γ , A ⟶ Θ ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ⱽ B 

ƛᴺ_ : ∀ {Γ Θ A B}
  → Γ , A ⟶ Θ ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ᴺ B

_·ⱽ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ⱽ B ∣ Γ ⟶ Θ 

_·ᴺ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ᴺ B ∣ Γ ⟶ Θ 

ƛⱽ N = not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ intΓᵗ (wkΓᵗ N) ⟩ ]) ]) ]

ƛᴺ N = μθ (inl⟨ not[ μγ(inr⟨ wkΘᵗ N ⟩ ● θ 0) ] ⟩ ● θ 0) 

M ·ⱽ N = not⟨ `⟨ M , not[ N ] ⟩ ⟩

M ·ᴺ N = `[ not⟨ M ⟩ , N ]
