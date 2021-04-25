module Dual.Syntax.ContextandVars (T : Set) where

infix  4 _∋_
infixl 5 _,_

infix  9 `S


data Context : Set where
  ∅ : Context
  _,_ : Context → T → Context


data _∋_ : Context → T → Set where

  `Z : ∀ {Γ A}
      -------------
    → Γ , A ∋ A

  `S : ∀ {Γ A B}
    → Γ ∋ A
      -------------
    → Γ , B ∋ A