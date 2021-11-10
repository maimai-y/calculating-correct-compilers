module ccc-5lam where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)

data Value : Set
Env : Set
data Expr : Value → Env → Set

-- the following variables automatically become implicit arguments
variable
  α α₁ α₂ σ : Value
  Ε Ε′ : Env
  n m : ℕ

data Value where
  Num : (n : ℕ) → Value
  Clo : (exp : Expr α Ε) → (env : Env) → Value

Env = List Value

-- variables
data var : (α : Value) (Ε : Env) → Set where
  zero : var α (α ∷ Ε)
  suc  : (x : var α Ε) → var α (σ ∷ Ε)

data Expr where
  Val : (n : ℕ) → Expr (Num n) Ε
  Add : Expr (Num n) Ε → Expr (Num m) Ε → Expr (Num (n + m)) Ε
  Var : (v : var α Ε) → Expr α Ε
  Abs : (e : Expr α Ε′) →
        Expr (Clo e Ε) Ε
  App : {β : (Expr α₁ (α₂ ∷ Ε′))} → (e₁ : Expr (Clo β Ε′) Ε) →
        (e₂ : Expr α₂ Ε) →
          Expr α₁ Ε

-- 1 + 1
Expr1 : Expr (Num 3) []
Expr1 = Add (Val 1) (Val 2)
-- (λx. x)
Expr2 : Expr (Clo (Var zero) ((Num 3) ∷ [])) ((Num 3) ∷ [])
Expr2 = Abs (Var {α = Num 3} {Ε = (Num 3) ∷ []} zero)
-- (λx. x) 3
Expr3 : Expr (Num 3) []
Expr3 = App (Abs (Var {α = Num 3} {Ε = (Num 3) ∷ []} zero)) (Val 3)
-- x
Expr4 : Expr (Num 2) (Num 0 ∷ Num 2 ∷ [])
Expr4 = Var (suc zero)
