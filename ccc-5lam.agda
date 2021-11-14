
module ccc-5lam where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)

data Value : Set
data Env : List Value → Set
data Expr : Value → List Value → Set

-- the following variables automatically become implicit arguments
variable
  α α₁ α₂ σ : Value
  L L′ : List Value
  n m : ℕ

data Value where
  Num : (n : ℕ) → Value
  Clo : (exp : Expr α₁ (α₂ ∷ L)) → (env : List Value) → Value

data Env where
  env : (l : List Value) → Env l

-- variables
data var : (α : Value) (L : List Value) → Set where
  zero : var α (α ∷ L)
  suc  : (x : var α L) → var α (σ ∷ L)

data Expr where
  Val : (n : ℕ) → Expr (Num n) L
  Add : Expr (Num n) L → Expr (Num m) L → Expr (Num (n + m)) L
  Var : (v : var α L) → Expr α L
  Abs : (exp : Expr α₁ (α₂ ∷ L)) →
        Expr (Clo exp L) L
  App : {β : (Expr α₁ (α₂ ∷ L′))} → (e₁ : Expr (Clo β L′) L) →
        (e₂ : Expr α₂ L) →
          Expr α₁ L

-- 1 + 1
Expr1 : Expr (Num 3) []
Expr1 = Add (Val 1) (Val 2)
-- (λx. x)
Expr2 : Expr (Clo {α₁ = Num 3} (Var zero) []) []
Expr2 = Abs (Var zero)
-- (λx. x) 3
Expr3 : Expr (Num 3) []
Expr3 = App (Abs (Var zero)) (Val 3)
-- x
Expr4 : Expr (Num 2) (Num 0 ∷ Num 2 ∷ [])
Expr4 = Var (suc zero)

data Fun : Set where
  fun : (exp : Expr α L) → (env : List Value) → Fun 
  
El : Value → Set
El (Num n) = ℕ
El (Clo exp L) = Fun

eval : (Expr α L) → Env L → El α
eval (Val n) e = n
eval (Add x y) e with (eval x e) | (eval y e)
... | n | m = n + m
eval {Num n} (Var zero) (env .(Num n ∷ _)) = n
eval {Clo ex en} (Var zero) (env .(Clo ex en ∷ _)) = fun ex en
eval (Var (suc v)) (env (x ∷ l)) = eval (Var v) (env l)
eval (Abs exp) (env lst) = fun exp lst
eval (App {α₁ = Num n} x y) (env lst) = n
eval (App {α₁ = Clo ex en} x y) (env lst) = fun ex en
