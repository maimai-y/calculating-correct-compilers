
module ccc-5lam-defun where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Ty : Set
data STy : Set
data Value : Ty → Set
data Env : List Ty → Set
data Expr : Ty → List Ty → Set
data Code : List STy → List STy → List Ty → List Ty → Set

El : Ty → Set

-- the following variables automatically become implicit arguments
variable
  α α' α₁ α₂ σ : Ty
  β : STy
  E E' E'' E-lam : List Ty
  S S' S'' : List STy

data Ty where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

data STy where
  typ : Ty → STy
  clo-ty : List STy → List STy → List Ty → List Ty → STy
 
data ℂ : Ty → Ty → Set where
  -- ExprはCodeになった方が良さそう
  clo : Expr α₁ (α₂ ∷ E) → Env E → ℂ α₂ α₁
  
El nat = ℕ
El (α₂ ⇒ α₁) = ℂ α₂ α₁

data Elem : STy → Set where
  VAL : El α → Elem (typ α)
  CLO : Code (typ α₁ ∷ S) S' E E' → Env E → Elem (clo-ty (typ α₁ ∷ S) S' E E')

data Stack : List STy → Set where
  ϵ : Stack []
  _▷_ : Elem β → Stack S → Stack (β ∷ S)
infixr 40 _▷_

data Env where
  nil : Env []
  cons : El α → Env E → Env (α ∷ E)

data Value where
  Num : (n : ℕ) → Value nat
  Clo : (exp : Expr (α₂ ⇒ α₁) E) → (env : Env E) → Value (α₂ ⇒ α₁)

-- variables
data var : (α : Ty) (E : List Ty) → Set where
  zero : var α (α ∷ E)
  suc  : (x : var α E) → var α (σ ∷ E)

data Expr where
  Val : (n : ℕ) → Expr nat E
  Add : Expr nat E → Expr nat E → Expr nat E
  Var : (v : var α E) → Expr α E
  Abs : (exp : Expr α₁ (α₂ ∷ E)) →
        Expr (α₂ ⇒ α₁) E
  App : (e₁ : Expr (α₂ ⇒ α₁) E) →
        (e₂ : Expr α₂ E) →
        Expr α₁ E

lookup : var α E → Env E → El α
lookup zero (cons x env) = x
lookup (suc v) (cons x env) = lookup v env

{-# TERMINATING #-}
eval : (Expr α E) → Env E → El α
eval (Val n) env = n
eval (Add e₁ e₂) env = (eval e₁ env) + (eval e₂ env)
eval (Var v) env = lookup v env
eval (Abs e) env = clo e env
eval (App e₁ e₂) env with eval e₁ env
... | clo e-lam env-lam = eval e-lam (cons (eval e₂ env) env-lam)
  
data Code where
  PUSH : (n : ℕ) → Code (typ nat ∷ S) S' E E' → Code S S' E E'
  ADD : Code (typ nat ∷ S) S' E E' → Code (typ nat ∷ typ nat ∷ S) S' E E'
  LOOKUP : var α E → Code (typ α ∷ S) S' E E' → Code S S' E E'
  ABS : Expr α₁ (α₂ ∷ E) → Code (typ (α₂ ⇒ α₁) ∷ S) S' E E' → Code S S' E E'
  RET : Code (typ α₁ ∷ clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E'
  APP : Code (typ α₁ ∷ S) S' E E' → Code (typ α₂ ∷ typ (α₂ ⇒ α₁) ∷ S) S' E E'
  HALT : Code S S E E

comp : Expr α E → Code (typ α ∷ S) S' E E' → Code S S' E E'
comp (Val n) c = PUSH n c
comp (Add e₁ e₂) c = (comp e₁ (comp e₂ (ADD c)))
comp (Var v) c = LOOKUP v c
comp (Abs e) c = ABS e c
comp (App e₁ e₂) c = comp e₁ (comp e₂ (APP c))

{-# TERMINATING #-}
exec : Code S S' E E' → Stack S × Env E → Stack S' × Env E'
exec (PUSH n c) ⟨ s , env ⟩ = exec c ⟨ VAL n ▷ s , env ⟩
exec (ADD c) ⟨ VAL m ▷ VAL n ▷ s , env ⟩ = exec c ⟨ VAL (n + m) ▷ s , env ⟩
exec (LOOKUP v c) ⟨ s , env ⟩ = exec c ⟨ VAL (lookup v env) ▷ s , env ⟩
exec (ABS e c) ⟨ s , env ⟩ = exec c ⟨ VAL (clo e env) ▷ s , env ⟩
exec HALT ⟨ s , env ⟩ = ⟨ s , env ⟩
exec RET ⟨ VAL v₁ ▷ CLO c env ▷ s , _ ⟩ = exec c ⟨ VAL v₁ ▷ s , env ⟩
exec (APP c) ⟨ VAL v₂ ▷ VAL (clo e-lam env-lam) ▷ s , env ⟩
  = exec (comp e-lam RET) ⟨ CLO c env ▷ s , cons v₂ env-lam ⟩
  
{-# TERMINATING #-}
correct :
  (e : Expr α E)
  (c : Code (typ α ∷ S) S' E E')
  (s : Stack S)
  (env : Env E)
  →
  exec (comp e c) ⟨ s , env ⟩ ≡ exec c ⟨ VAL (eval e env) ▷ s , env ⟩

correct (Val n) c s env =
  begin
    exec (comp (Val n) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (PUSH n c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL n ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (eval (Val n) env) ▷ s , env ⟩
  ∎

correct (Add e₁ e₂) c s env =
  begin
    exec (comp (Add e₁ e₂) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (ADD c))) ⟨ s , env ⟩
  ≡⟨ correct e₁ (comp e₂ (ADD c)) s env ⟩
    exec (comp e₂ (ADD c)) ⟨ (VAL (eval e₁ env) ▷ s) , env ⟩
  ≡⟨ correct e₂ (ADD c) (VAL (eval e₁ env) ▷ s) env ⟩
    exec (ADD c) ⟨ VAL (eval e₂ env) ▷ VAL (eval e₁ env) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL ((eval e₁ env) + (eval e₂ env)) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (eval (Add e₁ e₂) env) ▷ s , env ⟩
  ∎

correct (Var v) c s env =
  begin
    exec (comp (Var v) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (LOOKUP v c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (lookup v env) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (eval (Var v) env) ▷ s , env ⟩
  ∎

correct (Abs e) c s env =
  begin
    exec (comp (Abs e) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (ABS e c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (clo e env) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (eval (Abs e) env) ▷ s , env ⟩
  ∎

correct (App e₁ e₂) c s env with eval e₁ env       | inspect (eval e₁) env
correct (App e₁ e₂) c s env    | clo e-lam env-lam | [ eq ] =
  begin
    exec (comp (App e₁ e₂) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (APP c))) ⟨ s , env ⟩
  ≡⟨ correct e₁ (comp e₂ (APP c)) s env ⟩
    exec (comp e₂ (APP c)) ⟨ VAL (eval e₁ env) ▷ s , env ⟩
  ≡⟨ correct e₂ (APP c) (VAL (eval e₁ env) ▷ s) env ⟩
    exec (APP c) ⟨ VAL (eval e₂ env) ▷ VAL (eval e₁ env) ▷ s , env ⟩
  ≡⟨ cong (λ v₁ → exec (APP c) ⟨ VAL (eval e₂ env) ▷ VAL v₁ ▷ s , env ⟩) eq ⟩
    exec (APP c) ⟨ VAL (eval e₂ env) ▷ VAL (clo e-lam env-lam) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec (comp e-lam RET) ⟨ CLO c env ▷ s , cons (eval e₂ env) env-lam ⟩
  ≡⟨ correct e-lam RET (CLO c env ▷ s) (cons (eval e₂ env) env-lam) ⟩
    exec RET ⟨ VAL (eval e-lam (cons (eval e₂ env) env-lam)) ▷ CLO c env ▷ s , cons (eval e₂ env) env-lam ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (eval e-lam (cons (eval e₂ env) env-lam)) ▷ s , env ⟩
  -- ≡⟨ {!!} ⟩
  --   exec c ⟨ VAL (eval (App e₁ e₂) env) ▷ s , env ⟩
  ∎

compile : Expr α E → Code S (typ α ∷ S) E E
compile e = comp e HALT
  
correct' : (e : Expr α E) (s : Stack S) (env : Env E) → exec (compile e) ⟨ s , env ⟩ ≡ ⟨ VAL (eval e env) ▷ s , env ⟩
correct' e s env =
  begin
    exec (compile e) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (comp e HALT) ⟨ s , env ⟩
  ≡⟨ correct e HALT s env ⟩
    exec HALT ⟨ VAL (eval e env) ▷ s , env ⟩
  ≡⟨ refl ⟩
    ⟨ VAL (eval e env) ▷ s , env ⟩
  ∎
  
-- 1 + 1
Expr1 : Expr nat []
Expr1 = Add (Val 1) (Val 2)
-- (λx. x)
Expr2 : Expr (α ⇒ α) []
Expr2 = Abs (Var zero)
-- (λx. x) 3
Expr3 : Expr nat []
Expr3 = App (Abs (Var zero)) (Val 3)
-- x
Expr4 : Expr α (σ ∷ α ∷ E)
Expr4 = Var (suc zero)
-- (λx. x + 2) 3
Expr5 : Expr nat []
Expr5 = App (Abs (Add (Var zero) (Val 2))) (Val 3)
-- (λxy. y + x) 3 5
Expr6 : Expr nat []
Expr6 = App (App (Abs (Abs (Add (Var zero) (Var (suc zero))))) (Val 3)) (Val 5)
-- (λxy. y + x 1) (λx. x + 1) 3
Expr7 : Expr nat []
Expr7 = App (App (Abs (Abs (Add (Var zero) (App (Var (suc zero)) (Val 1))))) (Abs (Add (Var zero) (Val 1)))) (Val 3)

test3 : exec (compile Expr3) ⟨ ϵ , nil ⟩ ≡ ⟨ VAL 3 ▷ ϵ , nil ⟩
test3 = refl

test5 : exec (compile Expr5) ⟨ ϵ , nil ⟩ ≡ ⟨ VAL 5 ▷ ϵ , nil ⟩
test5 = refl

test6 : exec (compile Expr6) ⟨ ϵ , nil ⟩ ≡ ⟨ VAL 8 ▷ ϵ , nil ⟩
test6 = refl

test7 : exec (compile Expr7) ⟨ ϵ , nil ⟩ ≡ ⟨ VAL 5 ▷ ϵ , nil ⟩
test7 = refl
