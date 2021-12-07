
module ccc-5lam-defun-conv where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

data STy : Set where
  typ : Ty → STy
  -- clo-ty S S' E E'は退避させた継続の型、環境の型がそれぞれCode S S' E E'、Env Eであったことを表す
  clo-ty : List STy → List STy → List Ty → List Ty → STy

-- the following variables automatically become implicit arguments
variable
  α α' α₁ α₂ σ : Ty
  β : STy
  E E' E'' E-lam : List Ty
  S S' S'' : List STy

data Value : Ty → Set
data Env : List Ty → Set
data Expr : Ty → List Ty → Set
data Code : List STy → List STy → List Ty → List Ty → Set

data Value where
  Num : (n : ℕ) → Value nat
  Clo : (exp : Expr α₁ (α₂ ∷ E-lam)) → (env : Env E-lam) → Value (α₂ ⇒ α₁)

data Env where
  nil : Env []
  cons : Value α → Env E → Env (α ∷ E)
  
-- variables
data var : (α : Ty) (E : List Ty) → Set where
  zero : var α (α ∷ E)
  suc  : (x : var α E) → var α (σ ∷ E)

lookup : var α E → Env E → Value α
lookup zero (cons x env) = x
lookup (suc v) (cons x env) = lookup v env

data Expr where
  Val : (n : ℕ) → Expr nat E
  Add : Expr nat E → Expr nat E → Expr nat E
  Var : (v : var α E) → Expr α E
  Abs : (exp : Expr α₁ (α₂ ∷ E)) →
        Expr (α₂ ⇒ α₁) E
  App : (e₁ : Expr (α₂ ⇒ α₁) E) →
        (e₂ : Expr α₂ E) →
        Expr α₁ E

{-# TERMINATING #-}
eval : (Expr α E) → Env E → Value α
eval (Val n) env = Num n
eval (Add e₁ e₂) env with eval e₁ env | eval e₂ env
... | Num n | Num m = Num (n + m)
eval (Var v) env = lookup v env
eval (Abs e) env = Clo e env
eval (App e₁ e₂) env with eval e₁ env
... | Clo e-lam env-lam = eval e-lam (cons (eval e₂ env) env-lam)

data Code where
  PUSH : (n : ℕ) → Code (typ nat ∷ S) S' E E' → Code S S' E E'
  ADD : Code (typ nat ∷ S) S' E E' → Code (typ nat ∷ typ nat ∷ S) S' E E'
  LOOKUP : var α E → Code (typ α ∷ S) S' E E' → Code S S' E E'
  ABS : Code (clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E' →
        Code (typ (α₂ ⇒ α₁) ∷ S) S' E-lam E' →
        Code S S' E-lam E'
  RET : Code (typ α₁ ∷ clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E'
  APP : Code (typ α₁ ∷ S) S' E E' → Code (typ α₂ ∷ typ (α₂ ⇒ α₁) ∷ S) S' E E'
  HALT : Code S S E E

data Value-conv : Ty → Set
data Env-conv : List Ty → Set
conv-env : Env E → Env-conv E
comp : Expr α E → Code (typ α ∷ S) S' E E' → Code S S' E E'

data Value-conv where
  Num-conv : (n : ℕ) → Value-conv nat
  -- Clo-conv : (code : Code (clo-ty ((typ α₁) ∷ _) _ _ _) _ (α₂ ∷ E-lam) _) → (env : Env-conv E-lam) → Value-conv (α₂ ⇒ α₁)
  Clo-conv : (code : Code (clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E') →
             (env : Env-conv E-lam) →
             Value-conv (α₂ ⇒ α₁) -- ここにSS'EE'が無いのがhole1,2が埋まらない原因？

conv : {S S' : List STy} {E E' : List Ty} → Value α → Value-conv α
conv (Num n) = Num-conv n
conv {S = S} {S' = S'} {E = E} {E' = E'} (Clo exp env) = Clo-conv {S = S} {S' = S'} {E = E} {E' = E'} (comp exp RET) (conv-env env)
-- exp : Expr α₁ (α₂ ∷ E-lam)
-- env : Env E-lam
-- RET : Code (typ α₁ ∷ clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E'
-- comp : Expr α E → Code (typ α ∷ S) S' E E' → Code S S' E E'
-- now ... comp : Expr α₁ (α₂ ∷ E-lam) → Code (typ α₁ ∷ clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E'
--                  → Code (clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E'

data Env-conv where
  nil-conv : Env-conv []
  cons-conv : Value-conv α → Env-conv E → Env-conv (α ∷ E)
conv-env nil = nil-conv
conv-env (cons v env) = cons-conv (conv v) (conv-env env)

data Elem : STy → Set where
  VAL : Value-conv α → Elem (typ α)
  CLO : Code (typ α₁ ∷ S) S' E E' → Env-conv E → Elem (clo-ty (typ α₁ ∷ S) S' E E')

data Stack : List STy → Set where
  ϵ : Stack []
  _▷_ : Elem β → Stack S → Stack (β ∷ S)
infixr 40 _▷_

comp (Val n) c = PUSH n c
comp (Add e₁ e₂) c = (comp e₁ (comp e₂ (ADD c)))
comp (Var v) c = LOOKUP v c
comp (Abs e) c = ABS (comp e RET) c
comp (App e₁ e₂) c = comp e₁ (comp e₂ (APP c))

lookup-conv : var α E → Env-conv E → Value-conv α
lookup-conv zero (cons-conv x env) = x
lookup-conv (suc v) (cons-conv x env) = lookup-conv v env

{-# TERMINATING #-}
exec : Code S S' E E' → Stack S × Env-conv E → Stack S' × Env-conv E'
exec (PUSH n c) ⟨ s , env-conv ⟩ = exec c ⟨ VAL (Num-conv n) ▷ s , env-conv ⟩
exec (ADD c) ⟨ VAL (Num-conv m) ▷ VAL (Num-conv n) ▷ s , env-conv ⟩ =
  exec c ⟨ VAL (Num-conv (n + m)) ▷ s , env-conv ⟩
exec (LOOKUP v c) ⟨ s , env-conv ⟩ = exec c ⟨ VAL (lookup-conv v env-conv) ▷ s , env-conv ⟩
exec (ABS code c) ⟨ s , env-conv ⟩ = exec c ⟨ VAL (Clo-conv code env-conv) ▷ s , env-conv ⟩
exec RET ⟨ VAL v₁-conv ▷ CLO c env-conv ▷ s , _ ⟩ = exec c ⟨ VAL v₁-conv ▷ s , env-conv ⟩
exec (APP c) ⟨ (VAL v₂-conv) ▷ VAL (Clo-conv {S = S} {S' = S'} {E = E} {E' = E'} code-lam env-lam) ▷ s , env-conv ⟩
 = exec {!code-lam!} {!!}
 --exec code-lam ⟨ CLO c env-conv ▷ s , cons-conv v₂-conv env-lam ⟩
exec HALT ⟨ s , env-conv ⟩ = ⟨ s , env-conv ⟩

-- APP : Code (typ α₁ ∷ S) S' E E' → Code (typ α₂ ∷ typ (α₂ ⇒ α₁) ∷ S) S' E E'
-- CLO : Code (typ α₁ ∷ S) S' E E' → Env-conv E → Elem (clo-ty (typ α₁ ∷ S) S' E E')
-- Clo-conv : (code : Code (clo-ty (typ α₁ ∷ S) S' E E' ∷ S) S' (α₂ ∷ E-lam) E') → (env : Env-conv E-lam) → Value-conv (α₂ ⇒ α₁)

lemma-order-exchange : (v : var α E) (env : Env E) → lookup-conv v (conv-env env) ≡ conv (lookup v env)
lemma-order-exchange zero (cons x env) = refl
lemma-order-exchange (suc v) (cons x env) =
  begin
    lookup-conv (suc v) (conv-env (cons x env))
  ≡⟨ refl ⟩
    lookup-conv (suc v) (cons-conv (conv x) (conv-env env))
  ≡⟨ refl ⟩
    lookup-conv v (conv-env env)
  ≡⟨ lemma-order-exchange v env ⟩
    conv (lookup v env)
  ≡⟨ refl ⟩
    conv (lookup (suc v) (cons x env))
  ∎

{-# TERMINATING #-}
correct :
  (e : Expr α E)
  (c : Code (typ α ∷ S) S' E E')
  (s : Stack S)
  (env : Env E)
  →
  exec (comp e c) ⟨ s , conv-env env ⟩ ≡ exec c ⟨ VAL (conv (eval e env)) ▷ s , conv-env env ⟩

correct (Val n) c s env =
  begin
    exec (comp (Val n) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (PUSH n c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (Num-conv n) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (Num n)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (eval (Val n) env)) ▷ s , conv-env env ⟩
  ∎

correct (Add e₁ e₂) c s env with eval e₁ env | eval e₂ env | inspect (eval e₁) env | inspect (eval e₂) env
... | Num n | Num m | [ eq₁ ] | [ eq₂ ] =
  begin
    exec (comp (Add e₁ e₂) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (ADD c))) ⟨ s , conv-env env ⟩
  ≡⟨ correct e₁ (comp e₂ (ADD c)) s env ⟩
    exec (comp e₂ (ADD c)) ⟨ (VAL (conv (eval e₁ env)) ▷ s) , conv-env env ⟩
  ≡⟨ correct e₂ (ADD c) (VAL (conv (eval e₁ env)) ▷ s) env ⟩
    exec (ADD c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v → exec (ADD c) ⟨ VAL (conv v) ▷ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩) eq₂ ⟩
    exec (ADD c) ⟨ VAL (Num-conv m) ▷ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v → exec (ADD c) ⟨ VAL (Num-conv m) ▷ VAL (conv v) ▷ s , conv-env env ⟩) eq₁ ⟩
    exec (ADD c) ⟨ VAL (Num-conv m) ▷ VAL (Num-conv n) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (Num-conv (n + m)) ▷ s , conv-env env ⟩
  -- ≡⟨ refl ⟩
  --   exec c ⟨ VAL (conv (eval (Add e₁ e₂) env)) ▷ s , conv-env env ⟩
  ∎

correct (Var v) c s env =
  begin
    exec (comp (Var v) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (LOOKUP v c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (lookup-conv v (conv-env env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v → exec c ⟨ VAL v ▷ s , conv-env env ⟩) (lemma-order-exchange v env) ⟩
    exec c ⟨ VAL (conv (lookup v env)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (eval (Var v) env)) ▷ s , conv-env env ⟩
  ∎

correct (Abs e) c s env =
  begin
    exec (comp (Abs e) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (ABS (comp e RET) c) ⟨ s , conv-env env ⟩
  -- ≡⟨ {!!} ⟩
  --   exec c ⟨ VAL (Clo-conv (comp e RET) (conv-env env)) ▷ s , conv-env env ⟩
  -- ≡⟨ {!!} ⟩
  --   exec c ⟨ VAL (conv (Clo e env)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (eval (Abs e) env)) ▷ s , conv-env env ⟩
  ∎

correct (App e₁ e₂) c s env with eval e₁ env       | inspect (eval e₁) env
correct (App e₁ e₂) c s env    | Clo e-lam env-lam | [ eq ] =
  begin
    exec (comp (App e₁ e₂) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (APP c))) ⟨ s , conv-env env ⟩
  ≡⟨ correct e₁ (comp e₂ (APP c)) s env ⟩
    exec (comp e₂ (APP c)) ⟨ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩
  ≡⟨ correct e₂ (APP c) (VAL (conv (eval e₁ env)) ▷ s) env ⟩
    exec (APP c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v₁ → exec (APP c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (conv v₁) ▷ s , conv-env env ⟩) eq ⟩
    exec (APP c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (conv (Clo e-lam env-lam)) ▷ s , conv-env env ⟩
  ≡⟨ {!!} ⟩
    exec (APP c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (Clo-conv (comp e-lam RET) (conv-env env-lam)) ▷ s , conv-env env ⟩
  ≡⟨ {!!} ⟩
    exec (comp e-lam RET) ⟨ CLO c (conv-env env) ▷ s , cons-conv (conv (eval e₂ env)) (conv-env env-lam) ⟩
  ≡⟨ refl ⟩
    exec (comp e-lam RET) ⟨ CLO c (conv-env env) ▷ s , conv-env (cons (eval e₂ env) env-lam) ⟩
  ≡⟨ correct e-lam RET (CLO c (conv-env env) ▷ s) (cons (eval e₂ env) env-lam) ⟩
    exec RET ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ CLO c (conv-env env) ▷ s ,
               conv-env (cons (eval e₂ env) env-lam) ⟩
  ≡⟨ refl ⟩
    exec RET ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ CLO c (conv-env env) ▷ s ,
               cons-conv (conv (eval e₂ env)) (conv-env env-lam) ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ s , conv-env env ⟩
  -- ≡⟨ {!!} ⟩
  --   exec c ⟨ VAL (conv (eval (App e₁ e₂) env)) ▷ s , conv-env env ⟩
  ∎

compile : Expr α E → Code S (typ α ∷ S) E E
compile e = comp e HALT
  
correct' : (e : Expr α E) (s : Stack S) (env : Env E) → exec (compile e) ⟨ s , conv-env env ⟩ ≡ ⟨ VAL (conv (eval e env)) ▷ s , conv-env env ⟩
correct' e s env =
  begin
    exec (compile e) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e HALT) ⟨ s , conv-env env ⟩
  ≡⟨ correct e HALT s env ⟩
    exec HALT ⟨ VAL (conv (eval e env)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    ⟨ VAL (conv (eval e env)) ▷ s , conv-env env ⟩
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

test3 : exec (compile Expr3) ⟨ ϵ , nil-conv ⟩ ≡ ⟨ VAL (Num-conv 3) ▷ ϵ , nil-conv ⟩
test3 = refl

test5 : exec (compile Expr5) ⟨ ϵ , nil-conv ⟩ ≡ ⟨ VAL (Num-conv 5) ▷ ϵ , nil-conv ⟩
test5 = refl

test6 : exec (compile Expr6) ⟨ ϵ , nil-conv ⟩ ≡ ⟨ VAL (Num-conv 8) ▷ ϵ , nil-conv ⟩
test6 = refl

test7 : exec (compile Expr7) ⟨ ϵ , nil-conv ⟩ ≡ ⟨ VAL (Num-conv 5) ▷ ϵ , nil-conv ⟩
test7 = refl
