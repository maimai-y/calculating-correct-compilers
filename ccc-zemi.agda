
module ccc-zemi where

open import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

data Expr : Ty → List Ty → Set
data Env : List Ty → Set
data Value : Ty → Set

-- the following variables automatically become implicit arguments
variable
  α α₁ α₂ σ : Ty
  E E' Eλ : List Ty

data Env where
  nil : Env []
  cons : Value α → Env E → Env (α ∷ E)

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

data Value where
  Num : (n : ℕ) → Value nat
  Clo : (exp : Expr α₁ (α₂ ∷ E)) (env : Env E) → Value (α₂ ⇒ α₁)

lookup : var α E → Env E → Value α
lookup zero (cons x env) = x
lookup (suc v) (cons x env) = lookup v env

-- functional semantics
-- eval : (Expr α E) → Env E → El α
-- eval (Val n) env = n
-- eval (Add e₁ e₂) env = (eval e₁ env) + (eval e₂ env)
-- eval (Var v) env = lookup v env
-- eval (Abs e) env = λ x → eval e (cons x env)
-- eval (App e₁ e₂) env = (eval e₁ env) (eval e₂ env)

-- relational semantics
data eval : (Expr α E) → Env E → Value α → Set where
  eNum : {env : Env E}
         (n : ℕ) → eval (Val n) env (Num n)
  eAdd : {env : Env E} {e₁ e₂ : Expr nat E}
         (n₁ n₂ : ℕ)
         → eval e₁ env (Num n₁)
         → eval e₂ env (Num n₂)
         → eval (Add e₁ e₂) env (Num (n₁ + n₂))
  eVar : {env : Env E} {v : var α E}
         → eval (Var v) env (lookup v env)
  eAbs : {envλ : Env Eλ} {eλ : Expr α₁ (α₂ ∷ Eλ)}
         → eval (Abs eλ) envλ (Clo eλ envλ)
  eApp : {env : Env E}
         (eλ : Expr α₁ (α₂ ∷ Eλ)) (envλ : Env Eλ)
         {e₁ : Expr (α₂ ⇒ α₁) E} (vλ : Value α₁)
         {e₂ : Expr α₂ E} (v₂ : Value α₂)
         → eval e₁ env (Clo eλ envλ)
         → eval e₂ env v₂
         → eval eλ (cons v₂ envλ) vλ
         → eval (App e₁ e₂) env vλ

data STy : Set

data Env-c : List Ty → Set
data Value-c : Ty → Set
data Code : (List STy × List Ty) → (List STy × List Ty) → Set

variable
  β : STy
  S S' : List STy
  code : Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
  env : Env-c E

data STy where
  VAL : Ty → STy
  --CLO : Code ⟨ S , E ⟩ ⟨ S' , E' ⟩ → Env-c E → STy
  CLO : List STy → List STy → List Ty → List Ty → STy

data Env-c where
  nil-c : Env-c []
  cons-c : Value-c α → Env-c E → Env-c (α ∷ E)

data Value-c where
  Num-c : (n : ℕ) → Value-c nat
  Clo-c : (code : Code ⟨ CLO (VAL α₁ ∷ S) S' E E' ∷ S , α₂ ∷ Eλ ⟩ ⟨ VAL α₁ ∷ S , α₂ ∷ Eλ ⟩) (env : Env-c Eλ) → Value-c (α₂ ⇒ α₁)

data Elem : STy → Set where
  EVal : (v : Value-c α) → Elem (VAL α)
  EClo : (code : Code ⟨ S , E ⟩ ⟨ S' , E' ⟩) → (env : Env-c E) → Elem (CLO S S' E E')

data Stack : List STy → Set where
  ϵ : Stack []
  _▷_ : Elem β → Stack S → Stack (β ∷ S)
infixr 40 _▷_

data Code where
  PUSH : (n : ℕ) → (c : Code ⟨ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩) → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
  ADD : Code ⟨ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ VAL nat ∷ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩
  LOOKUP : var α E → Code ⟨ VAL α ∷ S , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
  APP : Code ⟨ VAL α₁ ∷ S , E ⟩ ⟨ S' , E' ⟩ →
        Code ⟨ VAL (α₂ ⇒ α₁) ∷ VAL α₂ ∷ S , E ⟩ ⟨ S' , E' ⟩
  -- RET : {code : Code ⟨ VAL α₁ ∷ S , E ⟩ ⟨ S' , E' ⟩} {env : Env-c E}
  --       → Code ⟨ VAL α₁ ∷ CLO code env ∷ S , Eλ ⟩ ⟨ VAL α₁ ∷ S , E ⟩
  RET : Code ⟨ VAL α₁ ∷ CLO (VAL α₁ ∷ S) S' E E' ∷ S , Eλ ⟩ ⟨ S' , E' ⟩
--   ABS : ({S S' : List STy} {E E' : List Ty} →
--         Code (VAL α₁-c ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') →
--         Code (ENV (conv-ty-lst E) ∷ S) S' (α₂-c ∷ E-lam-c) (conv-ty-lst E')) →      --exec ABSの定義においてlamの型
--         Code (VAL (α₂-c ⇒-c α₁-c , E-lam-c) ∷ S) S' E-lam-c E'-c →                 --exec ABSの定義においてcの型
--         Code S S' E-lam-c E'-c
--   HALT : Code S S E-c E-c

comp : Expr α E → Code ⟨ (VAL α ∷ S) , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
comp (Val n) c = PUSH n c
comp (Add e₁ e₂) c = comp e₁ (comp e₂ (ADD c))
comp (Var v) c = LOOKUP v c
comp (Abs x) c = {!!}
comp (App e₁ e₂) c = comp e₂ (comp e₁ (APP c))

-- comp (Abs e) c =
--   ABS
--     (λ {S : List STy} {S' : List STy} {E : List Ty} {E' : List Ty}
--          (c' : Code (VAL _ ∷ S) S' (conv-ty-lst E) (conv-ty-lst E'))
--       → (comp e (RET c')))
--     c

conv-env : Env E → Env-c E

conv-clo : (exp : Expr α₁ (α₂ ∷ Eλ)) (env : Env Eλ) → Value-c (α₂ ⇒ α₁)
conv-clo = {!!}

conv : Value α → Value-c α   --{S : List STy} →
conv (Num n) = Num-c n
conv (Clo exp env) = conv-clo exp env  --Clo-c (comp exp RET) (conv-env env) 

conv-env nil = nil-c
conv-env (cons v env) = cons-c (conv v) (conv-env env)

lookup-c : var α E → Env-c E → Value-c α
lookup-c zero (cons-c fst rest) = fst
lookup-c (suc v) (cons-c fst rest) = lookup-c v rest

-- exec (ABS lam c) ⟨ s , env-lam ⟩ = exec c ⟨ ⟨ lam , env-lam ⟩ ▷ s , env-lam ⟩
-- exec (RET c') ⟨ x₁ ▷ env ▷ s , cons-c x₂ env-lam ⟩ = exec c' ⟨ x₁ ▷ s , env ⟩
-- exec (APP c) ⟨ ⟨ lam ,  env-lam ⟩ ▷ x₂ ▷ s , env ⟩ = exec (lam c) ⟨ env ▷ s , cons-c x₂ env-lam ⟩
-- exec HALT ⟨ s , env ⟩ = ⟨ s , env ⟩

{-# TERMINATING #-}
exec : Code ⟨ S , E ⟩ ⟨ S' , E' ⟩ → Stack S × Env-c E → Stack S' × Env-c E'
exec (PUSH n c) ⟨ s , env ⟩ = exec c ⟨ (EVal (Num-c n) ▷ s) , env ⟩
exec (ADD c) ⟨ EVal (Num-c n₂) ▷ EVal (Num-c n₁) ▷ s , env ⟩ = exec c ⟨ EVal (Num-c (n₁ + n₂)) ▷ s , env ⟩
exec (LOOKUP v c) ⟨ s , env ⟩ = exec c ⟨ EVal (lookup-c v env) ▷ s , env ⟩
exec (APP c) ⟨ s , env ⟩ = {!!}
exec RET ⟨ EVal vλ ▷ EClo c env ▷ s , _ ⟩ = exec c ⟨ EVal vλ ▷ s , env ⟩
--{!exec {S = VAL α₁ ∷ S} c ⟨ EVal vλ ▷ s , env ⟩!} --{S = VAL α₂ ∷ CLO ∷ S} --{S = VAL α₁ ∷ CLO ∷ S}

lemma-order-exchange : (v : var α E) (env : Env E) → lookup-c v (conv-env env) ≡ conv (lookup v env)
lemma-order-exchange zero (cons x env) = refl
lemma-order-exchange (suc v) (cons x env) =
  begin
    lookup-c (suc v) (conv-env (cons x env))
  ≡⟨ refl ⟩
    lookup-c (suc v) (cons-c (conv x) (conv-env env))
  ≡⟨ refl ⟩
    lookup-c v (conv-env env)
  ≡⟨ lemma-order-exchange v env ⟩
    conv (lookup v env)
  ≡⟨ refl ⟩
    conv (lookup (suc v) (cons x env))
  ∎

correct :
  (e : Expr α E)
  (c : Code ⟨ VAL α ∷ S , E ⟩ ⟨ S' , E' ⟩)
  (s : Stack S)
  (env : Env E)
  {v : Value α}
  → (eval e env v)
  → exec (comp e c) ⟨ s , conv-env env ⟩ ≡ exec c ⟨ EVal (conv v) ▷ s , conv-env env ⟩


correct (Val n) c s env (eNum n) =
  begin
    exec (comp (Val n) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (PUSH n c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (Num-c n) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (conv (Num n)) ▷ s , conv-env env ⟩
  ∎

correct (Add e₁ e₂) c s env (eAdd n₁ n₂ p₁ p₂) =
  begin
    exec (comp (Add e₁ e₂) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (ADD c))) ⟨ s , conv-env env ⟩
  ≡⟨ correct e₁ (comp e₂ (ADD c)) s env p₁ ⟩
    exec (comp e₂ (ADD c)) ⟨ EVal (Num-c n₁) ▷ s , conv-env env ⟩
  ≡⟨ correct e₂ (ADD c) (EVal (Num-c n₁) ▷ s) env p₂ ⟩
    exec (ADD c) ⟨ EVal (Num-c n₂) ▷ EVal (Num-c n₁) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (Num-c (n₁ + n₂)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (conv (Num (n₁ + n₂))) ▷ s , conv-env env ⟩
  ∎

correct (Var v) c s env eVar =
  begin
    exec (comp (Var v) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (LOOKUP v c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (lookup-c v (conv-env env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v → exec c ⟨ EVal v ▷ s , conv-env env ⟩) (lemma-order-exchange v env) ⟩
    exec c ⟨ EVal (conv (lookup v env)) ▷ s , conv-env env ⟩
  ∎

correct (Abs _) c s env eAbs = {!!}

correct (App e₁ e₂) c s env (eApp eλ envλ vλ v₂ p₁ p₂ pλ) =
  begin
    exec (comp (App e₁ e₂) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e₂ (comp e₁ (APP c))) ⟨ s , conv-env env ⟩
  ≡⟨ correct e₂ (comp e₁ (APP c)) s env p₂ ⟩
    exec (comp e₁ (APP c)) ⟨ EVal (conv v₂) ▷ s , conv-env env ⟩
  ≡⟨ correct e₁ (APP c) (EVal (conv v₂) ▷ s) env p₁ ⟩
    exec (APP c) ⟨ EVal (conv (Clo eλ envλ)) ▷ EVal (conv v₂) ▷ s , conv-env env ⟩
  ≡⟨ {!!} ⟩
    exec RET ⟨ EVal (conv vλ) ▷ EClo c (conv-env env) ▷ s , conv-env envλ ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (conv vλ) ▷ s , conv-env env ⟩
  ∎
