
module ccc-5lam-cps where

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
  α α₁ α₂ σ β : Ty
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

--functional semantics
-- {-# TERMINATING #-}
-- eval : (Expr α E) → Env E → (Value α → Value β) → Value β
-- eval (Val n) env c = c (Num n)
-- eval (Add e₁ e₂) env c = eval e₁ env (λ { (Num n₁) → eval e₂ env (λ { (Num n₂) → c (Num (n₁ + n₂)) }) })
-- eval (Var v) env c = c (lookup v env)
-- eval (Abs e) env c = c (Clo e env)
-- eval (App e₁ e₂) env c = eval e₁ env (λ { (Clo eλ envλ) → eval e₂ env (λ { v₂ → eval eλ (cons v₂ envλ) c }) })

-- relational semantics
data C : Ty → Ty → Set where
  nilC : C α α
  addLC : (env : Env E) → (e₂ : Expr nat E) → (c : C nat β) → C nat β
  addRC : (v₁ : Value nat) → (c : C nat β) → C nat β
  appLC : (env : Env E) → (e₂ : Expr α₂ E) → (c : C α₁ β) → C (α₂ ⇒ α₁) β
  appRC : (v₁ : Value (α₂ ⇒ α₁)) → (c : C α₁ β) → C α₂ β 

data eval : (Expr α E) → Env E → C α β → Value β → Set

data appC : Value α → C α β → Value β → Set where
  CEmpty : {v : Value α}
           --------------- (CEmpty)
           → appC v nilC v
  CPlusL : {v₁ : Value nat} {v : Value β} {e₂ : Expr nat E} {env : Env E} {c : C nat β}
           → eval e₂ env (addRC v₁ c) v
           ---------------------------- (CPlusL)
           → appC v₁ (addLC env e₂ c) v
  CPlusR : {n₁ n₂ : ℕ} {c : C nat β} {v : Value β}
           → appC (Num (n₁ + n₂)) c v
           ---------------------------- (CPlusR)
           → appC (Num n₂) (addRC (Num n₁) c) v
  CAppL : {e₂ : Expr α₂ E} {env : Env E} {v₁ : Value (α₂ ⇒ α₁)} {c : C α₁ β} {v : Value β}
          → eval e₂ env (appRC v₁ c) v
          ---------------------------- (CPlusL)
          → appC v₁ (appLC env e₂ c) v
  CAppR : {env : Env E}
          (eλ : Expr α₁ (α₂ ∷ Eλ)) (envλ : Env Eλ)
          {v₂ : Value α₂}
          {c : C α₁ β} {v : Value β}
          → eval eλ (cons v₂ envλ) c v
          ---------------------------- (CPlusL)
          → appC v₂ (appRC (Clo eλ envλ) c) v

data eval where
  ENum : {env : Env E} {v : Value β} {c : C nat β} {n : ℕ}
         → appC (Num n) c v
         ------------------------ (ENum)
         → eval (Val n) env c v
  EPlus : {env : Env E} {e₁ e₂ : Expr nat E} {v : Value β} {c : C nat β}
         → eval e₁ env (addLC env e₂ c) v
         -------------------------------- (EPlus)
         → eval (Add e₁ e₂) env c v
  EVar : {env : Env E} {v : var α E} {c : C α β} {val : Value β}
         → appC (lookup v env) c val
         -------------------------- (EVar)
         → eval (Var v) env c val
  EAbs : {envλ : Env Eλ} {eλ : Expr α₁ (α₂ ∷ Eλ)} {c : C (α₂ ⇒ α₁) β} {v : Value β}
         → appC (Clo eλ envλ) c v
         -------------------------- (EAbs)
         → eval (Abs eλ) envλ c v
  EApp : {env : Env E} {c : C α₁ β} {v : Value β} {e₁ : Expr (α₂ ⇒ α₁) E} {e₂ : Expr α₂ E}
         → eval e₁ env (appLC env e₂ c) v
         ------------------------------ (EApp)
         → eval (App e₁ e₂) env c v

eval1 : eval (Add (Val 1) (Val 2)) nil nilC (Num 3)
eval1 = EPlus (ENum (CPlusL (ENum (CPlusR CEmpty))))

data STy : Set

data Env-c : List Ty → Set
data Value-c : Ty → Set
data Code : (List STy × List Ty) → (List STy × List Ty) → Set

variable
  γ : STy
  S S' : List STy

data STy where
  VAL : Ty → STy
  CLO : List STy → List STy → List Ty → List Ty → STy

data Env-c where
  nil-c : Env-c []
  cons-c : Value-c α → Env-c E → Env-c (α ∷ E)

data Value-c where
  Num-c : (n : ℕ) → Value-c nat
  Clo-c : (code : {S S' : List STy} {E E' : List Ty} → Code ⟨ CLO (VAL α₁ ∷ S) S' E E' ∷ S , α₂ ∷ Eλ ⟩ ⟨ S' , E' ⟩)
          (env : Env-c Eλ)
          → Value-c (α₂ ⇒ α₁)

data Elem : STy → Set where
  EVal : (v : Value-c α) → Elem (VAL α)
  EClo : (code : Code ⟨ VAL α₁ ∷ S , E ⟩ ⟨ S' , E' ⟩) → (env : Env-c E) → Elem (CLO (VAL α₁ ∷ S) S' E E') --cccのCLO

data Stack : List STy → Set where
  ϵ : Stack []
  _▷_ : Elem γ → Stack S → Stack (γ ∷ S)
infixr 40 _▷_

data Code where
  PUSH : (n : ℕ) → (c : Code ⟨ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩) → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
  ADD : Code ⟨ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ VAL nat ∷ VAL nat ∷ S , E ⟩ ⟨ S' , E' ⟩
  LOOKUP : var α E → Code ⟨ VAL α ∷ S , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
  APP : Code ⟨ VAL α₁ ∷ S , E ⟩ ⟨ S' , E' ⟩ →
        Code ⟨ VAL (α₂ ⇒ α₁) ∷ VAL α₂ ∷ S , E ⟩ ⟨ S' , E' ⟩
  RET : Code ⟨ VAL α₁ ∷ CLO (VAL α₁ ∷ S) S' E E' ∷ S , Eλ ⟩ ⟨ S' , E' ⟩
  ABS : ({S-app S' : List STy} {E-app E' : List Ty}
          → Code ⟨ (CLO (VAL α₁ ∷ S-app) S' E-app E' ∷ S-app) , α₂ ∷ Eλ ⟩ ⟨ S' , E' ⟩)
        → Code ⟨ VAL (α₂ ⇒ α₁) ∷ S , Eλ ⟩ ⟨ S' , E' ⟩
        → Code ⟨ S , Eλ ⟩ ⟨ S' , E' ⟩
  HALT : Code ⟨ S , E ⟩ ⟨ S , E ⟩

comp : Expr α E → Code ⟨ VAL α ∷ S , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
-- comp : Expr α E → Code ⟨ (VAL α ∷ S) , E ⟩ ⟨ S' , E' ⟩ → Code ⟨ S , E ⟩ ⟨ S' , E' ⟩
-- comp (Val n) c = PUSH n c
-- comp (Add e₁ e₂) c = comp e₁ (comp e₂ (ADD c))
-- comp (Var v) c = LOOKUP v c
-- comp (Abs e) c = ABS (comp e RET) c
-- comp (App e₁ e₂) c = comp e₂ (comp e₁ (APP c))

conv-env : Env E → Env-c E

conv : Value α → Value-c α
conv (Num n) = Num-c n
conv (Clo exp env) = Clo-c (comp exp RET) (conv-env env)

conv-env nil = nil-c
conv-env (cons v env) = cons-c (conv v) (conv-env env)

lookup-c : var α E → Env-c E → Value-c α
lookup-c zero (cons-c fst rest) = fst
lookup-c (suc v) (cons-c fst rest) = lookup-c v rest

{-# TERMINATING #-}
exec : Code ⟨ S , E ⟩ ⟨ S' , E' ⟩ → Stack S × Env-c E → Stack S' × Env-c E'
-- exec (PUSH n c) ⟨ s , env ⟩ = exec c ⟨ (EVal (Num-c n) ▷ s) , env ⟩
-- exec (ADD c) ⟨ EVal (Num-c n₂) ▷ EVal (Num-c n₁) ▷ s , env ⟩ = exec c ⟨ EVal (Num-c (n₁ + n₂)) ▷ s , env ⟩
-- exec (LOOKUP v c) ⟨ s , env ⟩ = exec c ⟨ EVal (lookup-c v env) ▷ s , env ⟩
-- exec RET ⟨ EVal vλ ▷ EClo c env ▷ s , _ ⟩ = exec c ⟨ EVal vλ ▷ s , env ⟩
-- exec (APP c) ⟨ EVal (Clo-c code envλ) ▷ EVal v₂ ▷ s , env ⟩ = exec code ⟨ EClo c env ▷ s , cons-c v₂ envλ ⟩
-- exec (ABS code c) ⟨ s , env ⟩ = exec c ⟨ EVal (Clo-c code env) ▷ s , env ⟩
-- exec HALT ⟨ s , env ⟩ = ⟨ s , env ⟩

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

conv-cont : (cont : C α β) → Code ⟨ VAL α ∷ S , E ⟩ ⟨ VAL β ∷ S , E ⟩ --???
conv-cont nilC = HALT
conv-cont (addLC env e₂ c) = {!!}
conv-cont (addRC (Num n₁) c) = PUSH n₁ (ADD (conv-cont c))
conv-cont (appLC env e₂ c) = {!!}
conv-cont (appRC (Clo exp env) c) = {!!}

correct :
  (e : Expr α E) (c : C α β) (s : Stack S) (env : Env E) {v : Value β}
  → eval e env c v
  → exec (comp e (conv-cont c)) ⟨ s , conv-env env ⟩ ≡ ⟨ EVal (conv v) ▷ s , conv-env env ⟩

correct .(Val _) c s env (ENum x) = {!!}
correct .(Add _ _) c s env (EPlus x) = {!!}
correct .(Var _) c s env (EVar x) = {!!}
correct .(Abs _) c s env (EAbs x) = {!!}
correct .(App _ _) c s env (EApp x) = {!!}

{-
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

correct (Abs e) c s env eAbs =
  begin
    exec (comp (Abs e) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (ABS (comp e RET) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (Clo-c (comp e RET) (conv-env env)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (conv (Clo e env)) ▷ s , conv-env env ⟩
  ∎

correct (App e₁ e₂) c s env (eApp eλ envλ vλ v₂ p₁ p₂ pλ) =
  begin
    exec (comp (App e₁ e₂) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e₂ (comp e₁ (APP c))) ⟨ s , conv-env env ⟩
  ≡⟨ correct e₂ (comp e₁ (APP c)) s env p₂ ⟩
    exec (comp e₁ (APP c)) ⟨ EVal (conv v₂) ▷ s , conv-env env ⟩
  ≡⟨ correct e₁ (APP c) (EVal (conv v₂) ▷ s) env p₁ ⟩
    exec (APP c) ⟨ EVal (conv (Clo eλ envλ)) ▷ EVal (conv v₂) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (APP c) ⟨ EVal (Clo-c (comp eλ RET) (conv-env envλ)) ▷ EVal (conv v₂) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp eλ RET) ⟨ EClo c (conv-env env) ▷ s , cons-c (conv v₂) (conv-env envλ) ⟩
  ≡⟨ correct eλ RET (EClo c (conv-env env) ▷ s) (cons v₂ envλ) pλ ⟩
    exec RET ⟨ EVal (conv vλ) ▷ EClo c (conv-env env) ▷ s , cons-c (conv v₂) (conv-env envλ) ⟩
  ≡⟨ refl ⟩
    exec c ⟨ EVal (conv vλ) ▷ s , conv-env env ⟩
  ∎

compile : Expr α E → Code ⟨ S , E ⟩ ⟨ (VAL α ∷ S) , E ⟩
compile e = comp e HALT
  
correct' : (e : Expr α E) (s : Stack S) (env : Env E) (v : Value α)
           → eval e env v
           → exec (compile e) ⟨ s , conv-env env ⟩ ≡ ⟨ EVal (conv v) ▷ s , conv-env env ⟩
correct' e s env v p =
  begin
    exec (compile e) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e HALT) ⟨ s , conv-env env ⟩
  ≡⟨ correct e HALT s env p ⟩
    exec HALT ⟨ EVal (conv v) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    ⟨ EVal (conv v) ▷ s , conv-env env ⟩
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

test3 : exec (compile Expr3) ⟨ ϵ , nil-c ⟩ ≡ ⟨ EVal (Num-c 3) ▷ ϵ , nil-c ⟩
test3 = refl

test5 : exec (compile Expr5) ⟨ ϵ , nil-c ⟩ ≡ ⟨ EVal (Num-c 5) ▷ ϵ , nil-c ⟩
test5 = refl

test6 : exec (compile Expr6) ⟨ ϵ , nil-c ⟩ ≡ ⟨ EVal (Num-c 8) ▷ ϵ , nil-c ⟩
test6 = refl

test7 : exec (compile Expr7) ⟨ ϵ , nil-c ⟩ ≡ ⟨ EVal (Num-c 5) ▷ ϵ , nil-c ⟩
test7 = refl
-}
