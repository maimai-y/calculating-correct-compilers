
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
  E E' E-lam : List Ty

-- data ℂ : Ty → Ty → List Ty → Set where
--   clo : Expr α₁ (α₂ ∷ E) → Env E → ℂ α₂ α₁ E

-- El : Ty → Set
-- El nat = ℕ
-- El (α₂ ⇒ α₁) = El α₂ → El α₁


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

-- fun
-- eval : (Expr α E) → Env E → El α
-- eval (Val n) env = n
-- eval (Add e₁ e₂) env = (eval e₁ env) + (eval e₂ env)
-- eval (Var v) env = lookup v env
-- eval (Abs e) env = λ x → eval e (cons x env)
-- eval (App e₁ e₂) env = (eval e₁ env) (eval e₂ env)

data eval : (Expr α E) → Env E → Value α → Set where
  eNum : {env : Env E} (n : ℕ) → eval (Val n) env (Num n)
  eAdd : {env : Env E} {n m : ℕ} {x y : Expr nat E} →
         eval x env (Num n) →
         eval y env (Num m) →
         eval (Add x y) env (Num (n + m))

data Env' : List Ty → Set
data Value' : Ty → Set
data Code : (List Ty × Env' E) → (List Ty × Env' E') → Set

variable
--   α-c α'-c α₁-c α₂-c σ-c : Ty-c
  S S' : List Ty
  env env' : Env' E
--   E-c E'-c E-lam-c : List Ty-c
--   β : STy

data Env' where
  nil' : Env' []
  cons' : Value' α → Env' E → Env' (α ∷ E)

data Value' where
  Num' : (n : ℕ) → Value' nat
  Clo' : (code : Code ⟨ S , env ⟩ ⟨ S' , env' ⟩) (env : Env' E) → Value' (α₂ ⇒ α₁)
-- data Ty-c : Set
-- data STy : Set

comp : {env : Env' E} → Expr α E → Code ⟨ (α ∷ S) , env ⟩ ⟨ S' , env' ⟩ → Code ⟨ S , env ⟩ ⟨ S' , env' ⟩
  
-- data Ty-c where
--   nat-c : Ty-c
--   _⇒-c_,_ : Ty-c → Ty-c → List Ty-c → Ty-c

-- data STy where
--   VAL : Ty → STy
--   CLO : List Ty-c → STy

-- conv-ty-lst : List Ty → List Ty-c

-- conv-ty : Ty → Ty-c
-- conv-ty nat = nat-c
-- conv-ty (α₂ ⇒ α₁ , E-lam) = (conv-ty α₂ ⇒-c conv-ty α₁ , conv-ty-lst E-lam)

-- conv-ty-lst [] = []
-- conv-ty-lst (fst ∷ rst) = conv-ty fst ∷ conv-ty-lst rst

-- El-Ty-c : Ty-c → Set

-- data Env-c : List Ty-c → Set where
--   nil-c : Env-c []
--   cons-c : El-Ty-c α-c → Env-c E-c → Env-c (α-c ∷ E-c)

-- El-Ty-c nat-c = ℕ
-- El-Ty-c (α₂-c ⇒-c α₁-c , E-lam-c)
--   = ({S S' : List STy} {E E' : List Ty}
--     → Code (VAL α₁-c ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') --S S' E-c E'-c はここのラムダ式の引数から割り当てる
--     → Code (ENV (conv-ty-lst E) ∷ S) S' (α₂-c ∷ E-lam-c) (conv-ty-lst E'))
--     × Env-c E-lam-c

-- El-STy : STy → Set
-- El-STy (VAL α-c) = El-Ty-c α-c
-- El-STy (ENV E) = Env-c E
{-
data Elem : Ty → Set where
  Val : (n : ℕ) → Elem nat
  Clo : (El α₂ → El α₁) → Elem (α₂ ⇒ α₁)  --(e : Expr α₁ E) (env : Env E) → Elem (α₂ ⇒ α₁)

data Stack : List Ty → Set where
  ϵ : Stack []
  _▷_ : Elem α → Stack S → Stack (α ∷ S)
infixr 40 _▷_


data Code where
  PUSH : (n : ℕ) → (c : Code (nat ∷ S) S') → Code S S'
--   ADD : Code (VAL nat-c ∷ S) S' E-c E'-c → Code (VAL nat-c ∷ VAL nat-c ∷ S) S' E-c E'-c
--   LOOKUP : var α E → Code (VAL (conv-ty α) ∷ S) S' (conv-ty-lst E) E'-c → Code S S' (conv-ty-lst E) E'-c
--   ABS : ({S S' : List STy} {E E' : List Ty} →
--         Code (VAL α₁-c ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') →
--         Code (ENV (conv-ty-lst E) ∷ S) S' (α₂-c ∷ E-lam-c) (conv-ty-lst E')) →      --exec ABSの定義においてlamの型
--         Code (VAL (α₂-c ⇒-c α₁-c , E-lam-c) ∷ S) S' E-lam-c E'-c →                 --exec ABSの定義においてcの型
--         Code S S' E-lam-c E'-c
--   RET : Code (VAL α₁-c ∷ S) S' E-c E'-c → Code (VAL α₁-c ∷ ENV E-c ∷ S) S' (α₂-c ∷ E-lam-c) E'-c
--   APP : Code (VAL α₁-c ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') →
--         Code (VAL (α₂-c ⇒-c α₁-c , E-lam-c) ∷ VAL α₂-c ∷ S) S' (conv-ty-lst E) (conv-ty-lst E')
--   HALT : Code S S E-c E-c

comp : Expr α E → Code (α ∷ S) S' → Code S S'
comp (Val n) c = PUSH n c
comp (Add x x₁) c = {!!}
comp (Var v) c = {!!}
comp (Abs x) c = {!!}
comp (App x x₁) c = {!!}
-- comp : Expr α E → Code (VAL (conv-ty α) ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') → Code S S' (conv-ty-lst E) (conv-ty-lst E')
-- comp (Val n) c = PUSH n c
-- comp (Add e₁ e₂) c = (comp e₁ (comp e₂ (ADD c)))
-- comp (Var v) c = LOOKUP v c
-- comp (Abs e) c =
--   ABS
--     (λ {S : List STy} {S' : List STy} {E : List Ty} {E' : List Ty}
--          (c' : Code (VAL _ ∷ S) S' (conv-ty-lst E) (conv-ty-lst E'))
--       → (comp e (RET c')))
--     c
-- comp (App e₁ e₂) c = comp e₂ (comp e₁ (APP c))

-- lookup-c : var α E → Env-c (conv-ty-lst E) → El-Ty-c (conv-ty α)
-- lookup-c zero (cons-c fst rest) = fst
-- lookup-c (suc v) (cons-c fst rest) = lookup-c v rest

exec : Code S S' → (s : Stack S) → Stack S'
exec (PUSH n c) s = exec c (Val n ▷ s)
-- {-# TERMINATING #-}
-- exec : Code S S' E-c E'-c → Stack S × Env-c E-c → Stack S' × Env-c E'-c
-- exec (PUSH n c) ⟨ s , env ⟩ = exec c ⟨ n ▷ s , env ⟩
-- exec (ADD c) ⟨ m ▷ n ▷ s , env ⟩ = exec c ⟨ (n + m) ▷ s , env ⟩
-- exec (LOOKUP v c) ⟨ s , env ⟩ = exec c ⟨ (lookup-c v env) ▷ s , env ⟩
-- exec (ABS lam c) ⟨ s , env-lam ⟩ = exec c ⟨ ⟨ lam , env-lam ⟩ ▷ s , env-lam ⟩
-- exec (RET c') ⟨ x₁ ▷ env ▷ s , cons-c x₂ env-lam ⟩ = exec c' ⟨ x₁ ▷ s , env ⟩
-- exec (APP c) ⟨ ⟨ lam ,  env-lam ⟩ ▷ x₂ ▷ s , env ⟩ = exec (lam c) ⟨ env ▷ s , cons-c x₂ env-lam ⟩
-- exec HALT ⟨ s , env ⟩ = ⟨ s , env ⟩

-- conv-env : Env E → Env-c (conv-ty-lst E)
conv : {α : Ty} → El α → Elem α
conv {nat} n = Val n
conv {α₂ ⇒ α₁} f = Clo f
-- conv {α₂ ⇒ α₁ , E} (clo e-lam e-env) = ⟨ (λ c' → comp e-lam (RET c')) , conv-env e-env ⟩

-- conv-env nil = nil-c
-- conv-env (cons v env) = cons-c (conv v) (conv-env env)



correct :
  (e : Expr α E)
  (c : Code (α ∷ S) S')
  (s : Stack S)
  (env : Env E)
  →
  exec (comp e c) s ≡ eval e env (λ v → exec c (conv v ▷ s))

correct {E = E} (Val n) c s env =
  begin
    exec (comp {E = E} (Val n) c) s
  ≡⟨ refl ⟩
    exec (PUSH n c) s
  ≡⟨ refl ⟩
    exec c (Val n ▷ s)
  ∎
correct (Add e e₁) c s env = {!!}
correct (Var v) c s env = {!!}
correct (Abs e) c s env =
  begin
    exec (comp (Abs e) c) s
  ≡⟨ {!!} ⟩
    exec c (Clo (λ x → eval e (cons x env)) ▷ s)
  ∎
correct (App e₁ e₂) c s env =
  begin
    exec (comp (App e₁ e₂) c) s
  ≡⟨ {!!} ⟩
    exec c (conv (eval e₁ env (eval e₂ env)) ▷ s)
  ∎

-}
