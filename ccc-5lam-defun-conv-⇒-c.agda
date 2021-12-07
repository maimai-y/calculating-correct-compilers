
module ccc-5lam-defun-conv-⇒-c where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

-- the following variables automatically become implicit arguments
variable
  α α' α₁ α₂ σ : Ty
  E E' E-lam : List Ty

data Value : Ty → Set
data Env : List Ty → Set
data Expr : Ty → List Ty → Set

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

---------------------------------------------------------------------意味論　終わり

data STy : Set
data Ty-c : Set

data Ty-c where
  nat-c : Ty-c
  ⇒-c :
    Ty-c → Ty-c →
    List STy → -- 最初のstack　型がどうなっているstackの上にα₁が置かれるか　関数適用する前のstack
    List STy → -- 最後のstack　最後まで継続の仕事を終わらせたらstackはどうなるか
    List Ty-c → -- 最初の環境
    List Ty-c → -- 最後の環境
    Ty-c

data STy where
  typ : Ty-c → STy
  -- clo-ty S S' E E'は退避させた継続の型、環境の型がそれぞれCode S S' E E'、Env Eであったことを表す
  clo-ty : List STy → List STy → List Ty-c → List Ty-c → STy

-- the following variables automatically become implicit arguments
variable
  α-c α'-c α₁-c α₂-c σ-c : Ty-c
  β : STy
  E-c E'-c E-lam-c : List Ty-c
  S S' : List STy

{-# TERMINATING #-}
conv-ty : {S S' : List STy} {E-c E'-c : List Ty-c} → Ty → Ty-c
conv-ty nat = nat-c
conv-ty {S = S} {S' = S'} {E-c = E-c} {E'-c = E'-c} (α₂ ⇒ α₁) =
  ⇒-c
  (conv-ty {S = S} {S' = S'} {E-c = E-c} {E'-c = E'-c} α₂)
  (conv-ty
    -- {S = typ (conv-ty {S = S} {S' = S'} {E-c = E-c} {E'-c = E'-c} α₂) ∷
    --             typ (conv-ty {S = S} {S' = S'} {E-c = E-c} {E'-c = E'-c} (α₂ ⇒ α₁)) ∷
    --             S}
           {S' = S'}
           {E-c = E-c}
           {E'-c = E'-c}
           α₁)
  S S' E-c E'-c

conv-ty-lst : List Ty → List Ty-c
conv-ty-lst [] = []
conv-ty-lst (fst ∷ rst) = conv-ty fst ∷ conv-ty-lst rst

data Env-c : List Ty-c → Set
conv-env : Env E → Env-c (conv-ty-lst E)
data Code : List STy → List STy → List Ty-c → List Ty-c → Set
comp : {S S' : List STy} {E E' : List Ty} →
       Expr α E →
       Code (typ (conv-ty {S = S} {S' = S'} {E-c = conv-ty-lst E} {E'-c = conv-ty-lst E'} α) ∷ S)
            S'
            (conv-ty-lst E)
            (conv-ty-lst E') →
       Code S S' (conv-ty-lst E) (conv-ty-lst E')

data Value-c : Ty-c → Set where
  Num-c : (n : ℕ) → Value-c nat-c
  Clo-c : {S S' : List STy} {E-c E'-c : List Ty-c} →
          (code : Code (clo-ty (typ α₁-c ∷ S) S' E-c E'-c ∷ S) S' (α₂-c ∷ E-lam-c) E'-c)
          → (env : Env-c E-lam-c)
          → Value-c (⇒-c α₂-c α₁-c S S' E-c E'-c)

data Code where
  PUSH : (n : ℕ) → Code (typ nat-c ∷ S) S' E-c E'-c → Code S S' E-c E'-c
  ADD : Code (typ nat-c ∷ S) S' E-c E'-c → Code (typ nat-c ∷ typ nat-c ∷ S) S' E-c E'-c
  LOOKUP : var α E → Code (typ (conv-ty α) ∷ S) S' (conv-ty-lst E) E'-c → Code S S' (conv-ty-lst E) E'-c
  ABS : Code (clo-ty (typ (conv-ty α₁) ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') ∷ S)
             S'
             (conv-ty-lst (α₂ ∷ E-lam))
             (conv-ty-lst E') →
        Code (typ (⇒-c (conv-ty α₂) (conv-ty α₁)　S S' (conv-ty-lst E) (conv-ty-lst E')) ∷ S)
             S'
             (conv-ty-lst E-lam)
             (conv-ty-lst E')
        → Code S S' (conv-ty-lst E-lam) (conv-ty-lst E')
  RET : Code
        (typ (conv-ty α₁) ∷ clo-ty (typ (conv-ty α₁) ∷ S) S' E-c E'-c ∷ S)
        S'
        ((conv-ty α₂) ∷ E-lam-c)
        E'-c
  APP : Code (typ (conv-ty α₁) ∷ S) S' E-c E'-c
        → Code (typ (conv-ty α₂) ∷ typ (conv-ty (α₂ ⇒ α₁)) ∷ S)
                --typ (⇒-c (conv-ty α₂) (conv-ty α₁) S S' E-c E'-c) ∷ S)
               S'
               E-c
               E'-c
  HALT : Code S S E-c E-c

conv : {S S' : List STy} {E E' : List Ty} →
       Value α →
       Value-c (conv-ty {S = S} {S' = S'} {E-c = conv-ty-lst E} {E'-c = conv-ty-lst E'} α)
conv (Num n) = Num-c n
conv {S = S} {S' = S'} {E = E} {E' = E'} (Clo {α₁ = α₁} {α₂ = α₂} {E-lam = E-lam} exp env)
  = Clo-c
    {α₁-c = conv-ty α₁} {α₂-c = conv-ty α₂}
    {E-lam-c = conv-ty-lst E-lam}
    {S = S} {S' = S'} {E-c = conv-ty-lst E} {E'-c = conv-ty-lst E'}
    (comp {S = clo-ty (typ (conv-ty α₁) ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') ∷ S}
          {S' = S'}
          {E = α₂ ∷ E-lam}
          {E' = E'}
          exp RET)
    (conv-env env)

data Env-c where
  nil-c : Env-c []
  cons-c : Value-c α-c → Env-c E-c → Env-c (α-c ∷ E-c)
  
conv-env nil = nil-c
conv-env (cons v env) = cons-c (conv v) (conv-env env)

-- ValueのStack版のような感じ Elem-cの意味でElem
data Elem : STy → Set where
  VAL : Value-c α-c → Elem (typ α-c)
  CLO : Code (typ α₁-c ∷ S) S' E-c E'-c → Env-c E-c → Elem (clo-ty (typ α₁-c ∷ S) S' E-c E'-c)

data Stack : List STy → Set where
  ϵ : Stack []
  _▷_ : Elem β → Stack S → Stack (β ∷ S)
infixr 40 _▷_

comp (Val n) c = PUSH n c
comp (Add e₁ e₂) c = (comp e₁ (comp e₂ (ADD c)))
comp (Var v) c = LOOKUP v c
comp (Abs e) c = ABS (comp e RET) c
comp (App e₁ e₂) c = comp e₁ (comp e₂ (APP c))

lookup-c : var α E → Env-c (conv-ty-lst E) → Value-c (conv-ty α)
lookup-c zero (cons-c fst rest) = fst
lookup-c (suc v) (cons-c fst rest) = lookup-c v rest

{-# TERMINATING #-}
exec : Code S S' E-c E'-c → Stack S × Env-c E-c → Stack S' × Env-c E'-c
exec (PUSH n c) ⟨ s , env-c ⟩ = exec c ⟨ VAL (Num-c n) ▷ s , env-c ⟩
exec (ADD c) ⟨ VAL (Num-c m) ▷ VAL (Num-c n) ▷ s , env-c ⟩ =
  exec c ⟨ VAL (Num-c (n + m)) ▷ s , env-c ⟩
exec (LOOKUP v-c c) ⟨ s , env-c ⟩ = exec c ⟨ VAL (lookup-c v-c env-c) ▷ s , env-c ⟩
exec (ABS code c) ⟨ s , env-c ⟩ = exec c ⟨ VAL (Clo-c code env-c) ▷ s , env-c ⟩
exec RET ⟨ VAL v₁-c ▷ CLO c env-c ▷ s , _ ⟩ = exec c ⟨ VAL v₁-c ▷ s , env-c ⟩
exec (APP c) ⟨ (VAL v₂-c) ▷ VAL (Clo-c code-lam env-lam) ▷ s , env-c ⟩
  = exec code-lam ⟨ CLO c env-c ▷ s , cons-c v₂-c env-lam ⟩
exec HALT ⟨ s , env-c ⟩ = ⟨ s , env-c ⟩

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

{-# TERMINATING #-}
correct :
  (e : Expr α E)
  (c : Code (typ (conv-ty α) ∷ S) S' (conv-ty-lst E) (conv-ty-lst E'))
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
    exec c ⟨ VAL (Num-c n) ▷ s , conv-env env ⟩
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
    exec (ADD c) ⟨ VAL (Num-c m) ▷ VAL (conv (eval e₁ env)) ▷ s , conv-env env ⟩
  ≡⟨ cong (λ v → exec (ADD c) ⟨ VAL (Num-c m) ▷ VAL (conv v) ▷ s , conv-env env ⟩) eq₁ ⟩
    exec (ADD c) ⟨ VAL (Num-c m) ▷ VAL (Num-c n) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (Num-c (n + m)) ▷ s , conv-env env ⟩
  -- ≡⟨ refl ⟩
  --   exec c ⟨ VAL (conv (eval (Add e₁ e₂) env)) ▷ s , conv-env env ⟩
  ∎

correct (Var v) c s env =
  begin
    exec (comp (Var v) c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (LOOKUP v c) ⟨ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (lookup-c v (conv-env env)) ▷ s , conv-env env ⟩
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
  --   exec c ⟨ VAL (Clo-c (comp e RET) (conv-env env)) ▷ s , conv-env env ⟩
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
  ≡⟨ refl ⟩
    exec (APP c) ⟨ VAL (conv (eval e₂ env)) ▷ VAL (Clo-c (comp e-lam RET) (conv-env env-lam)) ▷ s , conv-env env ⟩
  ≡⟨ refl ⟩
    exec (comp e-lam RET) ⟨ CLO c (conv-env env) ▷ s , cons-c (conv (eval e₂ env)) (conv-env env-lam) ⟩
  ≡⟨ refl ⟩
    exec (comp e-lam RET) ⟨ CLO c (conv-env env) ▷ s , conv-env (cons (eval e₂ env) env-lam) ⟩
  ≡⟨ correct e-lam RET (CLO c (conv-env env) ▷ s) (cons (eval e₂ env) env-lam) ⟩
    exec RET ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ CLO c (conv-env env) ▷ s ,
               conv-env (cons (eval e₂ env) env-lam) ⟩
  ≡⟨ refl ⟩
    exec RET ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ CLO c (conv-env env) ▷ s ,
               cons-c (conv (eval e₂ env)) (conv-env env-lam) ⟩
  ≡⟨ refl ⟩
    exec c ⟨ VAL (conv (eval e-lam (cons (eval e₂ env) env-lam))) ▷ s , conv-env env ⟩
  -- ≡⟨ {!!} ⟩
  --   exec c ⟨ VAL (conv (eval (App e₁ e₂) env)) ▷ s , conv-env env ⟩
  ∎

compile : Expr α E → Code S (typ (conv-ty α) ∷ S) (conv-ty-lst E) (conv-ty-lst E)
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

test3 : exec (compile Expr3) ⟨ ϵ , nil-c ⟩ ≡ ⟨ VAL (Num-c 3) ▷ ϵ , nil-c ⟩
test3 = refl

test5 : exec (compile Expr5) ⟨ ϵ , nil-c ⟩ ≡ ⟨ VAL (Num-c 5) ▷ ϵ , nil-c ⟩
test5 = refl

test6 : exec (compile Expr6) ⟨ ϵ , nil-c ⟩ ≡ ⟨ VAL (Num-c 8) ▷ ϵ , nil-c ⟩
test6 = refl

test7 : exec (compile Expr7) ⟨ ϵ , nil-c ⟩ ≡ ⟨ VAL (Num-c 5) ▷ ϵ , nil-c ⟩
test7 = refl
