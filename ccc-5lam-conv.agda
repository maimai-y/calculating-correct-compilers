
module ccc-5lam-conv where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty

El : Ty → Set
El nat = ℕ
El (α₂ ⇒ α₁) = (El α₂) → (El α₁)

--data Value : Ty → Set
data Env : List Ty → Set
data Expr : Ty → List Ty → Set

-- the following variables automatically become implicit arguments
variable
  α α' α₁ α₂ σ : Ty
  E E' E-lam : List Ty

data Env where
  nil : Env []
  cons : El α → Env E → Env (α ∷ E)

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

eval : (Expr α E) → Env E → El α
eval (Val n) env = n
eval (Add e₁ e₂) env = (eval e₁ env) + (eval e₂ env)
eval (Var v) env = lookup v env
eval (Abs e) env = λ x → eval e (cons x env)
eval (App e₁ e₂) env = (eval e₁ env) (eval e₂ env)

data Ty-c : Set
data STy : Set
data Code : List STy → List STy → List Ty-c → List Ty-c → Set
variable
  α-c α'-c α₁-c α₂-c σ-c : Ty-c
  S S' : List STy
  E-c E'-c E-lam-c : List Ty-c
  β : STy
  
data Ty-c where
  nat-c : Ty-c
  lam-typ : (α₁-c α₂-c : Ty-c) (S S' : List STy) (E-c E'-c E-lam-c : List Ty-c) → Ty-c

data STy where
  VAL : Ty-c → STy
  ENV : List Ty-c → STy

conv-ty : Ty → Ty-c
conv-ty nat = nat-c
conv-ty (α₂ ⇒ α₁) = {!!}

El-Ty-c : Ty-c → Set

data Env-c : List Ty-c → Set where
  nil-c : Env-c []
  cons-c : El-Ty-c α-c → Env-c E-c → Env-c (α-c ∷ E-c)

El-Ty-c nat-c = ℕ
El-Ty-c (lam-typ α₁-c α₂-c S S' E-c E'-c E-lam-c)
  = (Code (VAL α₁-c ∷ S) S' E-c E'-c →
    Code (ENV E-c ∷ S) S' (α₂-c ∷ E-lam-c) E'-c) × Env-c E-lam-c

El-STy : STy → Set
El-STy (VAL α-c) = El-Ty-c α-c
El-STy (ENV E) = Env-c E
-- El-STy nat-typ = ℕ
-- El-STy (lst-typ E) = Env E
-- El-STy (lam-typ α₁ α₂ S S' E E' E-lam) = (Code (to-STy α₁ ∷ S) S' E E' → Code (lst-typ E ∷ S) S' (α₂ ∷ E-lam) E') × Env E-lam

-- El-STy : {S S' : List STy} {E E-lam : List Ty} → STy → Set
-- El-STy (typ nat) = ℕ
-- El-STy {S} {S'} {E} {E-lam} (typ (α₂ ⇒ α₁)) = Code (typ α₁ ∷ S) S' E → Code (lst-typ E ∷ S) S' (α₂ ∷ E-lam)

-- data Elem : STy → Set where
--   VAL : El α → Elem (typ α)
--   -- CLO : Elem clo

data Stack : List STy → Set where
  ϵ : Stack []
  --_▷_ : El α → Stack S → Stack (typ α ∷ S)
  _▷_ : El-STy β → Stack S → Stack (β ∷ S)
infixr 40 _▷_

conv-ty-lst : List Ty → List Ty-c
conv-ty-lst [] = []
conv-ty-lst (fst ∷ rst) = conv-ty fst ∷ conv-ty-lst rst

data Code where
  PUSH : (n : ℕ) → Code (VAL nat-c ∷ S) S' E-c E'-c → Code S S' E-c E'-c
  ADD : Code (VAL nat-c ∷ S) S' E-c E'-c → Code (VAL nat-c ∷ VAL nat-c ∷ S) S' E-c E'-c
  LOOKUP : var α E → Code (VAL (conv-ty α) ∷ S) S' (conv-ty-lst E) E'-c → Code S S' (conv-ty-lst E) E'-c
  ABS : (Code (VAL α₁-c ∷ S) S' E-c E'-c → Code (ENV E-c ∷ S) S' (α₂-c ∷ E-lam-c) E'-c) →
        Code (VAL (lam-typ α₁-c α₂-c S S' E-c E'-c E-lam-c) ∷ S) S' E-lam-c E'-c →
        --Code (lam-typ {α₁} {S} {S'} {E} {α₂} {E-lam} (Code (typ α₁ ∷ S) S' E → Code (lst-typ E ∷ S) S' (α₂ ∷ E-lam)) ∷ lst-typ E-lam ∷ S) S' E-lam →
        Code S S' E-lam-c E'-c
  RET : Code (VAL α₁-c ∷ S) S' E-c E'-c → Code (VAL α₁-c ∷ ENV E-c ∷ S) S' (α₂-c ∷ E-lam-c) E'-c
  APP : Code (VAL α₁-c ∷ S) S' E-c E'-c →
        Code (VAL (lam-typ α₁-c α₂-c S S' E-c E'-c E-lam-c) ∷ VAL α₂-c ∷ S) S' E-c E'-c
  HALT : Code S S E-c E-c
  
comp : Expr α E → Code (VAL (conv-ty α) ∷ S) S' (conv-ty-lst E) (conv-ty-lst E') → Code S S' (conv-ty-lst E) (conv-ty-lst E')
comp (Val n) c = PUSH n c
comp (Add e₁ e₂) c = (comp e₁ (comp e₂ (ADD c)))
comp (Var v) c = LOOKUP v c
comp (Abs e) c = ABS (λ c' → (comp e (RET c'))) c
comp (App e₁ e₂) c = comp e₂ (comp e₁ (APP c))

lookup-c : var α E → Env-c (conv-ty-lst E) → El-Ty-c (conv-ty α)
lookup-c zero (cons-c fst rest) = fst
lookup-c (suc v) (cons-c fst rest) = lookup-c v rest

{-# TERMINATING #-}
exec : Code S S' E-c E'-c → Stack S × Env-c E-c → Stack S' × Env-c E'-c
exec (PUSH n c) ⟨ s , env ⟩ = exec c ⟨ n ▷ s , env ⟩
exec (ADD c) ⟨ m ▷ n ▷ s , env ⟩ = exec c ⟨ (n + m) ▷ s , env ⟩
exec (LOOKUP v c) ⟨ s , env ⟩ = exec c ⟨ (lookup-c v env) ▷ s , env ⟩
exec (ABS lam c) ⟨ s , env-lam ⟩ = exec c ⟨ ⟨ lam , env-lam ⟩ ▷ s , env-lam ⟩
exec (RET c') ⟨ x₁ ▷ env ▷ s , cons-c x₂ env-lam ⟩ = exec c' ⟨ x₁ ▷ s , env ⟩
exec (APP c) ⟨ ⟨ lam ,  env-lam ⟩ ▷ x₂ ▷ s , env ⟩ = exec (lam c) ⟨ env ▷ s , cons-c x₂ env-lam ⟩
exec HALT ⟨ s , env ⟩ = ⟨ s , env ⟩
{-

correct :
  (e : Expr α E)
  (c : Code (typ α ∷ S) S' E)
  (s : Stack S)
  (env : Env E)
  →
  exec (comp e c) ⟨ s , env ⟩ ≡ exec c ⟨ eval e env ▷ s , env ⟩

correct (Val n) c s env =
  begin
    exec (comp (Val n) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (PUSH n c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ n ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ eval (Val n) env ▷ s , env ⟩
  ∎

correct (Add e₁ e₂) c s env =
  begin
    exec (comp (Add e₁ e₂) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (comp e₁ (comp e₂ (ADD c))) ⟨ s , env ⟩
  ≡⟨ correct e₁ (comp e₂ (ADD c)) s env ⟩
    exec (comp e₂ (ADD c)) ⟨ (eval e₁ env ▷ s) , env ⟩
  ≡⟨ correct e₂ (ADD c) (eval e₁ env ▷ s) env ⟩
    exec (ADD c) ⟨ (eval e₂ env ▷ eval e₁ env ▷ s) , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ ((eval e₁ env) + (eval e₂ env)) ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ eval (Add e₁ e₂) env ▷ s , env ⟩
  ∎

correct (Var v) c s env =
  begin
    exec (comp (Var v) c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec (LOOKUP v c) ⟨ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ lookup v env ▷ s , env ⟩
  ≡⟨ refl ⟩
    exec c ⟨ eval (Var v) env ▷ s , env ⟩
  ∎

-- correct (Abs e) c s env =
--   begin
--     exec (comp (Abs e) c) ⟨ s , env ⟩
--   ≡⟨ refl ⟩
--     exec (ABS (comp e HALT) c) ⟨ s , env ⟩
--   ≡⟨ refl ⟩
--     exec c ⟨ (λ x → head (proj₁ (exec (comp e HALT) ⟨ ϵ , cons x env ⟩))) ▷ s , env ⟩
--   ≡⟨ {!!} ⟩
--   --≡⟨ {!cong (λ pr → exec c ⟨ (λ x → head (proj₁ pr)) ▷ s , env ⟩) (correct e HALT ϵ (cons x env))!} ⟩
--     exec c ⟨ (λ x → head (proj₁ (exec HALT ⟨ eval e (cons x env) ▷ ϵ , cons x env ⟩))) ▷ s , env ⟩
--   ≡⟨ refl ⟩
--     exec c ⟨ eval (Abs e) env ▷ s , env ⟩
--   ∎

-- correct (App e₁ e₂) c s env =
--   begin
--     exec (comp (App e₁ e₂) c) ⟨ s , env ⟩
--   ≡⟨ refl ⟩
--     exec (comp e₂ (comp e₁ (APP c))) ⟨ s , env ⟩
--   ≡⟨ correct e₂ (comp e₁ (APP c)) s env ⟩
--     exec (comp e₁ (APP c)) ⟨ (eval e₂ env) ▷ s , env ⟩
--   ≡⟨ correct e₁ (APP c) ((eval e₂ env) ▷ s) env ⟩
--     exec (APP c) ⟨ eval e₁ env ▷ eval e₂ env ▷ s , env ⟩
--   ≡⟨ refl ⟩
--     exec c ⟨ (eval e₁ env) (eval e₂ env) ▷ s , env ⟩
--   ≡⟨ refl ⟩
--     exec c ⟨ eval (App e₁ e₂) env ▷ s , env ⟩
--   ∎

-}
compile : Expr α E → Code S (VAL (conv-ty α) ∷ S) (conv-ty-lst E) (conv-ty-lst E)
compile e = comp e HALT

-- correct' : (e : Expr α E) (s : Stack S) (env : Env E) → exec (compile e) ⟨ s , env ⟩ ≡ ⟨ eval e env ▷ s , env ⟩
-- correct' e s env =
--   begin
--     exec (compile e) ⟨ s , env ⟩
--   ≡⟨ refl ⟩
--     exec (comp e HALT) ⟨ s , env ⟩
--   ≡⟨ correct e HALT s env ⟩
--     exec HALT ⟨ eval e env ▷ s , env ⟩
--   ≡⟨ refl ⟩
--     ⟨ eval e env ▷ s , env ⟩
--   ∎

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

test3 : exec (compile Expr3) ⟨ ϵ , nil-c ⟩ ≡ ⟨ 3 ▷ ϵ , nil-c ⟩
test3 = refl

test5 : exec (compile Expr5) ⟨ ϵ , nil-c ⟩ ≡ ⟨ 5 ▷ ϵ , nil-c ⟩
test5 = refl

test6 : exec (compile Expr6) ⟨ ϵ , nil-c ⟩ ≡ ⟨ 8 ▷ ϵ , nil-c ⟩
test6 = refl

test7 : exec (compile Expr7) ⟨ ϵ , nil-c ⟩ ≡ ⟨ 5 ▷ ϵ , nil-c ⟩
test7 = refl


