
module ccc-5lam where

open import Data.Nat
open import Data.Bool using(Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Value : Set
data Env : List Value → Set
data Expr : Value → List Value → Set

-- the following variables automatically become implicit arguments
variable
  α α' α₁ α₂ σ : Value
  E E' E'' E₀ : List Value
  n m p : ℕ

data Value where
  Num : (n : ℕ) → Value -- n不要かも 
  Clo : (exp : Expr α₁ (α₂ ∷ E)) → (env : List Value) → Value

data Env where
  env : (l : List Value) → Env l

-- variables
data var : (α : Value) (E : List Value) → Set where
  zero : var α (α ∷ E)
  suc  : (x : var α E) → var α (σ ∷ E)

data Expr where
  Val : (n : ℕ) → Expr (Num n) E
  Add : Expr (Num n) E → Expr (Num m) E → Expr (Num (n + m)) E
  Var : (v : var α E) → Expr α E
  Abs : (exp : Expr α₁ (α₂ ∷ E)) →
        Expr (Clo exp E) E
  App : {β : (Expr α₁ (α₂ ∷ E'))} → (e₁ : Expr (Clo β E') E) →
        (e₂ : Expr α₂ E) →
          Expr α₁ E

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
  fun : (exp : Expr α E) → (env : List Value) → Fun 
  
El : Value → Set
El (Num n) = ℕ
El (Clo exp E) = Fun

eval : (Expr α E) → Env E → El α
eval (Val n) e = n
eval (Add x y) e with (eval x e) | (eval y e)
... | n | m = n + m
eval {Num n} (Var zero) (env .(Num n ∷ _)) = n
eval {Clo ex en} (Var zero) (env .(Clo ex en ∷ _)) = fun ex en
eval (Var (suc v)) (env (x ∷ l)) = eval (Var v) (env l)
eval (Abs exp) (env lst) = fun exp lst
eval (App {α₁ = Num n} x y) (env lst) = n
eval (App {α₁ = Clo ex en} x y) (env lst) = fun ex en

data Elem : Set
data Code : List Elem → List Elem → List Value → List Value → Set
  
variable
  S S' S'' : List Elem
  el : Elem

data Elem where
  VAL : Value → Elem
  CLO : Code S S' E E' → Env E → Elem

data Stack : List Elem → Set where
  ϵ : Stack []
  _▷_ : El α → Stack S → Stack (VAL α ∷ S)
infixr 40 _▷_

data Code where
  PUSH : (n : ℕ) → Code ((VAL (Num n)) ∷ S) S' E E'' → Code S S' E E''
  ADD : Code ((VAL (Num p)) ∷ S) S' E E'' → Code ((VAL (Num m)) ∷ (VAL (Num n)) ∷ S) S' E E''

comp : Expr α E → Code (VAL α ∷ S) S' E E' → Code S S' E E'

comp (Val n) c = PUSH n c
comp (Add x y) c = (comp x (comp y (ADD c)))
comp (Var v) c = {!!}
comp (Abs e) c = {!!}
comp (App e e₁) c = {!!}

exec : Code S S' E E' → Stack S × Env E → Stack S' × Env E'
exec (PUSH n c) ⟨ s , ev' ⟩ = exec c ⟨ n ▷ s , ev' ⟩
exec (ADD c) ⟨ m ▷ n ▷ s , ev' ⟩ = exec c ⟨ (n + m) ▷ s , ev' ⟩

correct :
  (e : Expr α E)
  (c : Code (VAL α ∷ S) S' E E')
  (s : Stack S)
  (ev : Env E)
  →
  exec (comp e c) ⟨ s , ev ⟩ ≡ exec c ⟨ eval e ev ▷ s , ev ⟩

correct (Val n) c s ev =
  begin
    exec (comp (Val n) c) ⟨ s , ev ⟩
  ≡⟨ refl ⟩
    exec (PUSH n c) ⟨ s , ev ⟩
  ≡⟨ refl ⟩
    exec c ⟨ n ▷ s , ev ⟩
  ≡⟨ refl ⟩
    exec c ⟨ eval (Val n) ev ▷ s , ev ⟩
  ∎
correct (Add x y) c s ev =
  begin
    exec (comp (Add x y) c) ⟨ s , ev ⟩
  ≡⟨ refl ⟩
    exec (comp x (comp y (ADD c))) ⟨ s , ev ⟩
  ≡⟨ correct x (comp y (ADD c)) s ev ⟩
    exec (comp y (ADD c)) ⟨ (eval x ev ▷ s) , ev ⟩
  ≡⟨ correct y (ADD c) (eval x ev ▷ s) ev ⟩
    exec (ADD c) ⟨ (eval y ev ▷ eval x ev ▷ s) , ev ⟩
  ≡⟨ refl ⟩
    exec c ⟨ ((eval x ev) + (eval y ev)) ▷ s , ev ⟩
  ≡⟨ refl ⟩
    exec c ⟨ eval (Add x y) ev ▷ s , ev ⟩
  ∎
correct (Var v) c s ev = {!!}
correct (Abs e) c s ev = {!!}
correct (App e e₁) c s ev = {!!}
