-- Normalization by evaluation for the β-STLC.
-- Computes β-normal form (no η-equality).

-- Andreas Abel, 2018-10-31

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Types, contexts, variables.

data Ty : Set where
  o : Ty
  _⇒_ : (A B : Ty) → Ty

Cxt = List Ty

Var : Cxt → Ty → Set
Var Γ A = A ∈ Γ

pattern vz = here refl
pattern vs x = there x

variable
  Γ Δ Φ : Cxt
  A B C : Ty

-- Terms.

data Tm (Γ : Cxt) : Ty → Set where
  var : (x : Var Γ A) → Tm Γ A
  abs : (t : Tm (A ∷ Γ) B) → Tm Γ (A ⇒ B)
  app : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A) → Tm Γ B

-- Neutral and non-neutral β-normal forms.

mutual
  data Ne Γ : Ty → Set where
    var : (x : Var Γ A) → Ne Γ A
    app : (t : Ne Γ (A ⇒ B)) (u : Nf Γ A) → Ne Γ B

  data Nf Γ : Ty → Set where
    ne  : (t : Ne Γ A) → Nf Γ A
    abs : (t : Nf (A ∷ Γ) B) → Nf Γ (A ⇒ B)

-- Category of order-preserving embeddings (renamings).

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : Γ ≤ Γ
  wk   : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ Δ
  lift : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ (A ∷ Δ)

_•_ : (ρ : Γ ≤ Φ) (ρ' : Δ ≤ Γ) → Δ ≤ Φ
ρ      • id      = ρ
ρ      • wk ρ'   = wk (ρ • ρ')
id     • lift ρ' = lift ρ'
wk ρ   • lift ρ' = wk (ρ • ρ')
lift ρ • lift ρ' = lift (ρ • ρ')

-- Var, Ne, Nf are presheaves (monotonicity).

monVar : (ρ : Δ ≤ Γ) → Var Γ A → Var Δ A
monVar id       x      = x
monVar (wk ρ)   x      = vs (monVar ρ x)
monVar (lift ρ) vz     = vz
monVar (lift ρ) (vs x) = vs (monVar ρ x)

mutual
  monNe : (ρ : Δ ≤ Γ) → Ne Γ A → Ne Δ A
  monNe ρ (var x)   = var (monVar ρ x)
  monNe ρ (app t u) = app (monNe ρ t) (monNf ρ u)

  monNf : (ρ : Δ ≤ Γ) → Nf Γ A → Nf Δ A
  monNf ρ (ne t)  = ne  (monNe ρ t)
  monNf ρ (abs t) = abs (monNf (lift ρ) t)

-- Semantics of types.

data _⊎̂_ (A B : Set) : Set where
  ne  : (t : A) → A ⊎̂ B
  val : (f : B) → A ⊎̂ B

⟦_⟧ : Ty → Cxt → Set
⟦ A ⟧ Γ = Ne Γ A ⊎̂ Val A
  where
  Val : Ty → Set
  Val o       = ⊥
  Val (A ⇒ B) = ∀{Δ} (ρ : Δ ≤ Γ) → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ

-- Semantics of contexts.

⟦_⟧G : (Φ Γ : Cxt) → Set
⟦ []    ⟧G Γ = ⊤
⟦ A ∷ Φ ⟧G Γ = ⟦ Φ ⟧G Γ × ⟦ A ⟧ Γ

-- Variables are projections.

⦅_⦆v : Var Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ vz   ⦆v = proj₂
⦅ vs x ⦆v = ⦅ x ⦆v ∘ proj₁

-- Semantic types and contexts are presheaves.

mon  : (ρ : Δ ≤ Γ) → ∀{A} → ⟦ A ⟧  Γ → ⟦ A ⟧  Δ
mon ρ         (ne  t) = ne (monNe ρ t)
mon ρ {A ⇒ B} (val f) = val λ ρ' → f (ρ • ρ')
mon ρ {o}     (val ())

monG : (ρ : Δ ≤ Γ) → ∀{Φ} → ⟦ Φ ⟧G Γ → ⟦ Φ ⟧G Δ
monG ρ {[]}    _       = _
monG ρ {A ∷ Φ} (γ , a) = monG ρ γ , mon ρ a

-- Reification.

reify : ∀{A} → ⟦ A ⟧ Γ → Nf Γ A
reify             (ne  t) = ne t
reify {A = B ⇒ C} (val f) = abs (reify (f (wk id) (ne (var vz))))
reify {A = o}     (val ())

-- Application and evaluation.

apply : ⟦ A ⇒ B ⟧ Γ → ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
apply (ne t) a = ne (app t (reify a))
apply (val f) a = f id a

⦅_⦆ : Tm Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ var x ⦆   γ = ⦅ x ⦆v γ
⦅ abs t ⦆   γ = val λ ρ a → ⦅ t ⦆( monG ρ γ , a )
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)

-- Identity environment.

env : ∀{Γ} (ρ : Δ ≤ Γ) → ⟦ Γ ⟧G Δ
env {Γ = []}    ρ = _
env {Γ = A ∷ Γ} ρ = env (wk id • ρ) , ne (var (monVar ρ vz))

-- Normalization.

nf : Tm Γ A → Nf Γ A
nf t = reify (⦅ t ⦆ (env id))
