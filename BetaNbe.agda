-- Normalization by evaluation for the β-STLC.
-- Computes β-normal form (no η-equality).

-- Andreas Abel, 2018-10-31

open import Data.List using (List; []; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- Semantics of types and contexts.

⟦_⟧ : Ty → Cxt → Set
⟦ o     ⟧ Γ = Ne Γ o
⟦ A ⇒ B ⟧ Γ = Ne Γ (A ⇒ B) ⊎ (∀{Δ} (ρ : Δ ≤ Γ) → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ)

⟦_⟧G : (Φ Γ : Cxt) → Set
⟦ []    ⟧G Γ = ⊤
⟦ A ∷ Φ ⟧G Γ = ⟦ Φ ⟧G Γ × ⟦ A ⟧ Γ

-- Variables are projections.

⦅_⦆v : Var Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ vz   ⦆v = proj₂
⦅ vs x ⦆v = ⦅ x ⦆v ∘ proj₁

-- Semantic types and contexts are presheaves.

mon : (ρ : Δ ≤ Γ) → ∀{A} → ⟦ A ⟧ Γ → ⟦ A ⟧ Δ
mon ρ {o} t = monNe ρ t
mon ρ {A ⇒ B} (inj₁ t) = inj₁ (monNe ρ t)
mon ρ {A ⇒ B} (inj₂ f) = inj₂ λ ρ' → f (ρ • ρ')

monG : (ρ : Δ ≤ Γ) → ∀{Φ} → ⟦ Φ ⟧G Γ → ⟦ Φ ⟧G Δ
monG ρ {[]}    _       = _
monG ρ {A ∷ Φ} (γ , a) = monG ρ γ , mon ρ a

-- Reflection and reification.

mutual
  reflect : ∀{A} → Ne Γ A → ⟦ A ⟧ Γ
  reflect {A = o}     t = t
  reflect {A = _ ⇒ _} t = inj₁ t

  reify : ∀{A} → ⟦ A ⟧ Γ → Nf Γ A
  reify {A = o} t = ne t
  reify {A = B ⇒ C} a = case a of λ where
    (inj₁ t) → ne t
    (inj₂ f) → abs (reify (f (wk id) (reflect (var vz))))

-- Application and evaluation.

apply : ⟦ A ⇒ B ⟧ Γ → ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
apply c a = case c of λ where
  (inj₁ t) → reflect (app t (reify a))
  (inj₂ f) → f id a

⦅_⦆ : Tm Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ var x ⦆   γ = ⦅ x ⦆v γ
⦅ abs t ⦆   γ = inj₂ (λ ρ a → ⦅ t ⦆( monG ρ γ , a ))
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)

-- Identity environment.

env : ∀{Γ} (ρ : Δ ≤ Γ) → ⟦ Γ ⟧G Δ
env {Γ = []}    ρ = _
env {Γ = A ∷ Γ} ρ = env (wk id • ρ) , reflect (var (monVar ρ vz))

-- Normalization.

nf : Tm Γ A → Nf Γ A
nf t = reify (⦅ t ⦆ (env id))
