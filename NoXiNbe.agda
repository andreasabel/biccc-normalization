-- "Normalization by evaluation" for closed terms.
-- Computes weak head normal form (no ξ,η-equality).

-- Andreas Abel, 2018-11-02

-- This is inspired by
--
-- Thierry Coquand, Peter Dybjer:
-- Intuitionistic Model Constructions and Normalization Proofs.
-- Mathematical Structures in Computer Science 7(1): 75-94 (1997)
--
-- http://www.cse.chalmers.se/~peterd/papers/GlueingTypes93.pdf

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_; lookup)
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

-- Neutral and non-neutral weak head normal forms.

mutual

  data Ne Γ : Ty → Set where
    var : (x : Var Γ A) → Ne Γ A
    app : (t : Ne Γ (A ⇒ B)) (u : Nf Γ A) → Ne Γ B

  data Nf Γ : Ty → Set where
    ne  : (t : Ne Γ A) → Nf Γ A
    abs : (t : Tm (A ∷ Γ) B) → Nf Γ (A ⇒ B)   -- λxt is always a value

-- Embedding of normal forms into terms.

mutual

  tm' : Ne Γ A → Tm Γ A
  tm' (var x) = var x
  tm' (app t u) = app (tm' t) (tm u)

  tm : Nf Γ A → Tm Γ A
  tm (ne t)  = tm' t
  tm (abs t) = abs t

-- Category of order-preserving embeddings (act as renamings).

data _≤_ : (Γ Δ : Cxt) → Set where
  id   : Γ ≤ Γ
  wk   : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ Δ
  lift : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ (A ∷ Δ)

_•_ : (ρ : Γ ≤ Φ) (ρ' : Δ ≤ Γ) → Δ ≤ Φ
ρ      • id      = ρ
ρ      • wk   ρ' = wk   (ρ • ρ')
id     • ρ'      = ρ'
wk   ρ • lift ρ' = wk   (ρ • ρ')
lift ρ • lift ρ' = lift (ρ • ρ')

-- Var and Tm are presheaves (monotonicity).

monVar : (ρ : Δ ≤ Γ) → Var Γ A → Var Δ A
monVar id       x      = x
monVar (wk ρ)   x      = vs (monVar ρ x)
monVar (lift ρ) vz     = vz
monVar (lift ρ) (vs x) = vs (monVar ρ x)

monTm : (ρ : Δ ≤ Γ) → Tm Γ A → Tm Δ A
monTm ρ (var x)   = var (monVar ρ x)
monTm ρ (abs t)   = abs (monTm (lift ρ) t)
monTm ρ (app t u) = app (monTm ρ t) (monTm ρ u)

-- Substitutions.

_⊢_  : (Γ Δ : Cxt) → Set
Γ ⊢ Δ = All (Tm Γ) Δ

-- Lifting a substitution under a binder.
-- (Requires renaming.)

monSub : (ρ : Δ ≤ Γ) → Γ ⊢ Φ → Δ ⊢ Φ
monSub ρ []      = []
monSub ρ (t ∷ σ) = monTm ρ t ∷ monSub ρ σ

liftS : Γ ⊢ Δ → (A ∷ Γ) ⊢ (A ∷ Δ)
liftS σ = var vz ∷ monSub (wk id) σ

-- Substitution into terms.

subst : Γ ⊢ Δ → Tm Δ A → Tm Γ A
subst σ (var x)   = lookup σ x
subst σ (abs t)   = abs (subst (liftS σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)

-- Semantics of types.
--
-- Values are pairs of normal forms (code) and denotation (function).

mutual
  ⟦_⟧_ : Ty → Cxt → Set
  ⟦ A ⟧ Γ = Nf Γ A × Sem A Γ

  Sem : Ty → Cxt → Set
  Sem o       Γ = ⊤
  Sem (A ⇒ B) Γ = ⟦ A ⟧ Γ → ⟦ B ⟧ Γ

-- Since we do go under binders during reification, we do not need
-- a Kripke function space here.

-- Semantics of contexts.
--
-- Environments are lists of values.

⟦_⟧G : (Γ Δ : Cxt) → Set
⟦ Γ ⟧G Δ = All (⟦_⟧ Δ) Γ

-- Reification of values (first projection).

reify : ∀{A} → ⟦ A ⟧ Γ → Nf Γ A
reify (t , _) = t

-- Application of values (second projection).

apply : ⟦ A ⇒ B ⟧ Γ → ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
apply (_ , f) a = f a

-- Reification of environments into substitutions (pointwise).

reifyS : ⟦ Γ ⟧G Δ → Δ ⊢ Γ
reifyS []      = []
reifyS (a ∷ γ) = tm (reify a) ∷ reifyS γ

-- Evaluation of terms to values (in an environment).

⦅_⦆ : Tm Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ var x ⦆   γ = lookup γ x
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)
⦅ abs t ⦆   γ = abs (subst (liftS (reifyS γ)) t) , λ a → ⦅ t ⦆(a ∷ γ)

-- The value of an abstraction (abs t) consists of a weak head normal form
-- and a function.  We obtain the function as usual by evaluating the
-- abstraction body once we get a value for the arguments.
--
-- For the weak head normal form, we have (t : Tm (A ∷ Γ) B) but need
-- a body in Tm (A ∷ Δ) B.  This can be obtained by substituting
-- with the whnf contained in the environment (γ : ⟦ Γ ⟧G Δ), which we
-- can reify to a substitution Δ ⊢ Γ.

-- Reflection of neutrals as values.

mutual
  reflect : Ne Γ A → ⟦ A ⟧ Γ
  reflect t = ne t , reflect' t

  reflect' : Ne Γ A → Sem A Γ
  reflect' {A = o}         = _
  reflect' {A = A ⇒ B} t a = reflect (app t (reify a))

-- Identity environment mapping variables to their reflection.

env : ∀{Γ} (ρ : Δ ≤ Γ) → ⟦ Γ ⟧G Δ
env {Γ = []}    ρ = []
env {Γ = A ∷ Γ} ρ = reflect (var (monVar ρ vz)) ∷ env (wk id • ρ)

-- Normalization by evaluation.

nf : Tm Γ A → Nf Γ A
nf t = reify (⦅ t ⦆ (env id))

-- Examples.

I : Tm Γ (A ⇒ A)
I = abs (var vz)

K : Tm Γ (A ⇒ (B ⇒ A))
K = abs (abs (var (vs vz)))

S : Tm Γ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
S = abs (abs (abs (app (app (var (vs (vs vz))) (var vz)) (app (var (vs vz)) (var vz)))))

SKK : Tm Γ (A ⇒ A)
SKK {A = A} = app (app S K) (K {B = A})

nfSKK : Nf [] (A ⇒ A)
nfSKK = nf SKK  -- abs (app (app K (var vz)) (app K (var vz)))

SKKI : Tm Γ (A ⇒ A)
SKKI = app SKK I

nfSKKI : Nf [] (A ⇒ A)
nfSKKI = nf SKKI  -- I

SKKx : Tm (A ∷ Γ) A
SKKx = app SKK (var vz)

nfSKKx : Nf (o ∷ Γ) o
nfSKKx = nf SKKx  -- ne (var vz)

nfSKKx1 : Nf ((A ⇒ B) ∷ Γ) (A ⇒ B)
nfSKKx1 = nf SKKx  -- ne (var vz)

SKxy : Tm ((A ⇒ B) ∷ A ∷ Γ) A
SKxy = app (app (app S K) (var vz)) (var (vs vz))  -- nf: ne (var (vs vz))
