-- Normalization by evaluation for the β-STLC.
-- Computes β-normal form (no η-equality).

-- Andreas Abel, 2018-10-31

{-# OPTIONS --rewriting #-}

open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_; lookup)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_$_; _∘_; case_of_)
open import Relation.Binary.PropositionalEquality as Id using (_≡_; refl; cong; cong₂)

{-# BUILTIN REWRITE _≡_ #-}

-- Types, contexts, variables.

data Ty : Set where
  o : Ty
  _⇒_ : (A B : Ty) → Ty

Cxt = List Ty

Var : Ty → Cxt → Set
Var A Γ = A ∈ Γ

pattern vz = here refl
pattern vs x = there x

variable
  Γ Δ Φ : Cxt
  A B C : Ty
  x : Var A Γ

-- Category of order-preserving embeddings (renamings).

data _≤_ : (Γ Δ : Cxt) → Set where
  id : Γ ≤ Γ
  wk : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ Δ
  lift : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ (A ∷ Δ)

Mon : (P : Cxt → Set) → Set
Mon P = ∀{Δ Γ} (ρ : Δ ≤ Γ) → P Γ → P Δ

_•_ : Mon (_≤ Φ)
id     • ρ       = ρ
wk ρ   • ρ'      = wk (ρ • ρ')
lift ρ • id      = lift ρ
lift ρ • wk ρ'   = wk (ρ • ρ')
lift ρ • lift ρ' = lift (ρ • ρ')

variable
  ρ ρ' : Δ ≤ Γ

comp-id : ρ • id ≡ ρ
comp-id {ρ = id} = refl
comp-id {ρ = wk ρ} = cong wk comp-id
comp-id {ρ = lift ρ} = refl

-- Var A is a presheaf (monotonicity).

monVar : Mon (Var A)
monVar id       x      = x
monVar (wk ρ)   x      = vs (monVar ρ x)
monVar (lift ρ) vz     = vz
monVar (lift ρ) (vs x) = vs (monVar ρ x)

monVar-comp : monVar ρ (monVar ρ' x) ≡ monVar (ρ • ρ') x
monVar-comp {x = x}    {ρ = id}     {ρ' = ρ'}      = refl
monVar-comp {x = x}    {ρ = wk ρ}   {ρ' = ρ'}      = cong vs (monVar-comp {ρ = ρ})
monVar-comp {x = x}    {ρ = lift ρ} {ρ' = id}      = refl
monVar-comp {x = x}    {ρ = lift ρ} {ρ' = wk ρ'}   = cong vs (monVar-comp {ρ = ρ})
monVar-comp {x = vz}   {ρ = lift ρ} {ρ' = lift ρ'} = refl
monVar-comp {x = vs x} {ρ = lift ρ} {ρ' = lift ρ'} = cong vs (monVar-comp {ρ = ρ})

-- Terms.

data Tm : Ty → Cxt → Set where
  var : (x : Var A Γ) → Tm A Γ
  abs : (t : Tm B (A ∷ Γ)) → Tm (A ⇒ B) Γ
  app : (t : Tm (A ⇒ B) Γ) (u : Tm A Γ) → Tm B Γ

variable
  t t' u u' v v' : Tm A Γ

monTm : Mon (Tm A)
monTm ρ (var x)   = var (monVar ρ x)
monTm ρ (abs t)   = abs (monTm (lift ρ) t)
monTm ρ (app t u) = app (monTm ρ t) (monTm ρ u)

monTm-comp : monTm ρ (monTm ρ' t) ≡ monTm (ρ • ρ') t
monTm-comp {ρ = ρ} {t = var x}   = cong  var (monVar-comp {x = x} {ρ = ρ})
monTm-comp         {t = abs t}   = cong  abs monTm-comp
monTm-comp         {t = app t u} = cong₂ app monTm-comp monTm-comp

{-# REWRITE monTm-comp #-}

-- Substitution.

_⊢_  : (Γ Δ : Cxt) → Set
Γ ⊢ Δ = All (λ A → Tm A Γ) Δ

monSub : Mon (_⊢ Φ)
monSub ρ [] = []
monSub ρ (t ∷ σ) = monTm ρ t ∷ monSub ρ σ

-- data Sub : (Φ Γ : Cxt) → Set where
--   [] : Sub [] Γ
--   _∷_ : Tm A Γ → Sub Φ Γ → Sub (A ∷ Φ) Γ

liftS : Γ ⊢ Δ → (A ∷ Γ) ⊢ (A ∷ Δ)
liftS σ = var vz ∷ monSub (wk id) σ

idS : Γ ⊢ Γ
idS {[]} = []
idS {Γ = A ∷ Γ} = liftS idS

subst : Γ ⊢ Δ → Tm A Δ → Tm A Γ
subst σ (var x)   = lookup σ x
subst σ (abs t)   = abs (subst (liftS σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)

subst1 : Tm B (A ∷ Γ) → Tm A Γ → Tm B Γ
subst1 t u = subst (u ∷ idS) t

-- Definitional equality.

data Eq : ∀{Γ A} → (t u : Tm A Γ) → Set where
  β     : Eq (app (abs t) u) (subst1 t u)
  abs   : Eq t t' → Eq (abs t) (abs t')
  app   : Eq t t' → Eq u u' → Eq (app t u) (app t' u')
  refl  : Eq t t
  trans : Eq t u → Eq u v → Eq t v
  sym   : Eq t u → Eq u t

pattern appl eq = app eq refl

monEq : Eq t u → Eq (monTm ρ t) (monTm ρ u)
monEq β              = {! β !}
monEq (abs eq)       = abs (monEq eq)
monEq (app eq eq')   = app (monEq eq) (monEq eq')
monEq refl           = refl
monEq (trans eq eq') = trans (monEq eq) (monEq eq')
monEq (sym eq)       = sym (monEq eq)

-- Neutral and non-neutral β-normal forms.

mutual
  data Ne : ∀{Γ A} → Tm Γ A → Set where
    var : (x : Var A Γ) → Ne (var x)
    app : Ne t → Nf u → Ne (app t u)

  data Nf : ∀{Γ A} → Tm Γ A → Set where
    ne  : Ne t → Nf t
    abs : Nf t → Nf (abs t)

mutual
  monNe : Ne t → Ne (monTm ρ t)
  monNe (var x)   = var (monVar _ x)
  monNe (app t u) = app (monNe t) (monNf u)

  monNf : Nf t → Nf (monTm ρ t)
  monNf (ne t)  = ne (monNe t)
  monNf (abs t) = abs (monNf t)

-- mutual
--   monNe : (ρ : Δ ≤ Γ) → Ne t → Ne (monTm ρ t)
--   monNe ρ (var x)   = var (monVar ρ x)
--   monNe ρ (app t u) = app (monNe ρ t) (monNf ρ u)

--   monNf : (ρ : Δ ≤ Γ) → Nf t → Nf (monTm ρ t)
--   monNf ρ (ne t)  = ne (monNe ρ t)
--   monNf ρ (abs t) = abs (monNf (lift ρ) t)

-- Neutral and normal up to conversion.

record NE {A Γ} (t : Tm A Γ) : Set where
  constructor mkNE
  field
    {t′} : Tm A Γ
    n    : Ne t′
    eq   : Eq t′ t

record NF {A Γ} (t : Tm A Γ) : Set where
  constructor mkNF
  field
    {t′} : Tm A Γ
    n    : Nf t′
    eq   : Eq t′ t

-- Constructions on NF.

neNF : NE t → NF t
neNF (mkNE n eq) = mkNF (ne n) eq

absNF : NF t → NF (abs t)
absNF (mkNF n eq) = mkNF (abs n) (abs eq)

-- Conversion and monotonicity.

convNE : Eq t t' → NE t → NE t'
convNE eq (mkNE n eq') = mkNE n (trans eq' eq)

convNF : Eq t t' → NF t → NF t'
convNF eq (mkNF n eq') = mkNF n (trans eq' eq)

monNE : NE t → NE (monTm ρ t)
monNE (mkNE n eq) = mkNE (monNe n) (monEq eq)

monNF : NF t → NF (monTm ρ t)
monNF (mkNF n eq) = mkNF (monNf n) (monEq eq)

-- Semantics of types and contexts.

VAL : ∀ A {Γ} → Tm A Γ → Set
VAL o           t = NE t
VAL (B ⇒ C) {Γ} t = NE t ⊎
  ∀{Δ} (ρ : Δ ≤ Γ) {u : Tm B Δ} (a : VAL B u) → VAL C (app (monTm ρ t) u)

ENV : Γ ⊢ Φ → Set
ENV [] = ⊤
ENV (t ∷ σ) = ENV σ × VAL _ t

-- Conversion of semantics.

convVAL : Eq t t' → VAL A t → VAL A t'
convVAL {A = o}     eq t        = convNE eq t
convVAL {A = _ ⇒ _} eq (inj₁ t) = inj₁ (convNE eq t)
convVAL {A = _ ⇒ _} eq (inj₂ f) = inj₂ λ ρ a → convVAL (appl (monEq eq)) (f ρ a)

-- Monotonicity of semantics.

monVAL : VAL A t → VAL A (monTm ρ t)
monVAL {o} t = monNE t
monVAL {A ⇒ B} (inj₁ t) = inj₁ (monNE t)
monVAL {A ⇒ B} {ρ = ρ} (inj₂ f) = inj₂ λ ρ' a → f (ρ' • ρ) a
  -- REWRITE monTm-comp

variable
  σ : Δ ⊢ Γ

monENV : ENV σ → ENV (monSub ρ σ)
monENV {σ = []}    _       = _
monENV {σ = t ∷ σ} (γ , v) = monENV γ , monVAL v

-- Variables are projections.

lookupEnv : (x : Var A Γ) → ENV σ → VAL A (lookup σ x)
lookupEnv {σ = t ∷ σ} (vz)   = proj₂
lookupEnv {σ = t ∷ σ} (vs x) = lookupEnv x ∘ proj₁

-- Reflection and reification.

mutual
  reflect : NE t → VAL A t
  reflect {A = o}     t = t
  reflect {A = _ ⇒ _} t = inj₁ t

  reify : VAL A t → NF t
  reify {A = o} t = neNF t
  reify {A = B ⇒ C} a = case a of λ where
    (inj₁ t) → neNF t
    (inj₂ f) → {! absNF {! (reify (f (wk id) (reflect (var vz)))) !} !}
{-
-- Application and evaluation.

apply : ⟦ A ⇒ B ⟧ Γ → ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
apply c a = case c of λ where
  (inj₁ t) → reflect (app t (reify a))
  (inj₂ f) → f id a

⦅_⦆ : Tm Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ var x ⦆ γ = ⦅ x ⦆v γ
⦅ abs t ⦆ γ = inj₂ (λ ρ a → ⦅ t ⦆( monG ρ γ , a ))
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)

-- Identity environment.

env : ∀{Γ} (ρ : Δ ≤ Γ) → ⟦ Γ ⟧G Δ
env {Γ = []}    ρ = _
env {Γ = A ∷ Γ} ρ = env (wk id • ρ) , reflect (var (monVar ρ vz))

-- Normalization.

nf : Tm Γ A → Nf Γ A
nf t = reify (⦅ t ⦆ (env id))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
