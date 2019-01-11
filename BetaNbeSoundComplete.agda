-- Normalization by evaluation for the β-STLC.
-- Computes β-normal form (no η-equality).

-- Andreas Abel, 2018-10-31

{-# OPTIONS --rewriting #-}

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.All using (All; []; _∷_; lookup)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)

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
monVar-comp {ρ = id}     {ρ' = ρ'}      {x = x}    = refl
monVar-comp {ρ = wk ρ}   {ρ' = ρ'}      {x = x}    = cong vs (monVar-comp {ρ = ρ})
monVar-comp {ρ = lift ρ} {ρ' = id}      {x = x}    = refl
monVar-comp {ρ = lift ρ} {ρ' = wk ρ'}   {x = x}    = cong vs (monVar-comp {ρ = ρ})
monVar-comp {ρ = lift ρ} {ρ' = lift ρ'} {x = vz}   = refl
monVar-comp {ρ = lift ρ} {ρ' = lift ρ'} {x = vs x} = cong vs (monVar-comp {ρ = ρ})

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
monTm-comp {ρ = ρ} {t = var x}   = cong  var (monVar-comp {ρ = ρ} {x = x})
monTm-comp         {t = abs t}   = cong  abs monTm-comp
monTm-comp         {t = app t u} = cong₂ app monTm-comp monTm-comp

-- {-# REWRITE monTm-comp #-}

-- Substitution.

_⊢_  : (Γ Δ : Cxt) → Set
Γ ⊢ Δ = All (λ A → Tm A Γ) Δ

monSub : Mon (_⊢ Φ)
monSub ρ [] = []
monSub ρ (t ∷ σ) = monTm ρ t ∷ monSub ρ σ

-- Naturality of lookup.

lookup-mon : ∀ σ → lookup (monSub ρ σ) x ≡ monTm ρ (lookup σ x)
lookup-mon {x = vz}   (u ∷ σ) = refl
lookup-mon {x = vs x} (u ∷ σ) = lookup-mon σ

-- Constructions on substitutions.

liftS : Γ ⊢ Δ → (A ∷ Γ) ⊢ (A ∷ Δ)
liftS σ = var vz ∷ monSub (wk id) σ

idS : Γ ⊢ Γ
idS {[]} = []
idS {Γ = A ∷ Γ} = liftS idS

renS : (ρ : Γ ≤ Δ) → Γ ⊢ Δ
renS id       = idS
renS (wk   ρ) = monSub (wk id) (renS ρ)
renS (lift ρ) = liftS (renS ρ)

sgS : (ρ : Γ ≤ Δ) (u : Tm A Γ) → Γ ⊢ (A ∷ Δ)
sgS ρ u = u ∷ renS ρ

subst : Γ ⊢ Δ → Tm A Δ → Tm A Γ
subst σ (var x)   = lookup σ x
subst σ (abs t)   = abs (subst (liftS σ) t)
subst σ (app t u) = app (subst σ t) (subst σ u)

-- Substitution composition.  \ .

_∙_ : Δ ⊢ Γ → Γ ⊢ Φ → Δ ⊢ Φ
σ ∙ []       = []
σ ∙ (u ∷ σ') = subst σ u ∷ (σ ∙ σ')


-- Functoriality of substitution.

-- subst σ (subst σ' t) ≡ subst (σ ∙ σ') t

subst1 : Tm B (A ∷ Γ) → Tm A Γ → Tm B Γ
subst1 t u = subst (u ∷ idS) t

subst-sg-lift : subst (sgS ρ u) (monTm (lift ρ') t) ≡ subst (sgS (ρ • ρ') u) t
subst-sg-lift = {!!}

{-# REWRITE subst-sg-lift #-}

variable
  σ σ' : Δ ⊢ Γ

subst-sg-liftS : subst (sgS ρ u) (subst (liftS σ) t) ≡ subst (u ∷ monSub ρ σ) t
subst-sg-liftS = {!!}
-- subst-sg-liftS {t = var vz} = refl
-- subst-sg-liftS {t = var (vs x)} = {!!}
-- subst-sg-liftS {t = abs t} = cong abs {!!}
-- subst-sg-liftS {t = app t u} = {!!}


{-# REWRITE subst-sg-liftS #-}

-- Identity substitution

lookup-idS : lookup idS x ≡ var x
lookup-idS {x = vz}   = refl
lookup-idS {x = vs x} = Id.trans
  (lookup-mon idS)
  (cong (monTm (wk id)) (lookup-idS {x = x}))

subst-idS : subst idS t ≡ t
subst-idS {t = var x} = lookup-idS
subst-idS {t = abs t} = cong abs subst-idS
subst-idS {t = app t u} = cong₂ app subst-idS subst-idS

-- {-# REWRITE subst-idS #-}

subst-sg-wk-vz : subst (sgS (wk id) (var vz)) t ≡ t
subst-sg-wk-vz = subst-idS

{-# REWRITE subst-sg-wk-vz #-}


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

eq-cong-β : Eq (abs t) t' → Eq (subst1 t u) (app t' u)
eq-cong-β eq = trans (sym β) (appl eq)

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
    {tm} : Tm A Γ
    isNe : Ne tm
    eq   : Eq tm t

record NF {A Γ} (t : Tm A Γ) : Set where
  constructor mkNF
  field
    {tm} : Tm A Γ
    isNf : Nf tm
    eq   : Eq tm t

-- Equality on NE and NF

EqNE : ∀{t t' : Tm A Γ} → NE t → NE t' → Set
EqNE n n' = NE.tm n ≡ NE.tm n'

EqNF : ∀{t t' : Tm A Γ} → NF t → NF t' → Set
EqNF n n' = NF.tm n ≡ NF.tm n'

-- Constructions on NE.

vzNE : NE (var {Γ = A ∷ Γ} vz)
vzNE = mkNE (var vz) refl

appNE : NE t → NF u → NE (app t u)
appNE (mkNE n eq) (mkNF m eq') = mkNE (app n m) (app eq eq')

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

-- Semantics of types.

Cand : Ty → Set₁
Cand A = ∀{Γ} → Tm A Γ → Set

CandEq : ∀{A} (⟦A⟧ : Cand A) → Set₁
CandEq {A} ⟦A⟧ = ∀{Γ} {t t' : Tm A Γ} → ⟦A⟧ t → ⟦A⟧ t' → Set

-- To work around restrictions of the positivity checker,
-- we defined a general version of LAM here,
-- rather than one specialized to A and B local to VAL.

record LAM {A B} (⟦A⟧ : Cand A) (⟦B⟧ : Cand B) (Eq⟦A⟧ : CandEq ⟦A⟧) (Eq⟦B⟧ : CandEq ⟦B⟧)
  {Γ} (t : Tm (A ⇒ B) Γ) : Set where
  constructor lam
  field
    {tm}  : Tm B (A ∷ Γ)
    eq    : Eq (abs tm) t
    fun   : ∀{Δ} (ρ : Δ ≤ Γ) {u : Tm A Δ} (a : ⟦A⟧ u) → ⟦B⟧ (subst (sgS ρ u) tm)
    fcong : ∀{Δ} (ρ : Δ ≤ Γ) {u u' : Tm A Δ} (a : ⟦A⟧ u) (a' : ⟦A⟧ u')
       → Eq⟦A⟧ a a'
       → Eq⟦B⟧ (fun ρ a) (fun ρ a')

mutual
  ⟦_⟧ : ∀ A {Γ} → Tm A Γ → Set
  ⟦ A ⟧ t = NE t ⊎ VAL A t

  VAL : ∀ A {Γ} → Tm A Γ → Set
  VAL o           t = ⊥
  VAL (A ⇒ B) {Γ} t = LAM ⟦ A ⟧ ⟦ B ⟧ EqDEN EqDEN t

  EqDEN : ∀{t t' : Tm A Γ} → ⟦ A ⟧ t → ⟦ A ⟧ t' → Set
  EqDEN (inj₁ t) (inj₁ t') = EqNE t t'
  EqDEN (inj₁ _) (inj₂ _) = ⊥  -- no η
  EqDEN (inj₂ _) (inj₁ _) = ⊥  -- no η
  EqDEN (inj₂ f) (inj₂ f') = EqVAL f f'

  EqVAL : ∀{t t' : Tm A Γ} → VAL A t → VAL A t' → Set
  EqVAL {A = o}             _ _ = ⊤
  EqVAL {A = A ⇒ B} {Γ = Γ} (lam _ f _) (lam _ f' _) =
    ∀ {Δ} (ρ : Δ ≤ Γ) {u : Tm A Δ} (a : ⟦ A ⟧ u) → EqDEN (f ρ a) (f' ρ a)

-- Conversion of semantics.

convVAL : Eq t t' → VAL A t → VAL A t'
convVAL {A = o}     eq ()
convVAL {A = _ ⇒ _} eq (lam eq' f fcong) = lam (trans eq' eq) f fcong

convDEN : Eq t t' → ⟦ A ⟧ t → ⟦ A ⟧ t'
convDEN eq (inj₁ t) = inj₁ (convNE  eq t)
convDEN eq (inj₂ f) = inj₂ (convVAL eq f)

variable
  a a' b c f f' : ⟦ A ⟧ t
  eqt eqt' : Eq t t'

convEqDEN : EqDEN {A = A} a a' → EqDEN (convDEN eqt a) (convDEN eqt' a')
convEqDEN {a = inj₁ _} {a' = inj₁ _} refl = refl
convEqDEN {A = A ⇒ B} {a = inj₂ (lam e f fcong)} {a' = inj₂ (lam e' f' fcong')} f=f' ρ a =
  f=f' ρ a

-- Monotonicity of semantics.

mutual
  monDEN : ⟦ A ⟧ t → ⟦ A ⟧ (monTm ρ t)
  monDEN (inj₁ t) = inj₁ (monNE t)
  monDEN (inj₂ f) = inj₂ (monVAL f)

  monVAL : VAL A t → VAL A (monTm ρ t)
  monVAL {A = o} ()
  monVAL {A = A ⇒ B} {ρ = ρ} (lam {tm = t'} eq f fcong) =
    lam {tm = monTm (lift ρ) t'}
        (monEq eq)
        (λ ρ' a → f (ρ' • ρ) a)
        λ ρ' a a' a=a' → fcong (ρ' • ρ) a a' a=a'
    -- REWRITE subst-sg-lift

-- Monotonicity of equality.

monEqDEN : EqDEN {A = A} a a' → EqDEN (monDEN {ρ = ρ} a) (monDEN {ρ = ρ} a')
monEqDEN               {a = inj₁ _} {a' = inj₁ _} refl = refl
monEqDEN               {a = inj₁ _} {a' = inj₂ _} ()
monEqDEN               {a = inj₂ _} {a' = inj₁ _} ()
monEqDEN {A = A₁ ⇒ A₂} {a = inj₂ _} {a' = inj₂ _} eq ρ' a = eq (ρ' • _) a

-- Reflexivity of semantic equality.

mutual
  reflDEN : (a : ⟦ A ⟧ t) → EqDEN a a
  reflDEN (inj₁ t) = refl
  reflDEN (inj₂ a) = reflVAL a

  reflVAL : (a : VAL A t) → EqVAL a a
  reflVAL {A = o} ()
  reflVAL {A = A ⇒ B} (lam eq f fcong) ρ a = reflDEN (f ρ a)
  -- ALT:
  -- reflVAL {A = A ⇒ B} (lam eq f fcong) ρ a = fcong ρ a a (reflDEN a)

-- Symmetry of semantic equality.

symDEN : EqDEN {A = A} a b → EqDEN b a
symDEN {a = inj₁ _} {b = inj₁ _} refl = refl
symDEN {A = A ⇒ B} {a = inj₂ (lam _ f _)} {b = inj₂ (lam _ f' _)} f=f' ρ a =
  symDEN {a = f ρ a} (f=f' ρ a)

-- Transitivity of semantic equality.

-- TODO: make a visible!?
transDEN : EqDEN {A = A} a b → EqDEN b c → EqDEN a c

transDEN {a = inj₁ t₁} {b = inj₁ t₂} {c = inj₁ t₃} refl refl = refl
transDEN {A = A ⇒ B} {a = inj₂ (lam _ f fcong)} {b = inj₂ (lam _ g gcong)} {c = inj₂ (lam _ h hcong)} f=g g=h ρ a = transDEN {a = f ρ a} (f=g ρ a) (g=h ρ a)

-- impossible cases:
transDEN {A = o} {a = inj₂ ()}
transDEN {a = inj₁ _} {b = inj₁ _} {c = inj₂ _} a=b ()
transDEN {a = inj₁ _} {b = inj₂ _} {c = inj₁ _} ()
transDEN {a = inj₁ _} {b = inj₂ _} {c = inj₂ _} ()
transDEN {a = inj₂ _} {b = inj₁ _} {c = inj₁ _} ()
transDEN {a = inj₂ _} {b = inj₁ _} {c = inj₂ _} ()
transDEN {a = inj₂ _} {b = inj₂ _} {c = inj₁ _} a=b ()

-- Semantics of contexts.

data ENV : ∀{Γ Φ} → Γ ⊢ Φ → Set where
  []  : ENV {Γ} []                     -- generalization wants {Γ} here
  _∷_ : (a : ⟦ A ⟧ t) (γ : ENV σ) → ENV (t ∷ σ)

monENV : ENV σ → ENV (monSub ρ σ)
monENV []      = []
monENV (a ∷ γ) = monDEN a ∷ monENV γ

-- Equality of environments.

variable
  γ γ' : ENV σ

data EqENV : ∀{Δ Γ} {σ σ' : Δ ⊢ Γ} → ENV σ → ENV σ' → Set where
  []   : EqENV {Δ} [] []
  _∷_  : (eq : EqDEN a a') (eqs : EqENV γ γ') → EqENV (a ∷ γ) (a' ∷ γ')

monEqENV : EqENV γ γ' → EqENV (monENV {ρ = ρ} γ) (monENV {ρ = ρ} γ')
monEqENV [] = []
monEqENV (_∷_ {a = a} eq eqs) = monEqDEN {a = a} eq ∷ monEqENV eqs

reflEqENV : (γ : ENV σ) → EqENV γ γ
reflEqENV [] = []
reflEqENV (a ∷ γ) = reflDEN a ∷ reflEqENV γ

symEqENV : EqENV γ γ' → EqENV γ' γ
symEqENV [] = []
symEqENV (_∷_ {a = a} eq eqs) = symDEN {a = a} eq ∷ symEqENV eqs

-- lreflENV : EqENV γ γ' → EqENV γ γ

-- Variables are projections from the environment.

lookupEnv : (x : Var A Γ) → ENV σ → ⟦ A ⟧ (lookup σ x)
lookupEnv (vz)   (a ∷ γ) = a
lookupEnv (vs x) (a ∷ γ) = lookupEnv x γ

lookupEqEnv : (x : Var A Γ) → EqENV γ γ' → EqDEN (lookupEnv x γ) (lookupEnv x γ')
lookupEqEnv (vz)   (eq ∷ eqs) = eq
lookupEqEnv (vs x) (eq ∷ eqs) = lookupEqEnv x eqs

-- Reification.

mutual
  reify : ⟦ A ⟧ t → NF t
  reify (inj₁ t) = neNF t
  reify (inj₂ f) = reifyVAL f

  reifyVAL : VAL A t → NF t
  reifyVAL {A = o}     ()
  reifyVAL {A = B ⇒ C} (lam eq f _) = convNF eq (absNF (reify (f (wk id) (inj₁ vzNE))))
    -- REWRITE subst-sg-wk-vz

-- Reification preserves equality.
-- TODO: make a visible (and maybe a' too)

reifyEq : EqDEN {A = A} a a' → EqNF (reify a) (reify a')
reifyEq         {a = inj₁ _} {a' = inj₁ _} refl = refl
reifyEq {A = o} {a = inj₂ ()}
reifyEq {A = A ⇒ B} {a = inj₂ (lam _ f _)} {a' = inj₂ (lam _ f' _)} f=f' =
  cong abs (reifyEq {a = f (wk id) (inj₁ vzNE)} (f=f' (wk id) (inj₁ vzNE)))

-- Application.

apply : ⟦ A ⇒ B ⟧ t → ⟦ A ⟧ u → ⟦ B ⟧ (app t u)

apply (inj₁ t)            a = inj₁ (appNE t (reify a))
apply (inj₂ (lam eq f _)) a = convDEN (eq-cong-β eq) (f id a)

-- Application preserves semantic equality.

applyEq : EqDEN f f' → EqDEN a a' → EqDEN (apply f a) (apply f' a')

applyEq {a = a} {f = inj₁ t} {f' = inj₁ t'} t=t' a=a' =
  cong₂ app t=t' (reifyEq {a = a} a=a')

applyEq {a = a} {f = inj₂ (lam e f fcong)} {f' = inj₂ (lam e' f' fcong')} f=f' a=a' =
  convEqDEN {a = f id a} (transDEN {a = f id a} (f=f' id a) (fcong' id a _ a=a'))

-- Evaluation and functoriality.

mutual

  ⦅_⦆ : (t : Tm A Γ) → ENV σ → ⟦ A ⟧ (subst σ t)
  ⦅ var x ⦆   γ = lookupEnv x γ
  ⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)
  ⦅ abs t ⦆   γ = inj₂ (lam refl
     (λ ρ a → ⦅ t ⦆ (a ∷ monENV γ))
     (λ ρ a a' a=a' → func t (a=a' ∷ reflEqENV (monENV γ))))
     -- REWRITE subst-sg-liftS

  -- Denotation is a semantic morphism (preserves equality).

  func : ∀ (t : Tm A Γ) {σ σ' : Δ ⊢ Γ} {γ : ENV σ} {γ' : ENV σ'}
    → EqENV γ γ'
    → EqDEN (⦅ t ⦆ γ) ( ⦅ t ⦆ γ')
  func (var x) eqs = lookupEqEnv x eqs
  func (app t u) eqs = applyEq {f = ⦅ t ⦆ _} (func t eqs) (func u eqs)
  func (abs t) eqs ρ a = func t (reflDEN a ∷ monEqENV eqs)

-- Identity environment.

-- idEnv : ENV idS  -- generalization does not kick in
idEnv : ∀{Γ} → ENV (idS {Γ = Γ})
idEnv {Γ = []}    = []
idEnv {Γ = A ∷ Γ} = inj₁ (mkNE (var vz) refl) ∷ monENV idEnv

-- Normalization.

nf : (t : Tm A Γ) → NF t
nf t = reify (Id.subst (⟦ _ ⟧) subst-idS (⦅ t ⦆ idEnv))
  -- REWRITE subst-idS  fails here

-- Evaluation of renamings.

monSub-id : monSub id σ ≡ σ
monSub-id = {!!}

-- {-# REWRITE monSub-id #-}

-- Evaluation of substitutions.

evalS : (σ : Δ ⊢ Γ) (γ : ENV σ') → ENV (σ' ∙ σ)
evalS []      γ = []
evalS (u ∷ σ) γ = ⦅ u ⦆ γ ∷ evalS σ γ

-- TODO: define this natively!
evalR : (ρ : Δ ≤ Γ) (γ : ENV σ) → ENV (σ ∙ renS ρ)
evalR ρ γ = evalS (renS ρ) γ

-- evalR-id : evalR id γ ≡ γ
-- evalR-id = ?

evalR-wk : EqENV (evalR (wk ρ) (a ∷ γ)) (evalR ρ γ)
evalR-wk = {!!}

-- Substitution lemma.

lookupEnv-mon : EqDEN (lookupEnv (monVar ρ x) γ) (lookupEnv x (evalR ρ γ))
lookupEnv-mon {ρ = id}                {γ = a ∷ γ} = {! reflDEN a !}
lookupEnv-mon {ρ = wk ρ}              {γ = a ∷ γ} = {!!}
lookupEnv-mon {ρ = lift ρ} {x = vz}   {γ = a ∷ γ} = reflDEN a
lookupEnv-mon {ρ = lift ρ} {x = vs x} {γ = a ∷ γ} = {!!}

eval-mon : EqDEN (⦅ monTm ρ t ⦆ γ) (⦅  t ⦆ (evalR ρ γ))
eval-mon {t = var x} = {!!}
eval-mon {t = abs t} = {!!}
eval-mon {t = app t u} = {!!}

-- TODO: this does not go through
-- Rather generalize to arbitrary renamings.
eval-wk : EqDEN (⦅ monTm (wk id) t ⦆ (a ∷ γ)) (⦅  t ⦆ γ)
eval-wk {t = var x}   = reflDEN (lookupEnv x _)
eval-wk {t = abs t}   ρ a = {!!}
eval-wk {t = app t u} = applyEq {f = ⦅ monTm (wk id) t ⦆ _}
   (eval-wk {t = t})
   (eval-wk {t = u})

evalS-wk : EqENV (evalS (monSub (wk id) σ) (a ∷ γ)) (evalS σ γ)
evalS-wk {σ = []} = []
evalS-wk {σ = u ∷ σ} = {!!} ∷ evalS-wk {σ = σ}

evalS-wk-mon : EqENV (monENV {ρ = ρ} (evalS σ γ)) (evalS (monSub (wk id) σ) (a ∷ monENV {ρ = ρ} γ))
evalS-wk-mon {σ = []} = []
evalS-wk-mon {σ = u ∷ σ} = {!!} ∷ {!!}

--       (⦅ t ⦆ (a ∷ monENV (evalS σ γ)))
--       (⦅ t ⦆ (a ∷ evalS (monSub (wk id) σ) (a ∷ monENV γ)))

substLem' : EqDEN (⦅ lookup σ x ⦆ γ) (lookupEnv x (evalS σ γ))
substLem' {σ = u ∷ σ} {x = vz}   = reflDEN (⦅ u ⦆ _)
substLem' {σ = u ∷ σ} {x = vs x} = substLem' {σ = σ} {x = x}

substLem : EqDEN (⦅ subst σ t ⦆ γ) (⦅ t ⦆(evalS σ γ))
substLem {σ = σ} {t = var x} = substLem' {σ = σ} {x = x}
substLem {σ = σ} {t = abs t} {γ = γ} ρ {u} a  = {!  (substLem {t = t} {σ = liftS σ} {γ = a ∷ monENV γ}) !}
-- Goal: EqDEN (⦅ subst (liftS σ) t ⦆ (a ∷ monENV γ))
--       (⦅ t ⦆ (a ∷ monENV (evalS σ γ)))
-- Have: EqDEN (⦅ subst (liftS σ) t ⦆ (a ∷ monENV γ))
--       (⦅ t ⦆ (a ∷ evalS (monSub (wk id) σ) (a ∷ monENV γ)))

substLem {σ = σ} {t = app t u} =
  applyEq {a = ⦅  subst σ u  ⦆ _} {f = ⦅  subst σ t ⦆ _ } {f' = ⦅ t ⦆ _}
   (substLem {σ = σ} {t = t})
   (substLem {σ = σ} {t = u})

-- Completeness.

fund : ∀{t t' : Tm A Γ}
  → Eq t t' → ∀{σ σ' : Δ ⊢ Γ} {γ : ENV σ} {γ' : ENV σ'}
  → EqENV γ γ'
  → EqDEN (⦅ t ⦆ γ) ( ⦅ t' ⦆ γ')

fund β                       eqs = {!!}
fund (abs eq)                eqs ρ a = fund eq (reflDEN a ∷ monEqENV eqs)
fund (app {t = t} eq eq')    eqs = applyEq {f = ⦅ t ⦆ _} (fund eq eqs) (fund eq' eqs)
fund (refl {t = t})          eqs = func t eqs
fund (trans {t = t} t=u u=v) eqs = transDEN {a = ⦅ t ⦆ _}
  (fund t=u (reflEqENV _))
  (fund u=v                  eqs)
fund (sym {t = t} eq)        eqs = symDEN {a = ⦅ t ⦆ _} (fund eq (symEqENV eqs))

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
