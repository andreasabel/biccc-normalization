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
    {t′} : Tm A Γ
    n    : Ne t′
    eq   : Eq t′ t

record NF {A Γ} (t : Tm A Γ) : Set where
  constructor mkNF
  field
    {t′} : Tm A Γ
    n    : Nf t′
    eq   : Eq t′ t

-- Constructions on NE.

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

mutual
  ⟦_⟧ : ∀ A {Γ} → Tm A Γ → Set
  ⟦ A ⟧ t = NE t ⊎ VAL A t

  VAL : ∀ A {Γ} → Tm A Γ → Set
  VAL o           t = ⊥
  VAL (B ⇒ C) {Γ} t = ∃ λ t' → Eq (abs t') t ×
    ∀{Δ} (ρ : Δ ≤ Γ) {u : Tm B Δ} (a : ⟦ B ⟧ u) → ⟦ C ⟧ (subst (sgS ρ u) t')

-- Conversion of semantics.

convVAL : Eq t t' → VAL A t → VAL A t'
convVAL {A = o}     eq ()
convVAL {A = _ ⇒ _} eq (t' , eq' ,  f) = t' , trans eq' eq , f

convDEN : Eq t t' → ⟦ A ⟧ t → ⟦ A ⟧ t'
convDEN eq (inj₁ t) = inj₁ (convNE  eq t)
convDEN eq (inj₂ f) = inj₂ (convVAL eq f)

-- Monotonicity of semantics.

mutual
  monDEN : ⟦ A ⟧ t → ⟦ A ⟧ (monTm ρ t)
  monDEN (inj₁ t) = inj₁ (monNE t)
  monDEN (inj₂ f) = inj₂ (monVAL f)

  monVAL : VAL A t → VAL A (monTm ρ t)
  monVAL {A = o} ()
  monVAL {A = A ⇒ B} {ρ = ρ} (t' , eq  , f) =
    monTm (lift ρ) t' ,  monEq eq  ,  λ ρ' a → f (ρ' • ρ) a
    -- REWRITE subst-sg-lift

-- Semantics of contexts.

data ENV : ∀{Γ Φ} → Γ ⊢ Φ → Set where
  []  : ENV {Γ} []                     -- generalization wants {Γ} here
  _∷_ : (a : ⟦ A ⟧ t) (γ : ENV σ) → ENV (t ∷ σ)

-- ENV : Γ ⊢ Φ → Set
-- ENV [] = ⊤
-- ENV (t ∷ σ) = ENV σ × ⟦ _ ⟧ t

monENV : ENV σ → ENV (monSub ρ σ)
monENV []      = []
monENV (a ∷ γ) = monDEN a ∷ monENV γ

-- Variables are projections.

lookupEnv : (x : Var A Γ) → ENV σ → ⟦ A ⟧ (lookup σ x)
lookupEnv (vz)   (a ∷ γ) = a
lookupEnv (vs x) (a ∷ γ) = lookupEnv x γ

-- lookupEnv : (x : Var A Γ) → ENV σ → ⟦ A ⟧ (lookup σ x)
-- lookupEnv {σ = t ∷ σ} (vz)   = proj₂
-- lookupEnv {σ = t ∷ σ} (vs x) = lookupEnv x ∘ proj₁

-- Reification.

mutual
  reify : ⟦ A ⟧ t → NF t
  reify (inj₁ t) = neNF t
  reify (inj₂ f) = reifyVAL f

  reifyVAL : VAL A t → NF t
  reifyVAL {A = o}     ()
  reifyVAL {A = B ⇒ C} (t' , eq , f) = convNF eq
    (absNF (reify (f (wk id) (inj₁ (mkNE (var vz) refl)))))
    -- REWRITE subst-sg-wk-vz

-- Application and evaluation.

apply : ⟦ A ⇒ B ⟧ t → ⟦ A ⟧ u → ⟦ B ⟧ (app t u)
apply (inj₁ t)            a = inj₁ (appNE t (reify a))
apply (inj₂ (_ , eq , f)) a = convDEN (eq-cong-β eq) (f id a)

⦅_⦆ : (t : Tm A Γ) → ENV σ → ⟦ A ⟧ (subst σ t)
⦅ var x ⦆   γ = lookupEnv x γ
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)
⦅ abs t ⦆   γ = inj₂ (_ , refl , λ ρ a → ⦅ t ⦆ (a ∷ monENV γ))
   -- REWRITE subst-sg-liftS

-- ⦅_⦆ : (t : Tm A Γ) (σ : Δ ⊢ Γ) → ENV σ → ⟦ A ⟧ (subst σ t)
-- ⦅ var x ⦆   σ γ = lookupEnv x γ
-- ⦅ abs t ⦆   σ γ = inj₂ ( subst (liftS σ) t , refl ,  λ ρ a →
--     ⦅ t ⦆(_ ∷ _) ( monENV γ , a )   )
-- ⦅ app t u ⦆ σ γ = apply (⦅ t ⦆ σ γ) (⦅ u ⦆ σ γ)


-- Identity environment.

-- idEnv : ENV idS  -- generalization does not kick in
idEnv : ∀{Γ} → ENV (idS {Γ = Γ})
idEnv {Γ = []}    = []
idEnv {Γ = A ∷ Γ} = inj₁ (mkNE (var vz) refl) ∷ monENV idEnv

-- Normalization.

nf : (t : Tm A Γ) → NF t
nf t = reify (Id.subst (⟦ _ ⟧) subst-idS (⦅ t ⦆ idEnv))
  -- REWRITE subst-idS  fails here

-- Completeness.

EqNE : ∀{t t' : Tm A Γ} → NE t → NE t' → Set
EqNE (mkNE {n} _ _) (mkNE {n'} _ _) = n ≡ n'

EqNF : ∀{t t' : Tm A Γ} → NF t → NF t' → Set
EqNF (mkNF {n} _ _) (mkNF {n'} _ _) = n ≡ n'

mutual
  EqDEN : ∀{t t' : Tm A Γ} → ⟦ A ⟧ t → ⟦ A ⟧ t' → Set
  EqDEN (inj₁ t) (inj₁ t') = EqNE t t'
  EqDEN (inj₁ _) (inj₂ _) = ⊥  -- no η
  EqDEN (inj₂ _) (inj₁ _) = ⊥  -- no η
  EqDEN (inj₂ f) (inj₂ f') = EqVAL f f'

  EqVAL : ∀{t t' : Tm A Γ} → VAL A t → VAL A t' → Set
  EqVAL         {A = o} _ _ = ⊤
  EqVAL {Γ = Γ} {A = A ⇒ B} (t , eq , f) (t' , eq' , f') =
    ∀ {Δ} (ρ : Δ ≤ Γ) {u : Tm A Δ} (a : ⟦ A ⟧ u) → EqDEN (f ρ a) (f' ρ a)

variable
  a a' f f' : ⟦ A ⟧ t

monEqDEN : EqDEN {A = A} a a' → EqDEN (monDEN {ρ = ρ} a) (monDEN {ρ = ρ} a')
monEqDEN                       {a = inj₁ _} {a' = inj₁ _} refl = refl
monEqDEN                       {a = inj₁ _} {a' = inj₂ _} ()
monEqDEN                       {a = inj₂ _} {a' = inj₁ _} ()
monEqDEN {A = A₁ ⇒ A₂} {ρ = ρ} {a = inj₂ _} {a' = inj₂ _} eq ρ' a = eq (ρ' • _) a

mutual
  reflDEN : (a : ⟦ A ⟧ t) → EqDEN a a
  reflDEN (inj₁ t) = refl
  reflDEN (inj₂ a) = reflVAL a

  reflVAL : (a : VAL A t) → EqVAL a a
  reflVAL {A = o} ()
  reflVAL {A = A ⇒ B} (t' , eq , f) ρ a = reflDEN (f ρ a)

-- EqENV : ∀{σ σ' : Δ ⊢ Γ} → ENV σ → ENV σ' → Set
-- EqENV {σ = []}    {σ' = []}      γ γ' = ⊤
-- EqENV {σ = u ∷ σ} {σ' = u' ∷ σ'} (γ , a) (γ' , a') = EqENV γ γ' × EqDEN a a'

variable
  γ γ' : ENV σ

-- data EqENV : ∀{Δ Γ} (σ σ' : Δ ⊢ Γ) → ENV σ → ENV σ' → Set where
--   []   : EqENV {Δ} [] [] γ γ'
--   _∷_  : EqDEN a a' → EqENV σ σ' γ γ' → EqENV (_ ∷ σ) (_ ∷ σ') (γ , a) (γ' , a')

data EqENV : ∀{Δ Γ} {σ σ' : Δ ⊢ Γ} → ENV σ → ENV σ' → Set where
  []   : EqENV {Δ} [] []
  _∷_  : (eq : EqDEN a a') (eqs : EqENV γ γ') → EqENV (a ∷ γ) (a' ∷ γ')

-- EqENV : ∀{Δ Γ} (σ σ' : Δ ⊢ Γ) → ENV σ → ENV σ' → Set where
-- EqENV {σ = []}    {σ' = []}      γ γ' = ⊤
-- EqENV {σ = u ∷ σ} {σ' = u' ∷ σ'} (γ , a) (γ' , a') = EqENV γ γ' × EqDEN a a'

monEqENV : EqENV γ γ' → EqENV (monENV {ρ = ρ} γ) (monENV {ρ = ρ} γ')
monEqENV [] = []
monEqENV (_∷_ {a = a} eq eqs) = monEqDEN {a = a} eq ∷ monEqENV eqs

-- EqENV : (σ σ' : Δ ⊢ Γ) → ENV σ → ENV σ' → Set
-- EqENV []      []        γ       γ'        = ⊤
-- EqENV (u ∷ σ) (u' ∷ σ') (γ , a) (γ' , a') = EqENV σ σ' γ γ' × EqDEN a a'

-- fund : ∀{t t' : Tm A Γ} → Eq t t' → ∀ {σ σ' : Δ ⊢ Γ} → EqENV σ σ' γ γ' → EqDEN (⦅ t ⦆ γ) ( ⦅ t' ⦆ γ')
-- fund : ∀{t t' : Tm A Γ} → Eq t t' → ∀{σ σ' : Δ ⊢ Γ}{γ : ENV σ}{γ' : ENV σ'} → EqENV σ σ' γ γ' → EqDEN (⦅ t ⦆ γ) ( ⦅ t' ⦆ γ')

applyEq : EqDEN f f' → EqDEN a a' → EqDEN (apply f a) (apply f' a')
applyEq {f = inj₁ x₁} {f' = inj₁ x₂} eq eq' = {!!}
applyEq {f = inj₁ _} {f' = inj₂ _} () eq'
applyEq {f = inj₂ _} {f' = inj₁ _} () eq'
applyEq {f = inj₂ (t , e , f)} {f' = inj₂ (t' , e' , f')} eq eq' = {!eq id !}

fund : ∀{t t' : Tm A Γ}
  → Eq t t' → ∀{σ σ' : Δ ⊢ Γ} {γ : ENV σ} {γ' : ENV σ'}
  → EqENV γ γ'
  → EqDEN (⦅ t ⦆ γ) ( ⦅ t' ⦆ γ')

fund β eqs = {!!}
fund (abs eq) eqs ρ a = fund eq (reflDEN a ∷ monEqENV eqs)
fund (app eq eq') eqs = {! applyEq (fund eq eqs) (fund eq' eqs) !}
fund refl eqs = {!!}
fund (trans eq eq₁) eqs = {!!}
fund (sym eq) eqs = {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
