open import Data.List using (List; []; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Ty : Set where
  o : Ty
  _⇒_ : (A B : Ty) → Ty

Cxt = List Ty

Var : Cxt → Ty → Set
Var Γ A = A ∈ Γ

variable
  Γ Δ : Cxt
  A B C : Ty

data Tm (Γ : Cxt) : Ty → Set where
  var : (x : Var Γ A) → Tm Γ A
  abs : (t : Tm (A ∷ Γ) B) → Tm Γ (A ⇒ B)
  app : (t : Tm Γ (A ⇒ B)) (u : Tm Γ A) → Tm Γ B

mutual
  data Ne Γ : Ty → Set where
    var : (x : Var Γ A) → Ne Γ A
    app : (t : Ne Γ (A ⇒ B)) (u : Nf Γ A) → Ne Γ B

  data Nf Γ : Ty → Set where
    ne : (t : Ne Γ A) → Nf Γ A
    abs : (t : Nf (A ∷ Γ) B) → Nf Γ (A ⇒ B)

data _≤_ : (Γ Δ : Cxt) → Set where
  id : Γ ≤ Γ
  wk : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ Δ
  lift : (ρ : Γ ≤ Δ) → (A ∷ Γ) ≤ (A ∷ Δ)

⟦_⟧ : Ty → Cxt → Set
⟦ o     ⟧ Γ = ∀{Δ} (ρ : Δ ≤ Γ) → Ne Δ o
⟦ A ⇒ B ⟧ Γ = ∀{Δ} (ρ : Δ ≤ Γ) → Ne Δ (A ⇒ B) ⊎ (⟦ A ⟧ Δ → ⟦ B ⟧ Δ)

⟦_⟧G : (Φ Γ : Cxt) → Set
⟦ [] ⟧G Γ = ⊤
⟦ A ∷ Φ ⟧G Γ = ⟦ Φ ⟧G Γ × ⟦ A ⟧ Γ

monNe : (ρ : Δ ≤ Γ) → Ne Γ A → Ne Δ A
monNe ρ t = {!!}

mon : (ρ : Δ ≤ Γ) → ∀{A} → ⟦ A ⟧ Γ → ⟦ A ⟧ Δ
mon ρ {o} a ρ' = {!!}
mon ρ {A ⇒ B} a ρ' = {!!}

monG : (ρ : Δ ≤ Γ) → ∀{Φ} → ⟦ Φ ⟧G Γ → ⟦ Φ ⟧G Δ
monG ρ {[]} _ = _
monG ρ {A ∷ Φ} (γ , a) = monG ρ γ , mon ρ a

mutual
  reflect : ∀{A} → Ne Γ A → ⟦ A ⟧ Γ
  reflect {A = o}     t ρ = monNe ρ t
  reflect {A = _ ⇒ _} t ρ = inj₁ (monNe ρ t)

  reify : ∀{A} → ⟦ A ⟧ Γ → Nf Γ A
  reify {A = o} f = ne (f id)
  reify {A = B ⇒ C} f = abs {!case f id!}

apply : ⟦ A ⇒ B ⟧ Γ → ⟦ A ⟧ Γ → ⟦ B ⟧ Γ
apply c a = case c id of λ where
  (inj₁ t) → {!reflect (app t (reify a))!}
  (inj₂ f) → f a

⦅_⦆v : Var Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ here refl ⦆v = proj₂
⦅ there x ⦆v = ⦅ x ⦆v ∘ proj₁

⦅_⦆ : Tm Γ A → ⟦ Γ ⟧G Δ → ⟦ A ⟧ Δ
⦅ var x ⦆ γ = ⦅ x ⦆v γ
⦅ abs t ⦆ γ ρ = inj₂ (λ a → ⦅ t ⦆( monG ρ γ , a ))
⦅ app t u ⦆ γ = apply (⦅ t ⦆ γ) (⦅ u ⦆ γ)
