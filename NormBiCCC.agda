data Ty : Set where
  _×_ _+_ _⇒_ : (A B : Ty) → Ty
  ⊥ ⊤ : Ty
  base : Ty

variable
  A B C D Γ : Ty

mutual
  -- Eliminations to be used on the left (as "function").
  -- Associate to the right.
  -- (On the right, they act as dominant substitutions: compE).
  data Elim : (A B : Ty) → Set where
    pi1 : Nf A C → Elim (A × B) C  -- f ∘ π₁
    pi2 : Nf B C → Elim (A × B) C
    eval : Nf B C → Elim ((A ⇒ B) × A) C  -- f ∘ eval
    copair : Nf A C → Nf B C → Elim (A + B) C
    abort : Elim ⊥ C   -- Since f ∘ abort = abort

  -- Entry Γ C A  is  Hom(Γ,A) → Hom(Γ,C)
  data Entry Γ C : Ty → Set where
    apply  : (h : Nf Γ A) → Entry Γ C (A ⇒ C)  -- eval ∘ ⟨□,h⟩
    pi1    : Entry Γ C (C × B) -- π₁ ∘ □
    pi2    : Entry Γ C (A × C) -- π₂ ∘ □
    copair : (f : Nf A C) (g : Nf B C) → Entry Γ C (A + B) -- [f,g] ∘ □
    abort  : Entry Γ C ⊥   -- abort ∘ □

  -- Spine Γ A C  is  Hom(Γ,A) → Hom(Γ,C)
  data Spine Γ A : Ty → Set where
    [] : Spine Γ A A
    _∷_ : Entry Γ B A → Spine Γ B C → Spine Γ A C

  -- Values, to be eliminated on the right (as "argument")
  -- (On the left, they stay values, as values are closed under substitution: compV).
  data Val : (A B : Ty) → Set where
    in1 : Nf A B → Val A (B + C)  -- in₁ ∘ f
    in2 : Nf A C → Val A (B + C)
    pair : Nf C A → Nf C B → Val C (A × B)
    curry : Nf (C × A) B → Val C (A ⇒ B)
    unit  : Val C ⊤

  data Nf : (A B : Ty) → Set where
    id   : Nf A A
    elim : Elim A B → Nf A B
    val  : Val A B → Nf A B
    sp   : (s : Spine A A C) → Nf A C  -- s [id / □]

cross : Nf A B → Nf C D → Nf (A × C) (B × D)
cross f g = val (pair (elim (pi1 f)) (elim (pi2 g)))

snoc : Spine Γ A B → Entry Γ C B → Spine Γ A C
snoc [] e = e ∷ []
snoc (d ∷ s) e = d ∷ snoc s e

_++_ : Spine Γ A B → Spine Γ B C → Spine Γ A C
[] ++ s = s
(e ∷ s) ++ s' = e ∷ (s ++ s')

mutual
  compV : Val B C → Nf A B → Val A C
  compV (in1 f)    k = in1 (comp f k)
  compV (in2 f)    k = in2 (comp f k)
  compV (pair f g) k = pair (comp f k) (comp g k)
  compV (curry f)  k = curry (comp f (cross k id))
  compV unit       k = unit

  compE : Nf B C → Elim A B → Elim A C
  compE f (pi1 e)      = pi1 (comp f e)
  compE f (pi2 e)      = pi2 (comp f e)
  compE f (eval e)     = eval (comp f e)
  compE f (copair g h) = copair (comp f g) (comp f h)
  compE f abort        = abort

  -- Critical pair:
  -- comp (val v) (elim e) = compE (val v) e
  -- comp (val v) (elim e) = compV v (elim e)

  comp : Nf B C → Nf A B → Nf A C
  comp id      r = r
  comp (val v) r = val (compV v r)
  comp l id = l
  comp l (elim e) = elim (compE l e)
  comp (elim e) (val v) = beta e v
  comp (sp s) r = {!plug s r !}
  comp (sp s) (sp s') = sp {!s ++ s'!}

  eliminate : Entry A C B → Val A B → Nf A C
  eliminate (apply h) (curry f) = comp f (val (pair id h))
  eliminate pi1 (pair f g) = f
  eliminate pi2 (pair f g) = g
  eliminate (copair f g) (in1 h) = comp f h
  eliminate (copair f g) (in2 h) = comp g h
  eliminate abort ()

  -- eliminate : Val A B → Entry A C B → Nf A C
  -- eliminate (in1 h) (copair f g) = comp f h
  -- eliminate (in2 h) (copair f g) = comp g h
  -- eliminate (pair f g) pi1 = f
  -- eliminate (pair f g) pi2 = g
  -- eliminate (curry f) (apply h) = {!!}
  -- eliminate unit ()

  plug : Spine A B C → Nf A B → Nf A C
  plug [] f = f
  plug s id = sp s
  plug s (sp s') = sp (s' ++ s)
  plug (e ∷ s) (elim x) = {!!}
  plug (e ∷ s) (val v) = plug s (eliminate e v)

  beta : Elim B C → Val A B → Nf A C
  beta (pi1 f) (pair g h) = comp f g
  beta (pi2 f) (pair g h) = comp f h
  beta (eval f) (pair g h) = comp f (app g h)
  beta (copair f g) (in1 h) = comp f h
  beta (copair f g) (in2 h) = comp g h
  beta abort ()

  {-# TERMINATING #-}
  app : Nf D (A ⇒ B) → Nf D A → Nf D B
  -- app id h = comp (elim (eval id)) (val (pair id h))
  -- app id h = comp (elim (eval id)) (val (pair (val (curry (elim (eval id)))) h))
  -- app id h = app (val (curry (elim (eval id)))) h
  app id h = sp (apply h ∷ [])
  -- h   : Nf (A ⇒ B) A
  -- ————————————————————————————————————————————————————————————
  -- Goal: Nf (A ⇒ B) B
  app (sp s) h = sp (snoc s (apply h))
  app (elim e) h = {!!} -- comp (elim (eval id)) (val (pair (elim e) h))
  app (val (curry g)) h = comp g (val (pair id h))
    -- TERMINATION complaint
    -- pair id_D h : D -> D

-- data Flag : Set where
--   l r : Flag

-- data Nf : (f : Flag) (A B : Ty) → Set where
--   id : ∀ {f A} → Nf f A A
--   pair : Nf C A → Nf C B → Nf C (A × B)
--   fst : Nf ? A C → Nf r (A × B) C  -- f ∘ π₁
--   snd : Nf r (A × B) A

-- comp : ∀ f {l r A B C} → Nf l B C → Nf r A B → Nf f A B
-- comp = ?
