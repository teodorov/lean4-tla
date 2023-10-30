-- import Mathlib.Tactic.Tauto
import «Lean4Tla».tla

variable {T: Type}
variable (p p₁ p₂ p₃ q : predicate T)

theorem tla_and_idem: ( p ∧ p) = p := by simp [tla_and]

theorem tla_or_idem: ( p ∨ p ) = p := by simp [tla_or]


theorem tla_and_comm: (p ∧ q) = (q ∧ p) :=
  by
    simp [tla_and]
    apply funext
    intro x
    apply propext
    apply And.comm

theorem tla_or_comm: (p ∨ q) = (q ∨ p) :=
  by
    simp [tla_or]
    apply funext
    intro x
    apply propext
    constructor
    intro H; apply Or.elim H (fun hp => Or.inr hp) (fun hq => Or.inl hq)
    intro H; apply Or.elim H (fun hp => Or.inr hp) (fun hq => Or.inl hq)

theorem tla_and_implies : ((p₁ ∧ p₂) → q) = (p₁ → p₂ → q) :=
  by
    simp [tla_and, tla_implies]
    apply funext
    intro X
    apply propext
    constructor
    . intro h
      intros hp₁ hp₂
      apply h
      apply And.intro
      exact hp₁
      exact hp₂
    . intro h
      intro hp1p2
      apply h
      apply hp1p2.left
      apply hp1p2.right

theorem tla_and_assoc : ((p₁ ∧ p₂) ∧ p₃) = (p₁ ∧ (p₂ ∧ p₃)) :=
  by
    simp [tla_and]
    apply funext
    intro X
    apply propext
    constructor
    . intro H
      apply And.intro
      apply H.left.left
      apply And.intro
      apply H.left.right
      apply H.right
    . intro H
      apply And.intro
      apply And.intro
      apply H.left
      apply H.right.left
      apply H.right.right

theorem tla_or_assoc : ((p₁ ∨ p₂) ∨ p₃) = (p₁ ∨ (p₂ ∨ p₃)) :=
  by
    simp [tla_or]
    apply funext
    intro X
    apply propext
    constructor
    . intro H
      apply Or.elim H
      intro p1p2
      apply Or.elim p1p2
      intro p1
      apply Or.intro_left; exact p1
      intro p2
      apply Or.intro_right; apply Or.intro_left; exact p2
      intro p3
      apply Or.intro_right; apply Or.intro_right; exact p3
    . intro H
      apply Or.elim H
      intro p1; apply Or.inl; apply Or.inl; exact p1
      intro p2p3; apply Or.elim p2p3
      intro p2; apply Or.inl; apply Or.inr; exact p2
      intro p3; apply Or.inr; exact p3

theorem tla_and_true_r : (p ∧ tla_true) = p :=
  by simp [tla_true, tla_and]

theorem tla_and_true_l : (tla_true ∧ p) = p :=
  by simp [tla_true, tla_and]


theorem tla_or_false_r : (p ∨ tla_false) = p :=
  by simp [tla_false, tla_or]

theorem tla_or_false_l : (tla_false ∨ p) = p :=
  by simp [tla_false, tla_or]

theorem tla_any_impl_true : p ⊢ tla_true :=
  by simp [pred_impl, tla_true]

theorem tla_false_impl_any : tla_false ⊢ p :=
  by simp [pred_impl, tla_false]

theorem tla_or_inl : p ⊢ p ∨ q :=
  by
    simp [pred_impl, tla_or]
    intros he hp
    apply Or.inl; exact hp

theorem tla_or_inr : q ⊢ p ∨ q :=
  by
    simp [pred_impl, tla_or]
    intros he hq
    apply Or.inr; exact hq

theorem tla_forall_intro {A} (φ: A → predicate A) Γ :
  (∀ x, Γ ⊢ φ x) → Γ ⊢ ∀ x, φ x
:= by
    simp [pred_impl, tla_forall]
    intro Hx
    intros e HG x
    apply Hx; apply HG

theorem tla_forall_apply {A} (φ: A → predicate A) (x₀: A) :
  (∀ x, φ x) ⊢ φ x₀
:= by
  simp [tla_forall, pred_impl]
  intro He Hx
  specialize Hx x₀; exact Hx

theorem tla_exists_intro {A} (φ: A → predicate A) :
  (∃ x, ⊢ φ x) → ⊢ ∃ x, φ x
:= by
    simp [tla_exists, valid]
    intro HEx e
    apply Exists.elim HEx
    intros HA He
    apply Exists.intro HA
    apply He

theorem tla_exists_impl {A} (φ: A → predicate A) (x₀ : A) :
  φ x₀ ⊢ ∃ x, φ x
:= by
  simp [tla_exists, pred_impl]
  intro He
  intro Hφ
  apply Exists.intro x₀; apply Hφ

theorem tla_exist_impl_intro {A} (φ: A → predicate A) Γ :
  (∃ x, Γ ⊢ φ x) →
  Γ ⊢ ∃ x, φ x
:= by
  simp [tla_exists, pred_impl]
  intro HEx He HΓ
  apply Exists.elim HEx
  intros Ha Hee
  exists Ha
  specialize Hee He
  apply Hee; apply HΓ

theorem tla_exist_and (φ: T → predicate T) :
  ((∃ x, φ x) ∧ p) = (∃ x, φ x ∧ p)
:= by
  simp [tla_exists, tla_and]
  apply funext
  intro Hx
  apply propext
  constructor
  . intro Hex
    apply Exists.elim Hex.left
    intro H Hφ
    exists H
    apply And.intro; exact Hφ; exact Hex.right
  . intro Hex
    apply And.intro
    . apply Exists.elim Hex
      intros H Hand
      exists H; apply Hand.left
    . apply Exists.elim Hex
      intro H Hand
      apply Hand.right


theorem tla_exists_or  [aI: Inhabited T] {φ: T → predicate T} :
  ((∃ x, φ x) ∨ p) = (∃ x, φ x ∨ p)
:= by
  simp [tla_exists, tla_or]
  apply funext
  intros hx
  apply propext
  constructor
  . intro HEx
    apply Or.elim HEx
    . intro X
      apply Exists.elim X
      intro h
      intro φhx
      exists h
      apply Or.inl; exact φhx
    . intros Hp
      exists aI.default
      apply Or.intro_right; exact Hp
  . intro HEx
    apply Exists.elim HEx
    intros h x
    apply Or.elim x
    intro φhx
    apply Or.inl; exists h
    intro phx
    apply Or.inr; exact phx

theorem tla_forall_and [aI: Inhabited T] {φ: T → predicate T}:
  ((∀ x, φ x) ∧ p) = (∀ x, φ x ∧ p)
:= by
  simp [tla_forall, tla_and]
  apply funext
  intro hx
  apply propext
  constructor
  . intros H hT
    apply And.intro; apply H.left; apply H.right
  . intros H
    apply And.intro; intro hT
    specialize H hT; exact H.left
    specialize H aI.default; exact H.right

open Classical
example (h : ¬¬m) : m :=
  byContradiction
    (fun h1 : ¬m =>
     show False from h h1)

theorem tla_forall_or [aI: Inhabited T] {φ: T → predicate T}:
  ((∀ x, φ x) ∨ p) = (∀ x, φ x ∨ p)
:= by
  simp [tla_forall, tla_or]
  apply funext
  intro hx
  apply propext
  constructor
  . intros H hT
    apply Or.elim H
    intros Hl
    apply Or.inl; specialize Hl hT; exact Hl
    intro hP; apply Or.inr; exact hP
  . intros H
    apply byContradiction
    intro H!
    sorry
