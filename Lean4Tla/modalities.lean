/-
**TLA modalities**

This file has some basic results about the TLA modalities, especially relating
them to each other. For example one of the theorems with a slightly involved
proof is that `□◇ (p ∨ q) = □◇ p ∨ □◇ q`, despite the fact that □ on its own
does not distribute over ∨.
-/

import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import Std.Data.List.Lemmas
-- import Mathlib.Data.Nat
import «Lean4Tla».tla
import «Lean4Tla».core
import «Lean4Tla».propositional_ltl

variable {T: Type}
-- variable (e: exec T)
variable (p q r: predicate T)
variable (a: action T)
variable (n m k: ℕ)


theorem eventually_to_always:
  (◇ p) = ! (□ (! p))
:= by {
  simp [eventually, always, tla_not]
}

theorem always_to_eventually:
  (□ p) = ! (◇ (! p))
:= by {
  simp [eventually, always, tla_not]
}

@[simp] theorem always_idem:
  (□ □ p) = □ p
:= by {
  simp [always]
  apply predicate_ext
  intro He
  constructor
  . intros H k
    specialize H k 0
    simp [drop] at *; exact H
  . intro H k k1
    simp [drop] at *;
    specialize H (k1 + k)
    conv in _ + _ + _ => rw [Nat.add_assoc]
    exact H
}

@[simp] theorem eventually_idem:
  (◇ ◇ p) = ◇ p
:= by {
  apply tla_not_inj
  simp [not_eventually]
  apply predicate_ext
  intro e
  constructor
  . intros H x
    specialize H x 0
    rw [drop_0] at H
    exact H
  . intros H x₁ x₂
    rw [drop_drop]
    specialize H $ x₂ + x₁
    exact H
}



theorem always_intro:
  (⊢ p) ↔ ⊢ □ p
:= by {
  constructor
  . simp [valid, always, drop]
    intros H e k
    tauto
  . simp [valid, always]
    intros H e
    specialize H e 0
    rw [drop_0] at H
    exact H
}

theorem implies_generalize:
  (⊢ (p → q)) → (⊢ (□ p) → (□ q))
:= by {
  simp [valid, always, tla_implies]
  intros H e H1 k
  apply H
  apply H1
}

theorem impl_under_always:
  (p ⊢ q) → ((□ p) ⊢ (□ q))
:= by {
  apply implies_generalize
}

theorem always_intro_impl:
  ((□ p) ⊢ q) → ((□p) ⊢ □ q)
:= by {
  simp [pred_impl, always] at *
  intros H e H1 k
  apply H
  intro r
  rw [drop_drop]
  apply H1
}


theorem always_and:
  (□(p ∧ q)) = ((□p) ∧ □q)
:= by {
  simp [always, tla_and, drop]
  apply predicate_ext
  intro He
  constructor
  . intros H
    simp [*]
  . intros H k
    simp [*]
}

theorem later_and:
  later (p ∧ q) = (later p ∧ later q)
:= by {
  simp [later, tla_and]
}

theorem later_or:
  later (p ∨ q) = (later p ∨ later q)
:= by {
  simp [later, tla_or]
}

theorem eventually_or:
  (◇(p ∨ q)) = ((◇p) ∨ (◇q))
:= by {
  apply tla_not_inj
  simp [not_eventually, tla_not_or]
  apply predicate_ext
  intro e
  constructor
  . intros x
    push_neg
    exact Iff.mp ball_or_left x
  . push_neg
    intros H x
    apply And.intro
    . apply H.left
    . apply H.right
}

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

theorem always_eventually_distrib:
  (□◇ (p ∨ q)) = ((□◇ p) ∨ (□◇ q))
:= by {
  apply predicate_ext
  intro e
  simp [eventually, always, tla_or, drop_drop]
  constructor <;> (intros H)
  . sorry
  . apply Or.elim H
    . intro Hl
      intro k
      specialize Hl k
      let ⟨ x₁, H₁ ⟩ := Hl
      exists x₁
      apply Or.inl
      exact H₁
    . intro Hr
      intro k
      specialize Hr k
      let ⟨ x₁, H₁ ⟩ := Hr
      exists x₁
      apply Or.inr
      exact H₁
}

theorem eventually_and:
  (◇ (p ∧ q)) ⊢ (◇ p) ∧ ◇ q
:= by {
  simp [eventually, tla_and, pred_impl]
  intros e x pd p2
  apply And.intro
  . exists x
  . exists x
}

/-
this is a weakening; the left side says they happen at the same time, while
the right allows them to happen only separately
-/
theorem always_eventually_and:
  (□◇ (p1 ∧ p2)) ⊢ (□◇ p1) ∧ □◇ p2
:= by {
  simp [eventually, always, tla_and, pred_impl]
  intros e H
  apply And.intro <;> (intro k; specialize H k; tauto)
}

theorem eventually_always_distrib:
  (◇□ (p1 ∧ p2)) = ((◇□ p1) ∧ (◇□ p2))
:= by {
  apply tla_not_inj
  simp [*] at *
  apply predicate_ext
  intro e
  constructor
  . intros H x H₁ x₁
    specialize H x₁
    let ⟨xx, Hx⟩ := H
    exists xx
    apply Hx
    sorry
  . intros H₁
    sorry
}

theorem always_or:
  ((□ p1) ∨ (□ p2)) ⊢ □ (p1 ∨ p2)
:= by {
  simp [always_to_eventually]
  intros e H k
  tauto
}

theorem eventually_always_or:
  ((◇□ p1) ∨ (◇□ p2)) ⊢ ◇□ (p1 ∨ p2)
:= by {
  simp only [always, eventually] at *
  simp [drop_drop]
  intro e H
  apply Or.elim H
  . intro Hl
    let ⟨x₁, H₁⟩  := Hl;
    exists x₁
    tauto
  . intro Hr
    let ⟨x₁, H₁⟩ := Hr;
    exists x₁
    tauto
}

lemma always_eventually_reverse:
  (□◇ p) = ! ◇□ !p
:= by {
  simp [always, eventually, tla_not]
}

lemma eventually_always_reverse:
  (◇□ p) = ! □◇ !p
:= by {
  simp [always, eventually, tla_not]
}

@[simp] theorem always_eventually_idem:
  (□ ◇ (□ ◇ p)) = (□ ◇ p)
:= by {
  apply predicate_ext
  simp [always, eventually]
  intro e
  constructor
  . intros H k
    simp [drop_drop] at *
    specialize H k
    let ⟨x₁, H₁⟩ := H
    specialize H₁ 0
    let ⟨x₂, H₂⟩ := H₁
    exists x₁ + x₂
    simp [*] at *
    have ac: x₂ + (x₁ + k) = x₁ + x₂ + k := by {
      rw [add_comm]
      rw [add_assoc]
      conv in (k + _) => rw [← add_comm]
      rw [add_assoc]
    }
    rw [← ac]
    exact H₂
  . intros H k
    simp [drop_drop] at *
    exists 0
    intro x₂
    specialize H $ x₂ + k
    let ⟨x₁, H₁⟩ := H
    exists x₁
    simp; exact H₁
}

@[simp] theorem eventually_always_idem:
  (◇ □ ◇ □ p) = ◇ □ p
:= by {
  apply predicate_ext
  simp [always, eventually]
  intro e
  constructor
  . intro H
    simp [drop_drop] at *
    let ⟨ x₁, H₁ ⟩ := H
    specialize H₁ 0
    let ⟨ x₂, H₂ ⟩ := H₁
    exists x₂ + x₁
    intro k
    specialize H₂ k
    simp at *; apply H₂
  . intro H
    simp [drop_drop] at *
    let ⟨ x₁, H₁ ⟩ := H
    exists x₁
    intro x₂
    exists 0
    intro x₃
    specialize H₁ $ x₃ + x₂
    conv at H₁ =>
      conv in _ + _ + _ => rw [add_assoc]
    simp; apply H₁
}

--Hint Rewrite always_eventually_idem eventually_always_idem : tla.

theorem always_weaken:
  (□ p) ⊢ p
:= by {
  simp [always, pred_impl]
  intros e H
  specialize H 0
  apply H
}

theorem always_weaken_eventually:
  (□ p) ⊢ ◇ p
:= by {
  simp [always, pred_impl, eventually]
  intros e H
  exists 0
  apply H
}

theorem always_and_eventually:
  ((□ p) ∧ (◇ q)) ⊢ ◇ (p ∧ q)
:= by {
  simp [always, pred_impl, eventually, tla_and]
  intros e H1 n H2
  exists n
  specialize H1 n
  trivial
}

theorem always_to_later:
  (□ p) ⊢ later p
:= by {
  simp [always, pred_impl, later]
  intros _ H
  apply H
}

theorem later_to_eventually:
  (later p) ⊢ ◇ p
:= by {
  simp [later, pred_impl, eventually]
  intros e H
  exists 1
}

theorem always_expand:
  (□ p) = (p ∧ □ p)
:= by {
  apply predicate_ext
  intro e
  simp [always, tla_and]
  intro H
  specialize H 0
  apply H
}

theorem later_always:
  (□ p) ⊢ later (□ p)
:= by {
  simp [always, pred_impl, later]
  intros e H k
  specialize H $ k + 1
  rw [drop_drop]
  exact H
}

theorem always_unroll:
  (□ p) = (p ∧ (later (□ p)))
:= by {
  apply equiv_to_impl
  . simp [always, later, tla_and, pred_impl]
    intro e H
    apply And.intro
    . specialize H 0; apply H
    . intro k; specialize H (k + 1); rw [drop_drop]; exact H
  . intro e H
    simp [always, later, tla_and, pred_impl] at *
    intro k₁
    match k₁ with
    | 0 => rw [drop_0]; exact H.left
    | k₂ + 1 => rw [←drop_drop]; apply H.right
}


theorem always_induction:
  (□ p) = (p ∧ □(p → later p))
:= by {
  apply equiv_to_impl <;> simp [always, tla_and, tla_implies, later, pred_impl]
  . intros e H
    apply And.intro
    . specialize H 0; apply H
    . intros k _; specialize H (1 + k); rw [drop_drop]; exact H
  . intros e pe H k
    conv at H =>
      conv in p (drop _ (drop _ _)) => rw [drop_drop]
    induction k with
    | zero => rw [drop_0]; exact pe
    | succ k' ihp =>
      specialize H k'
      conv at H =>
        conv in p (drop (_+_) e) => rw [Nat.add_comm]
      apply H
      apply ihp
}

lemma impl_intro'_iff:
  (p ⊢ q → r) ↔ ((p ∧ q) ⊢ r)
:= by {
  simp [pred_impl, tla_and, tla_implies]
}

lemma impl_intro':
  ((p ∧ q) ⊢ r) →
  (p ⊢ q → r)
:= by {
  simp [pred_impl, tla_and, tla_implies]
}

lemma impl_intro'_2:
  (p ⊢ q → r) →
  ((p ∧ q) ⊢ r)
:= by {
  simp [pred_impl, tla_and, tla_implies]
}

theorem always_induction_impl:
  (((□ p) ∧ q) ⊢ r) →
  (((□ p) ∧ r) ⊢ later r) →
  ((□ p) ⊢ □(q → □r))
:= by {
  intros Hr Hind
  apply always_intro_impl
  rw [always_induction r]
  apply impl_intro'
  apply tla_entails_and
  . apply Hr
  . apply impl_intro'_2
-- TODO: it should be possible to prove this in the tla layer
    simp [*] at *
    intros e H₁ _ k₁ H₃
    apply Hind
    . intro k₂
      rw [drop_drop]
      apply H₁
    . exact H₃
}

theorem always_induction_impl_pred a (Q R: T → Prop):
  (∀ s s', Q s → a s s' → R s) →
  (∀ s s', R s → a s s' → R s') →
  ((□ ⟨a⟩) ⊢ □(⌜Q⌝ → (□⌜R⌝)))
:= by {
  intros Hqr Hrr
  apply always_induction_impl
  . simp [action_predicate,state_pred] at *
    intros e H₁ H₂
    specialize H₁ 0
    simp [drop_n] at *
    apply (Hqr (e 0) (e 1))
    exact H₂
    exact H₁
  . simp [action_predicate,state_pred] at *
    intros e H₁ H₂
    simp [drop_n] at *
    apply Hrr (e 0) (e 1)
    exact H₂
    exact H₁ 0
}

theorem later_eventually:
  (p ∨ later (◇ p)) = ◇ p
:= by {
  apply predicate_ext
  intro e
  constructor
  . intro H
    apply Or.elim H
    . intro H₁; exists 0
    . intro H₁
      let ⟨ kk, Hk ⟩ := H₁
      exists kk + 1
  . intro H
    let ⟨ kk, Hk ⟩ := H
    simp [*] at *
    match kk with
    | 0 =>
      apply Or.inl
      rw [drop_0] at Hk
      exact Hk
    | m+1 =>
      apply Or.inr
      exists m
}

theorem later_eventually_weaken:
  later (◇ p) ⊢ ◇ p
:= by {
  simp [*] at *
  intros e x H
  rw [drop_drop] at H
  exists x+1
}

@[simp] theorem always_eventually_always:
  (□◇□ p) = ◇□ p
:= by {
  apply predicate_ext
  intro e
  simp [*] at *
  constructor
  . intro H
    specialize H 0
    rw [drop_0] at H
    exact H
  . intros H k₁
    let ⟨m, Hm⟩ := H
    exists m
    intro nn
    rw [drop_drop]
    rw [drop_drop]
    specialize Hm $ nn + k₁
    rw [drop_drop] at Hm
    have Ha: nn + m + k₁ = nn + k₁ + m := by {
      rw [add_assoc]; rw [add_assoc];
      have Hmk : m + k₁ = k₁ + m := by apply add_comm
      rw [Hmk]
    }
    rw [Ha]
    exact Hm
}

@[simp] theorem eventually_always_eventually:
  (◇□◇ p) = □◇ p
:= by {
  apply predicate_ext
  intro e
  simp [*] at *
  simp [drop_drop]
  constructor
  . intros H k
    let ⟨ x₁, H₁ ⟩ := H
    specialize H₁ k
    let ⟨ x₂, H₂ ⟩ := H₁
    exists x₂ + x₁
    rw [add_assoc]
    conv in x₁ + _ => rw [add_comm]
    exact H₂
  . intros H
    exists 0
}

/-

---------------------------------
Characterization of modalities
---------------------------------

Modalities can be composed. Here we show that □ and ◇ only give rise to 4
distinct modalities.

|*)

(*|
For simplicity we represent a chain of modalities `□ (◇ (◇ (□ ...)) p)` by
interpreting a list of booleans, where true is □ and false is ◇. Yes, we could
do something cleaner.
-/

def modality_chain (l: List Bool) (p: predicate T) : predicate T :=
  match l with
  | [] => p
  | true :: l => □ (modality_chain l p)
  | false :: l => ◇ (modality_chain l p)

example : @modality_chain T [true, false, false, true] p = (□ (◇ (◇ (□ p))))
:= by rfl


-- Hint Rewrite always_idem eventually_idem : tla.
-- Hint Rewrite always_eventually_idem eventually_always_idem : tla.
-- Hint Rewrite always_eventually_always eventually_always_eventually : tla.

open List
theorem modality_chain_reduces (l: List Bool) (p: predicate T):
  (modality_chain l p = p) ∨
  (modality_chain l p = ◇ p) ∨
  (modality_chain l p = □ p) ∨
  (modality_chain l p = ◇□ p) ∨
  (modality_chain l p = □◇ p)
:= by {
  induction l with
  | nil =>
    rw [modality_chain]
    apply Or.inl; rfl
  | cons h₁ l₁ iH₁ =>
    cases h₁ <;> rw [modality_chain] at *
    . induction l₁ with
      | nil =>
        rw [modality_chain]
        apply Or.inr; apply Or.inl; rfl
      | cons h₂ l₂ iH₂ =>
        cases h₂ <;> rw [modality_chain] at *
        . rw [eventually_idem]
          apply iH₁
        . cases l₂ with
          | nil =>
            rw [modality_chain]
            tauto
          | cons h₃ l₃ =>
            cases h₃ <;> rw [modality_chain] at *
            . rw [eventually_always_eventually]
              apply iH₁
            . rw [always_idem] at *
              apply iH₂
              apply iH₁
    . induction l₁ with
      | nil =>
        rw [modality_chain]
        tauto
      | cons h₂ l₂ iH₂ =>
        cases h₂ <;> rw [modality_chain] at *
        . cases l₂ with
        | nil =>
          rw [modality_chain]
          tauto
        | cons h₃ l₃ =>
          cases h₃ <;> rw [modality_chain] at *
          . rw [eventually_idem] at *
            apply iH₂
            apply iH₁
          . rw [always_eventually_always]
            apply iH₁
        . rw [always_idem]
          apply iH₁
}



-- Hint Rewrite always_idem eventually_idem : tla.
-- Hint Rewrite always_eventually_idem eventually_always_idem : tla.
-- Hint Rewrite always_eventually_always eventually_always_eventually : tla.
