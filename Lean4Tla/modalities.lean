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

theorem always_idem:
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

theorem eventually_idem:
  (◇ ◇ p) = ◇ p
:= by {
  apply tla_not_inj
  simp [not_eventually]
  apply always_idem
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
  apply always_and
}

theorem always_eventually_distrib:
  (□◇ (p ∨ q)) = ((□◇ p) ∨ (□◇ q))
:= by {
  apply predicate_ext
  intro e
  sorry
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
:= by sorry

theorem eventually_always_distrib:
  (◇□ (p1 ∧ p2)) = ((◇□ p1) ∧ (◇□ p2))
:= by sorry

theorem always_or:
  ((□ p1) ∨ (□ p2)) ⊢ □ (p1 ∨ p2)
:= by {
  simp [always_to_eventually]
  simp [tla_not, eventually, pred_impl, tla_or]
  intros e H k
  tauto
}

theorem eventually_always_or:
  ((◇□ p1) ∨ (◇□ p2)) ⊢ ◇□ (p1 ∨ p2)
:= by sorry

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

theorem always_eventually_idem:
  (□ ◇ □ ◇ p) = □ ◇ p
:= by {
  apply predicate_ext
  simp [always, eventually]
  intro e
  constructor
  . intros H k
    exists k
    specialize H k
    sorry
  . intros H k
    exists k
    intros k1
    exists k1
    specialize H k1
    sorry


}

theorem eventually_always_idem:
  (◇ □ ◇ □ p) = ◇ □ p
:= by sorry

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

lemma kmp : ∀ n, n - 1 + 1 = n
:= by {
  intro n
  sorry

}
theorem always_unroll:
  (□ p) = (p ∧ (later (□ p)))
:= by {
  apply equiv_to_impl
  <;> simp [always, later, tla_and, pred_impl]
  <;> intro e H
  . apply And.intro
    . specialize H 0; apply H
    . intro k; specialize H (k + 1); rw [drop_drop]; exact H
  . intro H1 k; specialize H1 (k - 1); rw [drop_drop] at H1
    conv at H1 =>
      conv in k-1+1 => rw [kmp]
    exact H1
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
  ((□ (p ∧ q)) ⊢ r) →
  ((□ (p ∧ r)) ⊢ later r) →
  ((□ p) ⊢ □(q → □r))
:= by {
  intros Hr Hlr
  apply always_intro_impl
  rw [always_induction r]
  apply impl_intro'
  sorry
}

theorem always_induction_impl_pred a (Q R: T → Prop):
  (∀ s s', Q s → a s s' → R s) →
  (∀ s s', R s → a s s' → R s') →
  ((□ ⟨a⟩) ⊢ □(⌜Q⌝ → (□⌜R⌝)))
:= by {
  intros HR Hind
  apply always_induction_impl
  . sorry
  . sorry

}

theorem later_always:
  (□ p) ⊢ later (□ p)
:= by {
  rw [always_unroll]
  simp [always, pred_impl, later, drop]
  intro e H
  sorry
}

theorem later_eventually:
  (p ∨ later (◇ p)) = ◇ p
:= by sorry

theorem later_eventually_weaken:
  later (◇ p) ⊢ ◇ p
:= by sorry

theorem always_eventually_always:
  (□◇□ p) = ◇□ p
:= by sorry

theorem eventually_always_eventually:
  (◇□◇ p) = □◇ p
:= by sorry

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

example modality_chain_ex : @modality_chain T [true, false, false, true] p = (□ (◇ (◇ (□ p))))
:= by sorry


-- Hint Rewrite always_idem eventually_idem : tla.
-- Hint Rewrite always_eventually_idem eventually_always_idem : tla.
-- Hint Rewrite always_eventually_always eventually_always_eventually : tla.

theorem modality_chain_reduces (l: List Bool) (p: predicate T):
  (modality_chain l p = p) ∨
  (modality_chain l p = ◇ p) ∨
  (modality_chain l p = □ p) ∨
  (modality_chain l p = ◇□ p) ∨
  (modality_chain l p = □◇ p)
:= by sorry



-- Hint Rewrite always_idem eventually_idem : tla.
-- Hint Rewrite always_eventually_idem eventually_always_idem : tla.
-- Hint Rewrite always_eventually_always eventually_always_eventually : tla.
