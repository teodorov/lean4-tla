import Mathlib.Tactic.Tauto
import Mathlib.Tactic.LibrarySearch
import «Lean4Tla».tla

variable {T: Type}
variable (p p₁ p₂ p₃ q r: predicate T)

def proof_to_true:
  (p ⊢ p) ↔ true
:= by {
  simp [pred_impl]
}

def not_proof_to_false:
  (¬p ⊢ p) ↔ False
:= by {
  simp [pred_impl]
}


lemma tla_not_not:
  (! ! p) = p
:= by {
  simp [tla_not]
}

lemma tla_not_inj:
  ((!p) = !q) → p = q
:= by {
  intro H
  rw [←(tla_not_not p), ←(tla_not_not q)]
  tauto
}

lemma tla_not_impl:
  ((!p) ⊢ !q) →
  q ⊢ p
:= by {
  simp [pred_impl, tla_not]
  intros H e Hq
  specialize H e
  tauto
}

lemma tla_not_or:
  (! (p ∨ q)) = (!p) ∧ (!q)
:= by {
  simp [tla_not, tla_or, tla_and]
  apply predicate_ext
  intro He
  tauto
}

lemma tla_not_and:
  (!(p ∧ q)) = ((!p) ∨ (!q))
:= by {
  simp [tla_not, tla_or, tla_and]
  apply predicate_ext
  intro He
  tauto
}

lemma tla_implies_to_or:
  (p → q) = ((!p) ∨ q)
:= by {
  simp [tla_not, tla_or, tla_implies]
  apply predicate_ext
  intro He
  tauto
}

lemma tla_or_to_implies:
  (p ∨ q) = ((!p) → q)
:= by {
  simp [tla_not, tla_or, tla_implies]
  apply predicate_ext
  intro He
  tauto
}

lemma tla_not_forall {A} (φ: A → predicate T):
  (!(tla_forall φ)) = (∃ x, !(φ x))
:= by {
  simp [tla_forall, tla_exists, tla_not]
}

lemma tla_not_exist {A} (φ: A → predicate T):
  ( ! tla_exists φ ) = (∀ x, !(φ x))
:= by {
  simp [tla_forall, tla_exists, tla_not]
}

lemma state_pred_e (P: T → Prop) e :
  state_pred P e ↔ P (e 0)
:= by {
  rfl
}

lemma action_pred_e (a: action T) e :
  (⟨ a ⟩) e ↔ a (e 0) (e 1)
:= by {
  rfl
}

@[simp] theorem tla_and_assoc:
  ((p ∧ q) ∧ r) = (p ∧ q ∧ r)
:= by {
  simp [tla_and, tla_or]
  apply predicate_ext
  intro He
  tauto
}

theorem tla_entails_to_iff:
  (p ⊢ q) →
  (q ⊢ p) →
  p = q
:= by {
  simp [pred_impl]
  intros H1 H2
  apply predicate_ext
  intro He
  tauto
}

theorem tla_entails_and_iff:
  ((p ⊢ q1) ∧ (p ⊢ q2)) ↔ (p ⊢ q1 ∧ q2)
:= by {
  simp [pred_impl, tla_and]
  constructor
  . intros H1 he
    tauto
  . intros H1
    apply And.intro
    . intros He pHe
      specialize H1 He
      tauto
    . intros He pHe
      specialize H1 He
      tauto
}

theorem tla_entails_and:
  (p ⊢ q1) →
  (p ⊢ q2) →
  (p ⊢ q1 ∧ q2)
:= by {
  rw [←tla_entails_and_iff]
  tauto
}

theorem entails_or_left:
  (p ⊢ q1) →
  (p ⊢ q1 ∨ q2)
:= by {
    simp [pred_impl, tla_or]
    intro H
    tauto
}

theorem entails_or_right:
  (p ⊢ q2) →
  (p ⊢ q1 ∨ q2)
:= by {
  simp [pred_impl, tla_or]
  intro H
  tauto
}

theorem entails_trans:
  (p ⊢ q) →
  (q ⊢ r) →
  (p ⊢ r)
:= by {
  simp [pred_impl]
  intro H1 H2 e pe
  tauto
}

theorem entails_cut:
  (p ⊢ q) →
  ((p ∧ q) ⊢ r) →
  (p ⊢ r)
:= by {
  simp [pred_impl, tla_and]
  intros H1 H2 e pe
  tauto
}

lemma tla_not_implies:
  (!(p → q)) = (p ∧ !q)
:= by {
  simp [tla_not, tla_and, tla_implies]
}

lemma drop_0 (e: exec T):
  drop 0 e = e
:= by {
  simp [drop]
}

lemma drop_n (e: exec T):
  drop k e n = e (n + k)
:= by {
  rfl
}

lemma drop_drop (e: exec T):
  drop n (drop m e) = drop (n + m) e
:= by {
  simp [drop]
  apply funext
  intro Hx
  conv in _ + _ + _ => rw [Nat.add_assoc]
}


theorem not_eventually:
  (! ◇p) = □ !p
:= by {
  apply predicate_ext; intro He
  simp [always, eventually, tla_not]
}

theorem not_always:
  (! □p) = ◇ !p
:= by {
  apply predicate_ext; intro He
  simp [always, eventually, tla_not]
}
