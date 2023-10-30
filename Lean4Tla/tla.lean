/-
================================
Embedding the TLA logic in Coq
================================

This development defines a version of TLA (the Temporal Logic of Actions) in
Lean4.
This file just sets out the basic definitions of TLA, in particular:
- the notion of a (temporal) predicate,
- lifting the basic propositional operators like "not" and "and" to predicates, and
- the always and eventually *modalities* of TLA.
-/

notation "ℕ" => Nat

variable {Θ: Type}

/-
A TLA formula is defined using `predicate`, which is defined in Lean as a predicate over executions (also known as "behaviors" in TLA). Executions are in turn defined to be an infinite sequence of states, which come from some arbitrary type Θ. Note that throughout the entire theory Θ does not change and remains abstract. In TLA, Θ corresponds to the state of all the variables, which are implicitly all available.
-/
def exec (Θ : Type) := ℕ → Θ
def predicate Θ := exec Θ → Prop

/-
There are a few primitive ways to construct TLA predicates, by lifting state predicates or actions; the particular use of actions is what distinguishes TLA from LTL (linear temporal logic), although the two will look very similar in this development.
-/
def state_pred (p: Θ → Prop) : predicate Θ :=
    λ ex => p (ex 0)

notation:65 "⌜" P "⌝" => (state_pred P)

def action (Θ: Type) := Θ → Θ → Prop
def action_predicate (a: action Θ) : predicate Θ :=
  λ ex => a (ex 0) (ex 1)

notation:65 "⟨" a "⟩" => (action_predicate a)

/-
TLA lifts the basic propositional logic connectives to predicates over executions, in a straightforward way.
-/

def tla_not (p: predicate Θ) : predicate Θ := λ e => ¬ p e
def tla_or (p₁ p₂ : predicate Θ) : predicate Θ := λ e => p₁ e ∨ p₂ e
def tla_and (p₁ p₂ : predicate Θ) : predicate Θ := λ e => p₁ e ∧ p₂ e
--@[simp]
def tla_implies (p₁ p₂ : predicate Θ) : predicate Θ := λ e => p₁ e → p₂ e
def tla_forall {A: Type} (p: A → predicate θ) : predicate θ :=
  λ e => ∀ x, (p x) e
def tla_exists {A: Type} (p: A → predicate θ) : predicate θ :=
  λ e => ∃ x, (p x) e

/-
The heart of TLA's assertions are the `always` and `eventually` modalities. A modality is in general a transformation on formulas. `always p` (which will be written □ p) says that `p` holds "from now on". This is expressed using the `drop` function, which shifts a behavior by k steps.

The other important modality is `eventually p` (which will be written ◇ p).
-/

def drop (k: ℕ) (e: exec θ) : exec θ := λ n => e (n + k)
def always (p: predicate θ) : predicate θ := λ e => ∀ k, p (drop k e)
def eventually (p : predicate θ) : predicate θ := λ e => ∃ k, p (drop k e)

/-
This serves the rule of the "prime" in TLA, but with a more general and
formal definition than TLA, which seems to only use them in actions and does not treat it as a full-fledged modality.
-/
def later (p : predicate θ) : predicate θ := λ e => p (drop 1 e)

/-
`valid` asserts that a TLA formula "holds" or "is true", which is defined as holding for all executions. This is sometimes phrased as saying that `p` is a tautology, but that can be confusing if you're not used to it. We'll use the standard logic notation `⊢ p` to state that `p` is valid. Note that validity is a "meta language assertion" (Prop, since Coq is our meta language), not a TLA formula.
-/
--@[simp]
def valid (p: predicate θ) := ∀ e, p e

/-
`pred_impl` is equivalent to `valid (tla_implies p q)`, but it's convenient for L∃∀N4 to have a definition for it (maybe, I haven't actually tried getting rid of it).
-/
--@[simp]
def pred_impl (p q: predicate θ) := ∀ e, (p e) → (q e)

/-
We assume some L∃∀N4 axioms so that predicates can be proven equal in the `=` sense if they are logically equivalent, which simplifies working with equivalent predicates a bit.
-/
def pred_ext {A: Type} (P₁ P₂: A → Prop): (∀ x, P₁ x ↔ P₂ x) → P₁ = P₂ :=
-- funext (fun x => propext (h x))
  by
    intro H
    apply funext
    intro x
    apply propext
    apply H


noncomputable def predicate_ext (p₁ p₂ : predicate θ): (∀ e, p₁ e ↔ p₂ e) → p₁ = p₂ :=
  by apply pred_ext

def pred_impl_as_valid (p q: predicate θ) : (pred_impl p q) ↔ (valid $ tla_implies p q) := by
      simp [pred_impl, valid, tla_implies]



def equiv_to_impl (p q: predicate θ): (pred_impl p q) → (pred_impl q p) → p = q :=
  by
    simp [pred_impl]
    intros H₁ H₂
    apply predicate_ext
    intro e
    apply Iff.intro
    apply H₁
    apply H₂


def tla_true: predicate θ := λ _ => True
def tla_false: predicate θ := λ _ => False

/-
`enabled a` is a state predicate that defines what it means for an action to be
enabled.
-/
def enabled {T} (a: action T) (s: T) := ∃ z, a s z

/-
`tla_enabled` is just a convenience for lifting `enabled a` to a temporal
predicate.
-/
def tla_enabled {T} (a : action T) : predicate T := state_pred (enabled a)

notation:65 "⊢" p => valid p
notation:65 p "⊢" q => pred_impl p q
notation:65 "!" p => tla_not p
notation:65 p "∨" q => tla_or p q
notation:65 p "∧" q => tla_and p q
notation:65 p "→" q => tla_implies p q
notation:65 "∀" x "," p => tla_forall λ x => p
notation:65 "∃" x "," p => tla_exists λ x => p
notation:65 "□" p => always p
notation:65 "◇" p => eventually p

def weak_fairness {T} (a: action T): predicate T :=
  □ ( □ (tla_enabled a) → ( ◇⟨ a ⟩))

def strong_fairness {T} (a: action T): predicate T :=
  □ (□◇ (tla_enabled a) → ( ◇⟨ a ⟩))

def leads_to {T} (p q: predicate T): predicate T :=
  □(p → ◇q)

notation:65 p "⇝"  q => p leads_to q
