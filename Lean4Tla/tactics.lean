import Mathlib.Tactic.Tauto
import «Lean4Tla».tla

syntax "tla_unseal": tactic

macro_rules
  | `(tactic| tla_unseal) => `(tactic | (apply predicate_ext; intro He; simp [*] at *; try tauto) )
