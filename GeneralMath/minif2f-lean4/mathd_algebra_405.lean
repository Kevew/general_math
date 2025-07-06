import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits

open BigOperators
open Real
open Nat
open Topology

theorem mathd_algebra_405 (S : Finset ℕ) (h₀ : ∀ x, x ∈ S ↔ 0 < x ∧ x^2 + 4 * x + 4 < 20) :
    S.card = 2 := by {
  have : S = {1 , 2} := by {
    ext x
    constructor
    · intro h1
      specialize h₀ x
      apply h₀.mp at h1
      have c:  x < 3 := by {
        by_contra h3
        push_neg at h3
        rcases h1 with ⟨h1, h2⟩
        have : x ^ 2 + 4 * x + 4 ≥ 20 := by {
          calc x ^ 2 + 4 * x + 4
          _ ≥ 3 ^ 2 + 4 * 3 + 4 := by nlinarith
          _ ≥ 20 := by norm_num
        }
        linarith
      }
      interval_cases x <;> try {contradiction} <;> simp
    · intro h1
      rw [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with h2 | h3
      · specialize h₀ 1
        have h1: 0 < 1 ∧ 1 ^ 2 + 4 * 1 + 4 < 20 := by omega
        rw [h2]
        exact h₀.mpr h1
      · specialize h₀ 2
        have h1: 0 < 2 ∧ 2 ^ 2 + 4 * 2 + 4 < 20 := by omega
        rw [h3]
        exact h₀.mpr h1
  }
  rw [this]
  exact rfl
}
