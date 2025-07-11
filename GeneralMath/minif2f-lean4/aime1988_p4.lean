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

theorem aime_1988_p4 (n : ℕ) (a : ℕ → ℝ) (h₀ : ∀ n, abs (a n) < 1)
  (h₁ : ∑ k ∈ Finset.range n, (abs (a k)) = 19 + abs (∑ k in Finset.range n, a k)) :
    20 ≤ n := by {
  have h1: ∑ k ∈ Finset.range n, |a k| < n := by {
    have h4 : ∑ k ∈ Finset.range n, |a k| < ∑ k ∈ Finset.range n, (1 : ℝ) := by {
      apply Finset.sum_lt_sum
      · intro i h1
        have := h₀ i
        exact le_of_lt (h₀ i)
      · by_cases h7 : n > 0
        · use 0
          constructor
          · simp only [Finset.mem_range]
            exact h7
          · apply h₀
        · push_neg at h7
          have hn0 : n = 0 := by linarith
          rw [hn0] at h₁
          norm_num [Finset.sum_range_succ] at h₁
    }
    have h6 : ∑ k ∈ Finset.range n, (1 : ℝ) = (n : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [h6] at h4
    exact h4
  }

  have h2: n ≥ 20 := by {
    have h2 : 19 + |∑ k ∈ Finset.range n, a k| < n := by {
      rw [← h₁]
      exact h1
    }
    have h3 : 19 < n := by {
      have h3: |∑ k ∈ Finset.range n, a k| ≥ 0 := by {
        exact abs_nonneg (∑ k ∈ Finset.range n, a k)
      }
      have h4: 19 + |∑ k ∈ Finset.range n, a k| ≥ 19 + |∑ k ∈ Finset.range n, a k| - |∑ k ∈ Finset.range n, a k| := by {
        simp only [add_sub_cancel_right, ge_iff_le, le_add_iff_nonneg_right, abs_nonneg]
      }
      have := calc 19
        _ = 19 + |∑ k ∈ Finset.range n, a k| - |∑ k ∈ Finset.range n, a k| := by simp only [add_sub_cancel_right]
        _ ≤ 19 + |∑ k ∈ Finset.range n, a k| := by exact h4
        _ < n := by omega
      have h2 : (19 : ℝ) < ↑n ↔ 19 < n := by {
        norm_cast
      }
      exact h2.mp this
    }
    exact h3
  }
  exact h2
}
