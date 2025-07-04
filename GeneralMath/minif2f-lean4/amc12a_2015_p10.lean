import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.IntervalCases

open BigOperators
open Real
open Nat
open Topology


theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + (x * y) = 80) :
    x = 26 := by {
  have h3 : (x + 1) * (y + 1) = 81 := by linarith
  have h4 : x + 1 ∣ 81 := by {
    use y + 1
    linarith
  }
  have h5 : x + 1 > 0 := by nlinarith
  have h6 : x + 1 ≤ 81 := by apply Int.le_of_dvd (by norm_num) h4
  interval_cases h : x + 1
  <;> omega
}
