import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Analysis.SpecialFunctions.Log.Base

open BigOperators
open Real
open Nat
open Topology


theorem aime_1984_p5 (a b : ℕ) (h₀ : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5)
(h₁ : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) : a * b = 512 := by {
  have h1: Real.logb 10 a / Real.logb 10 8 + 2 * Real.logb 10 b / Real.logb 10 4 = 5 := by {
    sorry
  }
  sorry
}



/-

Use the [[change of base formula]] to see that $\frac{\log a}{\log 8} + \frac{2 \log b}{\log 4} = 5$;
combine [[denominator]]s to find that $\frac{\log ab^3}{3\log 2} = 5$.
Doing the same thing with the second equation yields that $\frac{\log a^3b}{3\log 2} = 7$.
This means that $\log ab^3 = 15\log 2 \Longrightarrow ab^3 = 2^{15}$ and that $\log a^3 b = 21\log 2 \Longrightarrow a^3 b = 2^{21}$.
If we multiply the two equations together, we get that $a^4b^4 = 2^{36}$, so taking the fourth root of that, $ab = 2^9 = 512$.

-/
