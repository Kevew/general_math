import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases

theorem amc12a_2019_p21 (z : ℂ) (h₀ : z = (1 + Complex.I) / Real.sqrt 2) : (∑ k ∈ Finset.Icc 1 12, (z^(k^2))) * (∑ k ∈ Finset.Icc 1 12, (1 / z^(k^2))) = 36 := by {
  have h1: z = Complex.cos (Real.pi /4) + Complex.sin (Real.pi /4) * Complex.I := by {
    rw [h₀]
    calc  (1 + Complex.I) / ↑√2
    _ = 1 / ↑√2 * 1 + 1 / ↑√2 * 1 * (Complex.I) := by ring
    _ = 1 / ↑√2 * √2/√2 + 1 / ↑√2 * √2/√2 * (Complex.I) := by norm_num
    _ = √2 / 2 + √2 / ↑2 * (Complex.I):= by sorry -- Ye, i dunno what ot put here. This should be trivial
    _ = Real.cos (Real.pi /4) + Real.sin (Real.pi /4) * (Complex.I) := by norm_num
    _ = Complex.cos (Real.pi /4) + Complex.sin (Real.pi /4) * Complex.I := by {
      rw [Complex.ofReal_cos, Complex.ofReal_sin]
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    }
  }

  have h2: ∀ k : ℕ, z ^ k = z ^ (k + 8) := by {
    intro k
    rw [h1]
    have h3: (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ (k + 8) =
    (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ k * (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ 8 := by {
      exact
        Lean.Grind.Semiring.pow_add
          (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) k 8
    }
    rw [h3]
    have h4: (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ 8 = 1 := by {
      calc (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ 8
      _ = Complex.cos (↑8 * (↑Real.pi / 4)) + Complex.sin (↑8 * (↑Real.pi / 4)) * Complex.I := by apply Complex.cos_add_sin_mul_I_pow 8 (Real.pi / 4)
      _ = (↑(Complex.cos (↑(2 : ℂ) * Real.pi)) + ↑(Complex.sin (↑2 * ↑Real.pi)) * Complex.I) := by {
        have lol: (8: ℂ) * (↑Real.pi / 4) = 2 * ↑Real.pi := by {
          ring
        }
        rw [lol]
      }
      _ = (1 + 0 * Complex.I) := by simp only [Complex.cos_two_pi, Complex.sin_two_pi, zero_mul, add_zero]
      _ = 1 := by ring
    }
    rw [h4]
    simp only [mul_one]
  }

  have pow_mod8 (n m : ℕ) : z^n = z^(n + 8 * m) := by {
    induction' m with m ih
    · simp only [mul_zero, add_zero]
    · have basic: (n + 8 * m) + 8 = n + 8 * (m + 1) := by {
        omega
      }
      calc z^n = z^(n + 8 * m) := ih
      _ = z^((n + 8 * m) + 8) := by rw [h2 (n + 8*m)]
      _ = z^(n + 8 * (m + 1)) := by rw [basic]
  }


  have s₁ : ∀ k ∈ ({1, 5, 9}: Finset ℕ), z ^ (k ^ 2) = z := by {
    intro k h3
    have h₃_or : k = 1 ∨ k = 5 ∨ k = 9 := by {
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      exact h3
    }
    rcases h₃_or with p1 | p2 | p3
    · rw [p1]
      norm_num
    · rw [p2]
      have t1: z ^ 1 = z ^ 5 ^ 2 := by {
        symm
        calc z ^ 5 ^ 2
        _ = z ^ (1 + 8 * 3) := by norm_num
        _ = z ^ 1 := by rw [← pow_mod8]
      }
      rw [← t1]
      norm_num
    · rw [p3]
      have t1: z ^ 1 = z ^ 9 ^ 2 := by {
        symm
        calc z ^ 9 ^ 2
        _ = z ^ (1 + 8 * 10) := by norm_num
        _ = z ^ 1 := by rw [← pow_mod8]
      }
      rw [← t1]
      norm_num
  }

  have s₂ : ∀ k ∈ ({2, 6, 10}: Finset ℕ), z ^ (k ^ 2) = -1 := by {
    intro k h3
    have h₃_or : k = 2 ∨ k = 6 ∨ k = 10 := by {
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      exact h3
    }
    have t1: z ^ 4 = -1 := by {
      rw [h1]
      calc (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ 4
      _ = (Complex.cos (4 * (↑Real.pi / 4)) + Complex.sin (4 * (↑Real.pi / 4)) * Complex.I) := by apply Complex.cos_add_sin_mul_I_pow 4 (Real.pi / 4)
      _ = (Complex.cos (↑Real.pi) + Complex.sin (↑Real.pi) * Complex.I) := by ring_nf
      _ = -1 + 0 * Complex.I := by simp only [Complex.cos_pi, Complex.sin_pi, zero_mul, add_zero]
      _ = -1 := by norm_num
    }
    rcases h₃_or with p1 | p2 | p3
    · rw [p1]
      norm_num
      rw [t1]
    · rw [p2]
      have t2: z ^ 4 = z ^ 6 ^ 2 := by {
        symm
        calc z ^ 6 ^ 2
        _ = z ^ (4 + 8 * 4) := by norm_num
        _ = z ^ 4 := by rw [← pow_mod8 4 4]
      }
      rw [← t2, t1]
    · rw [p3]
      have t2: z ^ 4 = z ^ 10 ^ 2 := by {
        symm
        calc z ^ 10 ^ 2
        _ = z ^ (4 + 8 * 12) := by norm_num
        _ = z ^ 4 := by rw [← pow_mod8 4 12]
      }
      rw [← t2, t1]
  }

  have s₃ : ∀ k ∈ ({3, 7, 11}: Finset ℕ), z ^ (k ^ 2) = z := by {
    intro k h3
    have h₃_or : k = 3 ∨ k = 7 ∨ k = 11 := by {
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      exact h3
    }
    have t1: z ^ 9 = z := by {
      calc z ^ 9
      _ = z ^ (1 + 8 * 1) := by norm_num
      _ = z ^ 1 := by rw [← h2]
      _ = z := by ring
    }
    rcases h₃_or with p1 | p2 | p3
    · rw [p1]
      norm_num
      rw [t1]
    · rw [p2]
      have t2: z ^ 9 = z ^ 7 ^ 2 := by {
        symm
        calc z ^ 7 ^ 2
        _ = z ^ (9 + 8 * 5) := by norm_num
        _ = z ^ 9 := by rw [← pow_mod8 9]
      }
      rw [← t2, t1]
    · rw [p3]
      have t2: z ^ 9 = z ^ 11 ^ 2 := by {
        symm
        calc z ^ 11 ^ 2
        _ = z ^ (9 + 8 * 14) := by norm_num
        _ = z ^ 9 := by rw [← pow_mod8 9]
      }
      rw [← t2, t1]
  }

  have s₄  : ∀ k ∈ ({4, 8, 12}: Finset ℕ), z ^ (k ^ 2) = 1 := by {
    intro k h3
    have h₃_or : k = 4 ∨ k = 8 ∨ k = 12 := by {
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      exact h3
    }
    have t1: z ^ 16 = 1 := by {
      rw [h1]
      have t2: Complex.cos (4 * ↑Real.pi) = 1 := by {
        calc Complex.cos (4 * ↑Real.pi)
        _ = Complex.cos (2 * ↑Real.pi + 2 * ↑Real.pi) := by ring
        _ = Complex.cos (2 * ↑Real.pi) := by rw [← Complex.cos_add_two_pi (2 * ↑Real.pi)]
        _ = Complex.cos (0 + 2 * ↑Real.pi) := by ring
        _ = Complex.cos 0 := by rw [← Complex.cos_add_two_pi 0]
        _ = 1 := by simp
      }
      have t3: Complex.sin (4 * ↑Real.pi) = 0 := by {
        calc Complex.sin (4 * ↑Real.pi)
        _ = Complex.sin (2 * ↑Real.pi + 2 * ↑Real.pi) := by ring
        _ = Complex.sin (2 * ↑Real.pi) := by rw [← Complex.sin_add_two_pi (2 * ↑Real.pi)]
        _ = Complex.sin (0 + 2 * ↑Real.pi) := by ring
        _ = Complex.sin 0 := by rw [← Complex.sin_add_two_pi 0]
        _ = 0 := by simp
      }
      calc (Complex.cos (↑Real.pi / 4) + Complex.sin (↑Real.pi / 4) * Complex.I) ^ 16
      _ = (Complex.cos (16 * (↑Real.pi / 4)) + Complex.sin (16 * (↑Real.pi / 4)) * Complex.I) := by apply Complex.cos_add_sin_mul_I_pow 16 (Real.pi / 4)
      _ = (Complex.cos (4 * ↑Real.pi) + Complex.sin (4 * ↑Real.pi) * Complex.I) := by ring_nf
      _ = 1 + 0 * Complex.I := by rw [t2, t3]
      _ = 1 := by norm_num
    }
    rcases h₃_or with p1 | p2 | p3
    · rw [p1]
      norm_num
      rw [t1]
    · rw [p2]
      have t2: z ^ 16 = z ^ 8 ^ 2 := by {
        symm
        calc z ^ 8 ^ 2
        _ = z ^ (16 + 8 * 6) := by norm_num
        _ = z ^ 16 := by rw [← pow_mod8 16]
      }
      rw [← t2, t1]
    · rw [p3]
      have t2: z ^ 16 = z ^ 12 ^ 2 := by {
        symm
        calc z ^ 12 ^ 2
        _ = z ^ (16 + 8 * 16) := by norm_num
        _ = z ^ 16 := by rw [← pow_mod8 16]
      }
      rw [← t2, t1]
  }
  have h3 : z ^ 1 = z := by
    simp
  have h4 : z ^ 4 = -1 := by
    have h6 : z ^ (2 ^ 2) = -1 := s₂ 2 (by simp)
    simpa using h6
  have h9 : z ^ 9 = z := by
    have h10 : z ^ (3 ^ 2) = z := s₃ 3 (by simp)
    simpa using h10
  have h16 : z ^ 16 = 1 := by
    have h17 : z ^ (4 ^ 2) = 1 := s₄ 4 (by simp)
    simpa using h17
  have h25 : z ^ 25 = z := by
    have h26 : z ^ (5 ^ 2) = z := s₁ 5 (by simp)
    simpa using h26
  have h36 : z ^ 36 = -1 := by
    have h37 : z ^ (6 ^ 2) = -1 := s₂ 6 (by simp)
    simpa using h37
  have h49 : z ^ 49 = z := by
    have h50 : z ^ (7 ^ 2) = z := s₃ 7 (by simp)
    simpa using h50
  have h64 : z ^ 64 = 1 := by
    have h65 : z ^ (8 ^ 2) = 1 := s₄ 8 (by simp)
    simpa using h65
  have h81 : z ^ 81 = z := by
    have h82 : z ^ (9 ^ 2) = z := s₁ 9 (by simp)
    simpa using h82
  have h100 : z ^ 100 = -1 := by
    have h101 : z ^ (10 ^ 2) = -1 := s₂ 10 (by simp)
    simpa using h101
  have h121 : z ^ 121 = z := by
    have h122 : z ^ (11 ^ 2) = z := s₃ 11 (by simp)
    simpa using h122
  have h144 : z ^ 144 = 1 := by
    have h145 : z ^ (12 ^ 2) = 1 := s₄ 12 (by simp)
    simpa using h145
  have t1: ∑ k ∈ Finset.Icc 1 12, z ^ k ^ 2 = 6 * z := by {
    simp only [Nat.reduceAdd, Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self,
      Finset.sum_singleton, one_pow, Nat.reducePow]
    simp only [h3, h4, h9, h16, h25, h36, h49, h64, h81, h100,
      h121, h144]
    ring
  }
  have t2: ∑ k ∈ Finset.Icc 1 12, 1 / z ^ k ^ 2 = 6/z := by {
    simp only [one_div, Nat.reduceAdd, Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self,
      Finset.sum_singleton, one_pow, pow_one, Nat.reducePow]
    simp only [h3, h4, h9, h16, h25, h36, h49, h64, h81, h100,
      h121, h144]
    ring
  }
  rw [t1, t2]
  have hz1 : z ≠ 0 := by
    rw [h₀]
    field_simp [Complex.ext_iff, Real.sqrt_pos.mpr]
  calc 6 * z * (6 / z)
  _ = 6 * 6 * z / z := by ring
  _ = 6 * 6 * 1 := by field_simp [hz1]
  _ = 36 := by norm_num
}


/-
Note that $z = \mathrm{cis }(45^{\circ})$.

Also note that $z^{k} = z^{k + 8}$ for all positive integers $k$ because of De Moivre's Theorem. Therefore, we want to look at the exponents of each term modulo $8$.

$1^2, 5^2,$ and $9^2$ are all $1 \pmod{8}$

$2^2, 6^2,$ and $10^2$ are all $4 \pmod{8}$

$3^2, 7^2,$ and $11^2$ are all $1 \pmod{8}$

$4^2, 8^2,$ and $12^2$ are all $0 \pmod{8}$

Therefore,

$z^{1^2} = z^{5^2} = z^{9^2} = \mathrm{cis }(45^{\circ})$

$z^{2^2} = z^{6^2} = z^{10^2} = \mathrm{cis }(180^{\circ}) = -1$

$z^{3^2} = z^{7^2} = z^{11^2} = \mathrm{cis }(45^{\circ})$

$z^{4^2} = z^{8^2} = z^{12^2} = \mathrm{cis }(0^{\circ}) = 1$

The term thus $\left(z^{1^2}+z^{2^2}+z^{3^2}+\dots+z^{{12}^2}\right)$ simplifies to $6\mathrm{cis }(45^{\circ})$, while the term $\left(\frac{1}{z^{1^2}}+\frac{1}{z^{2^2}}+\frac{1}{z^{3^2}}+\dots+\frac{1}{z^{{12}^2}}\right)$ simplifies to $\frac{6}{\mathrm{cis }(45^{\circ})}$. Upon multiplication, the $\mathrm{cis }(45^{\circ})$ cancels out and leaves us with $\textbf{(C) }36$.
-/
