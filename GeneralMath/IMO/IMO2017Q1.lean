/-
Copyright (c) 2024 Qi Wen Wei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Wen Wei
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.ModEq

theorem square_imply_mod_2: ∀n : ℤ, IsSquare n → n ≡ 0 [ZMOD 3] ∨ n ≡ 1 [ZMOD 3] := by {
  intro n a5
  rcases a5 with ⟨r, hr⟩
  have a5 : (n : ℤ) % 3 = 0 ∨ (n : ℤ) % 3 = 1 := by {
    have a6 : (n : ℤ) = (r : ℤ) ^ 2 := by {
      linarith
    }
    rw [a6]
    have a7 : ((r : ℤ) ^ 2 % 3 = 0 ∨ (r : ℤ) ^ 2 % 3 = 1) := by {
      have a8 : (r : ℤ) % 3 = 0 ∨ (r : ℤ) % 3 = 1 ∨ (r : ℤ) % 3 = 2 := by omega
      rcases a8 with (a8 | a8 | a8)
      <;> simp [pow_two, Int.add_emod, Int.mul_emod, a8] <;> omega
    }
    omega
  }
  simp [Int.ModEq] at *
  omega
}

theorem useful: ∀ n : ℤ, n ≡ 2 [ZMOD 3] → ¬ IsSquare n := by {
  intro n hn
  intro h
  have h1 : n ≡ 0 [ZMOD 3] ∨ n ≡ 1 [ZMOD 3] := by
    exact square_imply_mod_2 n h
  have h2 : n % 3 = 2 := by
    exact hn
  have h3 : n % 3 = 0 ∨ n % 3 = 1 := by
    exact h1
  omega
}


theorem useful_2 (n: ℤ): n ≡ 0 [ZMOD 3] ∨ n ≡ 1 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by {
  have a8 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  simp [Int.ModEq] at *
  exact a8
}

theorem imo_q (seq: ℕ → ℤ)
  (h0: seq 0 > 1)
  (h1: ∀ n : ℕ, IsSquare (seq n) → seq (n + 1) = Int.sqrt (seq n))
  (h2: ∀ n : ℕ, ¬ IsSquare (seq n) → seq (n + 1) = seq n + 3)
  : {a0 : ℤ | ∃ A : ℝ, {n | seq n = A}.Infinite ∧ a0 > 1}
  = {x : ℤ | 3 ∣ x ∧ x > 0} := by {

  have claim_1 (n m : ℕ) (a0: seq n ≡ -1 [ZMOD 3])
    (a1: m ≥ n): ¬ IsSquare (seq m) := by {
    have sub_claim_1 (n m : ℕ) (a0: seq n ≡ -1 [ZMOD 3])
        (a1: m ≥ n): ¬ IsSquare (seq m) ∧ seq m ≡ -1 [ZMOD 3] := by {
      have a1: n ≤ m := by exact a1
      induction' m, a1 using Nat.le_induction with k hk1 hk2
      · constructor
        · exact useful (seq n) a0
        · exact a0
      · apply hk2 at hk1
        have a2: seq (k + 1) = seq k + 3 := by {
          apply h2
          have a3: 0 ≤ k := by exact Nat.zero_le k
          exact hk1.left
        }
        have a3: seq (k + 1) ≡ -1 [ZMOD 3] := by {
          calc seq (k + 1)
          _ = seq k + 3 := by rw [a2]
          _ ≡ -1 + 3 [ZMOD 3] := by rel [hk1.right]
          _ ≡ -1 [ZMOD 3] := by rfl
        }
        constructor
        · exact useful (seq (k + 1)) a3
        · exact a3
    }
    have t: ¬ IsSquare (seq m) ∧ seq m ≡ -1 [ZMOD 3] := by {
      exact sub_claim_1 n m a0 a1
    }
    rcases t with ⟨a, b⟩
    exact a
  }

  have claim_2 (n: ℕ) (a0: ¬ seq n ≡ -1 [ZMOD 3])
      (a1: seq n > 9): ∃ m : ℕ, m > n ∧ seq m < seq n := by {
    let t := Int.sqrt (seq n)
    have a2: t > 3 := by {
      calc t
      _ = Int.sqrt (seq n) := by rfl
      _ > Int.sqrt (9) := by sorry
      _ = 3 := by rfl
    }

    have ht_bounds : t * t < seq n ∧ seq n < (t + 1) * (t + 1) := by {
      constructor
      sorry
      sorry
    }
    rcases ht_bounds with ⟨p1, p2⟩

    have h_an_mod_3 : seq n ≡ 0 [ZMOD 3] ∨ seq n ≡ 1 [ZMOD 3] := by {
      have t1 := useful_2 (seq n)
      rcases t1 with t1 | t1 | t1
      · left
        exact t1
      · right
        exact t1
      · have h2: ¬seq n ≡ 2 [ZMOD 3] := by exact a0
        contradiction
    }

    have h_j_exists : ∃ j ∈ ({1, 2, 3} : Finset ℕ), ∃ m : ℕ, m > n ∧ (t + j)^2 = seq m := by {
      have h5 : seq n % 3 = 0 ∨ seq n % 3 = 1 ∨ seq n % 3 = 2 := by omega
      rcases h5 with (h | h | h)
      · -- Case seq n % 3 = 0
        have h1: ∀x : ℤ, 3 ∣ x → 3 ∣ x^2 := by {
          sorry
        }
        have : 3 ∣ (t + 1) ∨ 3 ∣ (t + 2) ∨ 3 ∣ (t + 3) := by {
          omega
        }
        rcases this with t1 | t1 | t1
        · have t3: 3 ∣ (t + 1) ^ 2 := by exact h1 (t + 1) t1
          have t4: ∃ k : ℕ, (t + 1) ^ 2 - seq n = 3 * k := by sorry
          rcases t4 with ⟨k, hk⟩
          use 1
          constructor
          · simp only [Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
            or_false]
          · use n + k
            constructor
            · omega
            · 



      · sorry
      · have contra: ¬seq n ≡ 2 [ZMOD 3] := by exact a0
        contradiction


    }
    rcases h_j_exists with ⟨j, hm, m, a4, a5⟩
    use m + 1
    have a6: IsSquare (seq m) := by {
      use (t + ↑j)
      rw [← a5]
      exact Lean.Grind.Semiring.pow_two (t + ↑j)
    }
    have a7: seq (m + 1) ≤ t + 3 := by {
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      have a9 := h1 m a6
      rw [← a5] at a9
      rcases hm with a8 | a8 | a8
      · rw [a8] at a9
        rw [a9]
        calc Int.sqrt ((t + ↑1) ^ 2)
        _ = Int.sqrt ((t + ↑1) * (t + ↑1)) := by ring_nf
        _ = ↑(t + ↑1).natAbs := by rw [Int.sqrt_eq]
        _ = (t + ↑1) := by rfl
        _ ≤ (t + 3) := by norm_num
      · rw [a8] at a9
        rw [a9]
        calc Int.sqrt ((t + ↑2) ^ 2)
        _ = Int.sqrt ((t + ↑2) * (t + ↑2)) := by ring_nf
        _ = ↑(t + ↑2).natAbs := by rw [Int.sqrt_eq]
        _ = (t + ↑2) := by rfl
        _ ≤ (t + 3) := by norm_num
      · rw [a8] at a9
        rw [a9]
        calc Int.sqrt ((t + ↑3) ^ 2)
        _ = Int.sqrt ((t + ↑3) * (t + ↑3)) := by ring_nf
        _ = ↑(t + ↑3).natAbs := by rw [Int.sqrt_eq]
        _ = (t + ↑3) := by rfl
        _ ≤ (t + 3) := by norm_num
    }
    constructor
    · omega
    · calc seq (m + 1) ≤ t + 3 := by exact a7
      _ < t ^ 2 := by nlinarith
      _ = t * t := by ring_nf
      _ < seq n := by exact p1
  }

  have claim_3 (n: ℕ) (a0: seq n ≡ 0 [ZMOD 3]):
      ∃m, m > n → seq m = 3 := by {
    have case1: seq n > 9 ∨ seq n ≤ 9 := by exact Int.lt_or_le 9 (seq n)
    rcases case1 with a1 | a1
    sorry
    sorry
  }

  have claim_4 (n: ℕ) (a0: seq n ≡ 1 [ZMOD 3]):
    ∃ m, m > n → seq m ≡ -1 [ZMOD 3] := by {
      sorry
  }





}
