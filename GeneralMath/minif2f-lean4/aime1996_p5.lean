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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open BigOperators
open Real
open Nat
open Topology
open Polynomial
open Multiset


theorem aime_1996_p5 {a b c r s t : ℂ}
(hroots : (X^3 + 3*X^2 + 4*X - 11 : ℂ[X]).roots = {a, b, c})
(hroots' : (X^3 + C r*X^2 + C s*X + C t : ℂ[X]).roots = {a + b, b + c, c + a})
    : t = 23 := by {

  have t0: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).natDegree = 3 := by {
    compute_degree!
  }
  have t1: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).leadingCoeff = 1 := by {
    monicity!
  }
  have h0: ((X^3 + 3*X^2 + 4*X - 11 : ℂ[X]).roots).card = (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).natDegree := by {
    rw [hroots]
    rw [t0]
    simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, reduceAdd]
  }

  have h2 : (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]) = (X - C a) * (X - C b) * (X - C c) := by {
    have h2 := prod_multiset_X_sub_C_of_monic_of_roots_card_eq t1 (h0)
    rw [hroots] at h2
    rw [← h2]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    rw [← mul_assoc]
  }


  have hsplit : Splits (RingHom.id ℂ) (X ^ 3 + 3 * X ^ 2 + 4 * X - 11) := by {
    rw [h2]
    apply splits_mul
    · apply splits_mul
      · apply splits_X_sub_C
      · apply splits_X_sub_C
    · apply splits_X_sub_C
  }


  have a1 : a + b + c = -3 := by {
    have p0 : 2 ≤ (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).natDegree := by rw [t0]; norm_num
    have h3 := @coeff_eq_esymm_roots_of_splits _ _ _ hsplit 2 p0
    have t2: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).coeff 2 = 3 := by {
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_assoc]
    }
    have t3: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).roots.esymm (3 - 2) = a + b + c := by {
      rw [hroots]
      simp [esymm]
      have p1: (Multiset.map (fun x ↦ x.prod) (powersetCard 1 {c})) = {c} := by {
        have p1: (powersetCard 1 {c}) = {{c}} := by {
          rfl
        }
        rw [p1]
        simp only [map_singleton, prod_singleton]
      }
      rw [p1]
      simp only [sum_singleton]
      ring
    }
    rw [t0, t1, t2, t3] at h3
    norm_num at h3
    calc a + b + c
    _ = -1 * (-c + (-b + -a)) := by ring
    _ = -1 * (3) := by rw [h3]
    _ = -3 := by norm_num
  }

  have a2 : a * b + b * c + c * a = 4 := by {
    have p0 : 1 ≤ (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).natDegree := by rw [t0]; norm_num
    have h3 := @coeff_eq_esymm_roots_of_splits _ _ _ hsplit 1 p0
    have t2: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).coeff 1 = 4 := by {
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_assoc]
    }
    have t3: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).roots.esymm (3 - 1) = a * b + b * c + c * a := by {
      rw [hroots]
      simp [esymm]
      have p1: (powersetCard 1 {c}) = {{c}} := by {
        rfl
      }
      repeat rw [p1]
      simp only [map_singleton, prod_singleton, sum_singleton]
      ring
    }
    rw [t0, t1, t2, t3] at h3
    norm_num at h3
    exact id (Eq.symm h3)
  }

  have a3 : a * b * c = 11 := by {
    have p0 : 0 ≤ (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).natDegree := by rw [t0]; norm_num
    have h3 := @coeff_eq_esymm_roots_of_splits _ _ _ hsplit 0 p0
    have t2: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).coeff 0 = -11 := by {
      simp only [coeff_sub, coeff_add, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte,
        coeff_ofNat_mul, mul_zero, add_zero, coeff_X_zero, coeff_ofNat_zero, zero_sub]
    }
    have t3: (X ^ 3 + 3 * X ^ 2 + 4 * X - 11 : ℂ[X]).roots.esymm (3 - 0) = a * b * c := by {
      rw [hroots]
      simp [esymm]
      have p1: (powersetCard 1 {c}) = {{c}} := by {
        rfl
      }
      repeat rw [p1]
      simp only [map_singleton, prod_singleton, sum_singleton]
      ring
    }
    rw [t0, t1, t2, t3] at h3
    norm_num at h3
    exact id (Eq.symm h3)
  }

  have a4: t = -(a + b) * (b + c) * (c + a) := by {
    have t0': (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).natDegree = 3 := by {
      compute_degree!
    }
    have t1': (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).leadingCoeff = 1 := by {
      monicity!
    }
    have g1 : (X ^ 3 + C r * X ^ 2 + C s * X + C t) = (X - C (a + b)) * (X - C (b + c)) * (X - C (c + a)) := by {
      have h3: ((X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).roots).card = (X ^ 3 + C r * X ^ 2 + C s * X + C t : ℂ[X]).natDegree := by {
        rw [hroots']
        rw [t0']
        simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton, reduceAdd]
      }
      have g2 := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (t1') (h3)
      rw [hroots'] at g2
      rw [← g2]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      rw [← mul_assoc]
    }
    have hsplit' : Splits (RingHom.id ℂ) (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]) := by {
      rw [g1]
      apply splits_mul
      · apply splits_mul
        · apply splits_X_sub_C
        · apply splits_X_sub_C
      · apply splits_X_sub_C
    }

    have p0' : 0 ≤ (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).natDegree := by rw [t0']; norm_num
    have h3' := @coeff_eq_esymm_roots_of_splits _ _ _ hsplit' 0 p0'
    have t2': (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).coeff 0 = t := by {
      simp only [coeff_add, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, mul_coeff_zero,
        coeff_C_zero, mul_zero, add_zero, coeff_X_zero, zero_add]
    }
    have t3': (X ^ 3 + C r * X ^ 2 + C s * X + C t: ℂ[X]).roots.esymm (3 - 0) = (a + b) * (b + c) * (c + a) := by {
      rw [hroots']
      simp [esymm]
      have p1: (powersetCard 1 {c + a}) = {{c + a}} := by {
        rfl
      }
      repeat rw [p1]
      simp only [map_singleton, prod_singleton, sum_singleton]
      ring
    }
    rw [t0', t1', t2', t3'] at h3'
    norm_num at h3'
    calc t
    _ = -((a + b) * (b + c) * (c + a)) := by rw [h3']
    _ = -(a + b) * (b + c) * (c + a) := by ring
  }

  have r1 : a + b = - 3 - c := by rw [← a1]; ring
  have r2 : b + c = - 3 - a := by rw [← a1]; ring
  have r3 : c + a = - 3 - b := by rw [← a1]; ring
  rw [r1, r2, r3] at a4

  calc t
  _ = -(-3 - c) * (-3 - a) * (-3 - b) := by rw [a4]
  _ = (a + 3) * (b + 3) * (c + 3) := by ring
  _ = (a * b + 3 * a + 3 * b + 9) * (c + 3) := by ring
  _ = (a * b * c) + 3 * (a * b + b * c + c * a) + 9 * (a + b + c) + 27 := by ring
  _ = 11 + 3 * 4 + 9 * (-3) + 27 := by rw [a1, a2, a3]
  _ = 23 := by norm_num
}
