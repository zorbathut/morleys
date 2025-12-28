/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Exponential
import Morleys.CubeRoot
import Morleys.Rotation

/-!
# Equilateral Triangle Characterization

This file establishes the algebraic characterization of equilateral triangles using
cube roots of unity, which is central to Connes' proof of Morley's theorem.

## Main results

* `omega_eq_cis_two_pi_div_three` : ω = cis(2π/3)
* `omega_sum_zero_isEquilateral` : If P + ω*Q + ω²*R = 0, then PQR is equilateral
* `equilateral_omega_iff` : P + ω*Q + ω²*R = 0 iff P - R = -ω*(Q - R)

The key insight is that for an equilateral triangle PQR with the right orientation,
the weighted sum with powers of ω vanishes. This provides a purely algebraic way to
verify equilaterality.
-/

namespace Morley

open Complex Real

/-- ω equals cis(2π/3) -/
theorem omega_eq_cis_two_pi_div_three : ω = cis (2 * Real.pi / 3) := by
  simp only [ω, cis]
  congr 1
  push_cast
  ring

/-- ω² equals cis(4π/3) -/
theorem omega_sq_eq_cis : ω ^ 2 = cis (4 * Real.pi / 3) := by
  rw [omega_eq_cis_two_pi_div_three]
  simp only [cis]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- ω + 1 = -ω² -/
theorem omega_add_one : ω + 1 = -ω ^ 2 := by
  have h := one_add_omega_add_omega_sq
  calc ω + 1 = 1 + ω := by ring
    _ = -(ω ^ 2) := by
        have : 1 + ω + ω ^ 2 = 0 := h
        calc 1 + ω = (1 + ω + ω ^ 2) - ω ^ 2 := by ring
          _ = 0 - ω ^ 2 := by rw [this]
          _ = -(ω ^ 2) := by ring

/-- 1 + ω² = -ω -/
theorem one_add_omega_sq : 1 + ω ^ 2 = -ω := by
  have h := one_add_omega_add_omega_sq
  calc 1 + ω ^ 2 = (1 + ω + ω ^ 2) - ω := by ring
    _ = 0 - ω := by rw [h]
    _ = -ω := by ring

/-- cis(2π/3) = ω expressed directly -/
theorem cis_two_pi_div_three_eq_omega : cis (2 * Real.pi / 3) = ω :=
  omega_eq_cis_two_pi_div_three.symm

/-- Equilateral triangle: all three sides have equal length -/
def IsEquilateral (P Q R : ℂ) : Prop :=
  ‖P - Q‖ = ‖Q - R‖ ∧ ‖Q - R‖ = ‖R - P‖

/-- |ω²| = 1 -/
theorem norm_omega_sq : ‖ω ^ 2‖ = 1 := by
  rw [norm_pow]
  simp [norm_omega]

/-- P + ω*Q + ω²*R = 0 implies |P - Q| = |Q - R| -/
theorem omega_sum_zero_eq_sides_PQ_QR (P Q R : ℂ)
    (h : P + ω * Q + ω ^ 2 * R = 0) : ‖P - Q‖ = ‖Q - R‖ := by
  -- From h: P = -ω*Q - ω²*R
  have hP : P = -(ω * Q) - ω ^ 2 * R := by
    have : P + ω * Q + ω ^ 2 * R = 0 := h
    calc P = (P + ω * Q + ω ^ 2 * R) - ω * Q - ω ^ 2 * R := by ring
      _ = 0 - ω * Q - ω ^ 2 * R := by rw [this]
      _ = -(ω * Q) - ω ^ 2 * R := by ring
  -- P - Q = -ω*Q - ω²*R - Q = -(1 + ω)*Q - ω²*R
  have hPQ : P - Q = -((1 + ω) * Q) - ω ^ 2 * R := by
    rw [hP]; ring
  -- 1 + ω = -ω²
  have h1ω : (1 : ℂ) + ω = -ω ^ 2 := by
    have := omega_add_one
    calc (1 : ℂ) + ω = ω + 1 := by ring
      _ = -ω ^ 2 := omega_add_one
  rw [h1ω] at hPQ
  -- P - Q = ω²*Q - ω²*R = ω²*(Q - R)
  have hPQ' : P - Q = ω ^ 2 * (Q - R) := by
    calc P - Q = -((-ω ^ 2) * Q) - ω ^ 2 * R := hPQ
      _ = ω ^ 2 * Q - ω ^ 2 * R := by ring
      _ = ω ^ 2 * (Q - R) := by ring
  rw [hPQ', norm_mul, norm_omega_sq, one_mul]

/-- P + ω*Q + ω²*R = 0 implies |Q - R| = |R - P| -/
theorem omega_sum_zero_eq_sides_QR_RP (P Q R : ℂ)
    (h : P + ω * Q + ω ^ 2 * R = 0) : ‖Q - R‖ = ‖R - P‖ := by
  -- From h: P = -ω*Q - ω²*R
  have hP : P = -(ω * Q) - ω ^ 2 * R := by
    have : P + ω * Q + ω ^ 2 * R = 0 := h
    calc P = (P + ω * Q + ω ^ 2 * R) - ω * Q - ω ^ 2 * R := by ring
      _ = 0 - ω * Q - ω ^ 2 * R := by rw [this]
      _ = -(ω * Q) - ω ^ 2 * R := by ring
  -- R - P = R + ω*Q + ω²*R = (1 + ω²)*R + ω*Q
  have hRP : R - P = (1 + ω ^ 2) * R + ω * Q := by rw [hP]; ring
  -- 1 + ω² = -ω
  rw [one_add_omega_sq] at hRP
  -- R - P = -ω*R + ω*Q = ω*(Q - R)
  have hRP' : R - P = ω * (Q - R) := by
    calc R - P = -ω * R + ω * Q := hRP
      _ = ω * (Q - R) := by ring
  calc ‖Q - R‖ = ‖ω * (Q - R)‖ := by rw [norm_mul, norm_omega, one_mul]
    _ = ‖R - P‖ := by rw [← hRP']

/-- P + ω*Q + ω²*R = 0 implies equilateral triangle -/
theorem omega_sum_zero_isEquilateral (P Q R : ℂ)
    (h : P + ω * Q + ω ^ 2 * R = 0) : IsEquilateral P Q R :=
  ⟨omega_sum_zero_eq_sides_PQ_QR P Q R h, omega_sum_zero_eq_sides_QR_RP P Q R h⟩

/-- The key characterization: P + ω*Q + ω²*R = 0 iff P - R = -ω*(Q - R).
    This is the correct form of the rotation relationship. -/
theorem equilateral_omega_iff (P Q R : ℂ) (_hPR : P ≠ R) :
    (P + ω * Q + ω ^ 2 * R = 0) ↔ (P - R = -ω * (Q - R)) := by
  constructor
  · intro h
    -- From h: P = -ω*Q - ω²*R
    have hP : P = -(ω * Q) - ω ^ 2 * R := by
      have : P + ω * Q + ω ^ 2 * R = 0 := h
      calc P = (P + ω * Q + ω ^ 2 * R) - ω * Q - ω ^ 2 * R := by ring
        _ = 0 - ω * Q - ω ^ 2 * R := by rw [this]
        _ = -(ω * Q) - ω ^ 2 * R := by ring
    calc P - R = (-(ω * Q) - ω ^ 2 * R) - R := by rw [hP]
      _ = -(ω * Q) - (1 + ω ^ 2) * R := by ring
      _ = -(ω * Q) - (-ω) * R := by rw [one_add_omega_sq]
      _ = -ω * (Q - R) := by ring
  · intro hrot
    -- P - R = -ω*(Q - R)
    -- P = R - ω*(Q - R) = R - ω*Q + ω*R = (1 + ω)*R - ω*Q
    have hP : P = (1 + ω) * R - ω * Q := by
      calc P = (P - R) + R := by ring
        _ = -ω * (Q - R) + R := by rw [hrot]
        _ = (1 + ω) * R - ω * Q := by ring
    -- 1 + ω = -ω²
    have h1ω : (1 : ℂ) + ω = -ω ^ 2 := by
      calc (1 : ℂ) + ω = ω + 1 := by ring
        _ = -ω ^ 2 := omega_add_one
    rw [h1ω] at hP
    -- P = -ω²*R - ω*Q
    calc P + ω * Q + ω ^ 2 * R
        = ((-ω ^ 2) * R - ω * Q) + ω * Q + ω ^ 2 * R := by rw [hP]
      _ = 0 := by ring

/-- Alternative: Q + ω*R + ω²*P = 0 (cyclic permutation) -/
theorem omega_sum_cyclic (P Q R : ℂ) :
    (P + ω * Q + ω ^ 2 * R = 0) ↔ (Q + ω * R + ω ^ 2 * P = 0) := by
  have hcubed : ω ^ 3 = 1 := omega_cubed
  have h4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = 1 * ω := by rw [hcubed]
      _ = ω := by ring
  constructor
  · intro h
    -- From P + ω*Q + ω²*R = 0, multiply by ω²:
    have hmul2 : ω ^ 2 * P + ω ^ 3 * Q + ω ^ 4 * R = 0 := by
      calc ω ^ 2 * P + ω ^ 3 * Q + ω ^ 4 * R
          = ω ^ 2 * (P + ω * Q + ω ^ 2 * R) := by ring
        _ = ω ^ 2 * 0 := by rw [h]
        _ = 0 := by ring
    simp only [hcubed, h4, one_mul] at hmul2
    -- Now: ω²*P + Q + ω*R = 0
    calc Q + ω * R + ω ^ 2 * P = ω ^ 2 * P + Q + ω * R := by ring
      _ = 0 := hmul2
  · intro h
    -- From Q + ω*R + ω²*P = 0, multiply by ω:
    -- ω*Q + ω²*R + ω³*P = 0
    -- ω*Q + ω²*R + P = 0 (using ω³ = 1)
    have hmul : ω * Q + ω ^ 2 * R + ω ^ 3 * P = 0 := by
      calc ω * Q + ω ^ 2 * R + ω ^ 3 * P
          = ω * (Q + ω * R + ω ^ 2 * P) := by ring
        _ = ω * 0 := by rw [h]
        _ = 0 := by ring
    simp only [hcubed, one_mul] at hmul
    -- Now: ω*Q + ω²*R + P = 0
    calc P + ω * Q + ω ^ 2 * R = ω * Q + ω ^ 2 * R + P := by ring
      _ = 0 := hmul

/-- The converse: equilateral with correct orientation implies omega sum is zero -/
theorem isEquilateral_omega_sum (P Q R : ℂ) (hRP : R ≠ P)
    (hangle : P - R = -ω * (Q - R)) :
    P + ω * Q + ω ^ 2 * R = 0 :=
  (equilateral_omega_iff P Q R hRP.symm).mpr hangle

/-- conj(ω) = ω² (since ω³ = 1 and |ω| = 1).
    Proof: For |z| = 1, conj(z) = z⁻¹. Since ω³ = 1, ω⁻¹ = ω². -/
theorem conj_omega : starRingEnd ℂ ω = ω ^ 2 := by
  have h1 : ω * starRingEnd ℂ ω = ‖ω‖ ^ 2 := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]
  rw [norm_omega] at h1
  simp at h1
  have h2 : starRingEnd ℂ ω = ω⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2, omega_inv]

/-- cis(-2π/3) = ω² -/
theorem cis_neg_two_pi_div_three_eq_omega_sq : cis (-(2 * Real.pi / 3)) = ω ^ 2 := by
  -- Use cis(-θ) = cis(θ)⁻¹ for real θ, then ω⁻¹ = ω²
  have h1 : (-(2 * Real.pi / 3) : ℝ) = -1 * (2 * Real.pi / 3) := by ring
  simp only [cis, h1]
  rw [neg_one_mul, Complex.ofReal_neg, neg_mul, Complex.exp_neg]
  have h : Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) = ω := by
    rw [omega_eq]
    congr 1
    push_cast
    ring
  rw [h, omega_inv]

end Morley
