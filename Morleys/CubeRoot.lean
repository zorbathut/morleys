/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Data.Complex.Exponential
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cube Roots of Unity

This file defines the primitive cube root of unity ω = e^(2πi/3) and proves its key properties
needed for Morley's theorem.

## Main definitions

* `Morley.ω` : The primitive cube root of unity e^(2πi/3)

## Main results

* `omega_cubed` : ω^3 = 1
* `one_add_omega_add_omega_sq` : 1 + ω + ω² = 0
* `omega_ne_one` : ω ≠ 1
* `omega_sq_ne_one` : ω² ≠ 1

These are essential for the equilateral triangle characterization: three points form an
equilateral triangle iff α + ωβ + ω²γ = 0 (up to orientation).
-/

namespace Morley

open Complex Real

/-- The primitive cube root of unity ω = e^(2πi/3) = cis(2π/3) -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- ω expressed as exp((2π/3) * I) -/
theorem omega_eq : ω = Complex.exp ((2 * Real.pi / 3) * Complex.I) := by
  simp only [ω]
  congr 1
  ring

/-- ω³ = 1 -/
theorem omega_cubed : ω ^ 3 = 1 := by
  rw [omega_eq]
  rw [← Complex.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have h : (3 : ℂ) * ((2 * Real.pi / 3) * Complex.I) = (2 * Real.pi) * Complex.I := by
    ring
  rw [h]
  exact Complex.exp_two_pi_mul_I

/-- The cube roots of unity satisfy z³ - 1 = (z - 1)(z² + z + 1) -/
theorem cube_minus_one_factor (z : ℂ) : z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1) := by ring

/-- ω ≠ 1 -/
theorem omega_ne_one : ω ≠ 1 := by
  simp only [ω]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h1 : (2 : ℂ) * Real.pi * Complex.I / 3 = n * (2 * Real.pi * Complex.I) := hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp only [ne_eq, ofReal_eq_zero]
    exact Real.pi_pos.ne'
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [hpi, hI]
  -- Simplify h1 to get 1/3 = n
  have h2 : (1 : ℂ) / 3 = n := by
    have h1' : (2 : ℂ) * Real.pi * Complex.I / 3 = n * (2 * Real.pi * Complex.I) := h1
    have h1'' : (1 : ℂ) / 3 * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      calc (1 : ℂ) / 3 * (2 * Real.pi * Complex.I)
        = (2 * Real.pi * Complex.I) / 3 := by ring
        _ = n * (2 * Real.pi * Complex.I) := h1'
    exact mul_right_cancel₀ h2pi h1''
  -- n = 1/3 is not an integer
  have h3 : (n : ℂ) = (1 : ℂ) / 3 := h2.symm
  have h4 : (3 : ℂ) * n = 1 := by
    rw [h3]
    field_simp
  have h5 : (3 : ℤ) * n = 1 := by
    have : ((3 : ℤ) : ℂ) * n = 1 := by exact_mod_cast h4
    exact_mod_cast this
  omega

/-- 1 + ω + ω² = 0 -/
theorem one_add_omega_add_omega_sq : 1 + ω + ω ^ 2 = 0 := by
  have h1 : ω ^ 3 - 1 = 0 := by simp [omega_cubed]
  have h2 : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := cube_minus_one_factor ω
  rw [h2] at h1
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have h3 : ω ^ 2 + ω + 1 = 0 := by
    have := mul_eq_zero.mp h1
    cases this with
    | inl h => exact (hne h).elim
    | inr h => exact h
  calc 1 + ω + ω ^ 2 = ω ^ 2 + ω + 1 := by ring
    _ = 0 := h3

/-- Equivalent form: ω² + ω + 1 = 0 -/
theorem omega_sq_add_omega_add_one : ω ^ 2 + ω + 1 = 0 := by
  have h := one_add_omega_add_omega_sq
  calc ω ^ 2 + ω + 1 = 1 + ω + ω ^ 2 := by ring
    _ = 0 := h

/-- ω ≠ 0 -/
theorem omega_ne_zero : ω ≠ 0 := by
  simp only [ω]
  exact Complex.exp_ne_zero _

/-- |ω| = 1 -/
theorem norm_omega : ‖ω‖ = 1 := by
  rw [omega_eq]
  have h : (2 * Real.pi / 3 : ℂ) * Complex.I = (2 * Real.pi / 3 : ℝ) * Complex.I := by simp
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi / 3)

/-- ω² ≠ 1 -/
theorem omega_sq_ne_one : ω ^ 2 ≠ 1 := by
  intro heq
  have h := one_add_omega_add_omega_sq
  rw [heq] at h
  have h2 : (2 : ℂ) + ω = 0 := by
    calc (2 : ℂ) + ω = 1 + ω + 1 := by ring
      _ = 0 := h
  have h3 : ω = -2 := by
    calc ω = 0 - 2 := by rw [← h2]; ring
      _ = -2 := by ring
  have habs : ‖ω‖ = 1 := norm_omega
  rw [h3] at habs
  simp at habs

/-- ω² = -1 - ω -/
theorem omega_sq_eq : ω ^ 2 = -1 - ω := by
  have h := omega_sq_add_omega_add_one
  calc ω ^ 2 = ω ^ 2 + ω + 1 - ω - 1 := by ring
    _ = 0 - ω - 1 := by rw [h]
    _ = -1 - ω := by ring

/-- ω³ⁿ = 1 for any natural n -/
theorem omega_pow_three_mul (n : ℕ) : ω ^ (3 * n) = 1 := by
  rw [pow_mul]
  rw [omega_cubed]
  simp

/-- ω * ω² = 1 -/
theorem omega_mul_omega_sq : ω * ω ^ 2 = 1 := by
  have h : ω * ω ^ 2 = ω ^ 3 := by ring
  rw [h, omega_cubed]

/-- ω² ≠ 0 -/
theorem omega_sq_ne_zero : ω ^ 2 ≠ 0 := pow_ne_zero 2 omega_ne_zero

/-- ω⁻¹ = ω² -/
theorem omega_inv : ω⁻¹ = ω ^ 2 := by
  have h : ω * ω ^ 2 = 1 := omega_mul_omega_sq
  rw [mul_comm] at h
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- (ω²)⁻¹ = ω -/
theorem omega_sq_inv : (ω ^ 2)⁻¹ = ω := by
  have h : ω ^ 2 * ω = 1 := by
    have : ω ^ 2 * ω = ω ^ 3 := by ring
    rw [this, omega_cubed]
  rw [inv_eq_iff_eq_inv]
  exact eq_inv_of_mul_eq_one_left h

end Morley
