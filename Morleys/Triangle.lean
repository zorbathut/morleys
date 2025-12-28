/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Exponential
import Morleys.Rotation

/-!
# Triangle Angles in the Complex Plane

This file defines directed angles and non-collinearity for points in ℂ,
establishing the geometric foundation for Morley's theorem.

## Main definitions

* `Morley.angle_at` : Directed angle at a vertex
* `Morley.NonCollinear` : Three points that don't lie on a line

## Main results

* `trisected_angles_sum` : Trisected angles sum to π/3

These results bridge the geometric setup to the algebraic proof in Connes.lean.
-/

namespace Morley

open Complex Real

/-- Directed angle at vertex B from ray BA to ray BC.
    This is the argument of the ratio (A - B) / (C - B), giving the
    signed angle needed to rotate BA onto BC. Range is (-π, π]. -/
noncomputable def angle_at (A B C : ℂ) : ℝ := Complex.arg ((A - B) / (C - B))

/-- Three points are non-collinear if they are pairwise distinct and
    don't lie on a single line. -/
def NonCollinear (A B C : ℂ) : Prop :=
  A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ ¬∃ t : ℝ, C - A = t • (B - A)

/-- Non-collinear implies distinct points -/
theorem NonCollinear.ne_AB {A B C : ℂ} (h : NonCollinear A B C) : A ≠ B := h.1

theorem NonCollinear.ne_BC {A B C : ℂ} (h : NonCollinear A B C) : B ≠ C := h.2.1

theorem NonCollinear.ne_CA {A B C : ℂ} (h : NonCollinear A B C) : C ≠ A := h.2.2.1

/-- Non-collinear is symmetric in A and C -/
theorem NonCollinear.symm_AC {A B C : ℂ} (h : NonCollinear A B C) : NonCollinear C B A := by
  refine ⟨h.ne_BC.symm, h.ne_AB.symm, h.ne_CA.symm, ?_⟩
  intro ⟨t, ht⟩
  apply h.2.2.2
  -- We have A - C = t • (B - C), need to show ∃ s, C - A = s • (B - A)
  by_cases ht0 : t = 0
  · -- t = 0 means A = C, contradiction
    simp only [ht0, zero_smul, sub_eq_zero] at ht
    exact absurd ht.symm h.ne_CA
  by_cases ht1 : t = 1
  · -- t = 1 means A - C = B - C, so A = B, contradiction
    simp only [ht1, one_smul] at ht
    have : A = B := by
      have h1 : A - C = B - C := ht
      calc A = (A - C) + C := by ring
        _ = (B - C) + C := by rw [h1]
        _ = B := by ring
    exact absurd this h.ne_AB
  · -- General case: s = t / (t - 1)
    use t / (t - 1)
    have ht1' : (t : ℂ) - 1 ≠ 0 := by
      simp only [ne_eq, sub_eq_zero]
      exact fun heq => ht1 (Complex.ofReal_inj.mp heq)
    have h1t' : (1 : ℂ) - t ≠ 0 := by
      intro heq
      apply ht1'
      calc (t : ℂ) - 1 = -((1 : ℂ) - t) := by ring
        _ = -(0 : ℂ) := by rw [heq]
        _ = 0 := by ring
    simp only [Complex.real_smul] at ht ⊢
    -- From ht: A - C = t * (B - C), so A = (1-t)C + tB
    -- Then: B - A = (1-t)(B - C) [doesn't involve C - A!]
    have hBA : B - A = (1 - ↑t) * (B - C) := by
      have hA : A = (1 - ↑t) * C + ↑t * B := by
        have : A - C = ↑t * (B - C) := ht
        calc A = (A - C) + C := by ring
          _ = ↑t * (B - C) + C := by rw [this]
          _ = (1 - ↑t) * C + ↑t * B := by ring
      calc B - A = B - ((1 - ↑t) * C + ↑t * B) := by rw [hA]
        _ = (1 - ↑t) * B - (1 - ↑t) * C := by ring
        _ = (1 - ↑t) * (B - C) := by ring
    -- So B - C = (B - A) / (1 - t)
    have hBC : B - C = (B - A) / (1 - ↑t) := by
      field_simp [h1t']
      calc (B - C) * (1 - ↑t) = (1 - ↑t) * (B - C) := by ring
        _ = B - A := hBA.symm
    -- And C - A = -t(B - C) = -t(B - A)/(1-t) = t/(t-1) * (B - A)
    calc C - A = -(A - C) := by ring
      _ = -(↑t * (B - C)) := by rw [ht]
      _ = -(↑t * ((B - A) / (1 - ↑t))) := by rw [hBC]
      _ = -↑t / (1 - ↑t) * (B - A) := by ring
      _ = ↑t / (↑t - 1) * (B - A) := by
          congr 1
          field_simp [h1t']
          ring
      _ = ↑(t / (t - 1)) * (B - A) := by
          simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]

/-- Non-collinear is cyclic -/
theorem NonCollinear.cycle {A B C : ℂ} (h : NonCollinear A B C) : NonCollinear B C A := by
  refine ⟨h.ne_BC, h.ne_CA, h.ne_AB, ?_⟩
  intro ⟨t, ht⟩
  apply h.2.2.2
  -- We have A - B = t • (C - B), need to show ∃ s, C - A = s • (B - A)
  by_cases ht0 : t = 0
  · -- t = 0 means A = B, contradiction
    simp only [ht0, zero_smul, sub_eq_zero] at ht
    exact absurd ht h.ne_AB
  by_cases ht1 : t = 1
  · -- t = 1 means A - B = C - B, so A = C, contradiction
    simp only [ht1, one_smul] at ht
    have : A = C := by
      have h1 : A - B = C - B := ht
      calc A = (A - B) + B := by ring
        _ = (C - B) + B := by rw [h1]
        _ = C := by ring
    exact absurd this.symm h.ne_CA
  · -- General case: s = (t - 1) / t
    use (t - 1) / t
    have ht0' : (t : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ht0
    simp only [Complex.real_smul] at ht ⊢
    -- From ht: A - B = t * (C - B), so A = (1-t)B + tC
    -- Then: B - A = -t(C - B) = t(B - C) [doesn't involve C - A!]
    have hBA : B - A = ↑t * (B - C) := by
      have hA : A = (1 - ↑t) * B + ↑t * C := by
        have : A - B = ↑t * (C - B) := ht
        calc A = (A - B) + B := by ring
          _ = ↑t * (C - B) + B := by rw [this]
          _ = (1 - ↑t) * B + ↑t * C := by ring
      calc B - A = B - ((1 - ↑t) * B + ↑t * C) := by rw [hA]
        _ = ↑t * B - ↑t * C := by ring
        _ = ↑t * (B - C) := by ring
    -- So B - C = (B - A) / t
    have hBC : B - C = (B - A) / ↑t := by
      field_simp [ht0']
      calc (B - C) * ↑t = ↑t * (B - C) := by ring
        _ = B - A := hBA.symm
    -- And C - A = (1-t)(C - B) = -(1-t)(B - C) = -(1-t)(B - A)/t = (t-1)/t * (B - A)
    have hCA : C - A = (1 - ↑t) * (C - B) := by
      have hA : A = (1 - ↑t) * B + ↑t * C := by
        have : A - B = ↑t * (C - B) := ht
        calc A = (A - B) + B := by ring
          _ = ↑t * (C - B) + B := by rw [this]
          _ = (1 - ↑t) * B + ↑t * C := by ring
      calc C - A = C - ((1 - ↑t) * B + ↑t * C) := by rw [hA]
        _ = (1 - ↑t) * C - (1 - ↑t) * B := by ring
        _ = (1 - ↑t) * (C - B) := by ring
    calc C - A = (1 - ↑t) * (C - B) := hCA
      _ = -(1 - ↑t) * (B - C) := by ring
      _ = -(1 - ↑t) * ((B - A) / ↑t) := by rw [hBC]
      _ = -(1 - ↑t) / ↑t * (B - A) := by ring
      _ = (↑t - 1) / ↑t * (B - A) := by ring
      _ = ↑((t - 1) / t) * (B - A) := by
          simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]

/-- angle_at is well-defined when points are distinct -/
theorem angle_at_well_defined {A B C : ℂ} (hAB : A ≠ B) (hCB : C ≠ B) :
    (A - B) / (C - B) ≠ 0 := by
  apply div_ne_zero
  · exact sub_ne_zero.mpr hAB
  · exact sub_ne_zero.mpr hCB

/-- For non-collinear points, the ratio (A - B) / (C - B) is not a real number -/
theorem NonCollinear.ratio_not_real {A B C : ℂ} (h : NonCollinear A B C) :
    ∀ r : ℝ, (A - B) / (C - B) ≠ r := by
  intro r hr
  apply h.2.2.2
  -- If (A - B) / (C - B) = r, then A - B = r * (C - B)
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr h.ne_BC.symm
  have heq : A - B = ↑r * (C - B) := by
    calc A - B = ((A - B) / (C - B)) * (C - B) := by field_simp [hCB]
      _ = ↑r * (C - B) := by rw [hr]
  -- Now derive C - A = s * (B - A) for s = (r - 1) / r
  by_cases hr0 : r = 0
  · -- r = 0 means A = B, contradiction
    simp only [hr0, Complex.ofReal_zero, zero_mul, sub_eq_zero] at heq
    exact absurd heq h.ne_AB
  · -- General case
    use (r - 1) / r
    have hr0' : (r : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hr0
    simp only [Complex.real_smul]
    -- From heq: A - B = r * (C - B), so A = (1-r)B + rC
    have hBA : B - A = ↑r * (B - C) := by
      calc B - A = -(A - B) := by ring
        _ = -(↑r * (C - B)) := by rw [heq]
        _ = ↑r * (B - C) := by ring
    have hBC : B - C = (B - A) / ↑r := by
      field_simp [hr0']
      calc (B - C) * ↑r = ↑r * (B - C) := by ring
        _ = B - A := hBA.symm
    have hCA : C - A = (1 - ↑r) * (C - B) := by
      calc C - A = C - B + (B - A) := by ring
        _ = C - B + ↑r * (B - C) := by rw [hBA]
        _ = C - B - ↑r * (C - B) := by ring
        _ = (1 - ↑r) * (C - B) := by ring
    calc C - A = (1 - ↑r) * (C - B) := hCA
      _ = -(1 - ↑r) * (B - C) := by ring
      _ = -(1 - ↑r) * ((B - A) / ↑r) := by rw [hBC]
      _ = -(1 - ↑r) / ↑r * (B - A) := by ring
      _ = (↑r - 1) / ↑r * (B - A) := by ring
      _ = ↑((r - 1) / r) * (B - A) := by
          simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one]

/-- For non-collinear points, the argument is not 0 or π -/
theorem NonCollinear.arg_ne_zero_pi {A B C : ℂ} (h : NonCollinear A B C) :
    Complex.arg ((A - B) / (C - B)) ≠ 0 ∧ Complex.arg ((A - B) / (C - B)) ≠ Real.pi := by
  set z := (A - B) / (C - B) with hz_def
  have hz : z ≠ 0 := angle_at_well_defined h.ne_AB h.ne_BC.symm
  constructor
  · -- arg z ≠ 0
    intro heq
    rw [Complex.arg_eq_zero_iff] at heq
    -- z.re ≥ 0 and z.im = 0, and z ≠ 0, so z.re > 0 or z = 0
    have hre : z.re ≠ 0 := by
      intro hre0
      apply hz
      apply Complex.ext <;> simp [hre0, heq.2]
    -- So z = z.re, a nonzero real
    have hzeq : (A - B) / (C - B) = (z.re : ℂ) := by
      rw [← hz_def]
      exact Complex.ext (by simp) (by simp [heq.2])
    exact h.ratio_not_real z.re hzeq
  · -- arg z ≠ π
    intro heq
    rw [Complex.arg_eq_pi_iff] at heq
    -- z.re < 0 and z.im = 0, so z = z.re, a negative real
    have hzeq : (A - B) / (C - B) = (z.re : ℂ) := by
      rw [← hz_def]
      exact Complex.ext (by simp) (by simp [heq.2])
    exact h.ratio_not_real z.re hzeq

/-- The angle at B is in the range (-π, π) for non-collinear points
    (strictly, excluding both endpoints) -/
theorem NonCollinear.angle_in_range {A B C : ℂ} (h : NonCollinear A B C) :
    -Real.pi < angle_at A B C ∧ angle_at A B C < Real.pi := by
  have ⟨_, hnepi⟩ := h.arg_ne_zero_pi
  constructor
  · exact Complex.neg_pi_lt_arg ((A - B) / (C - B))
  · exact lt_of_le_of_ne (Complex.arg_le_pi _) hnepi

/-- Sum of angles around a triangle: angle at A + angle at B + angle at C equals ±π.
    The sign depends on orientation. -/
theorem angle_sum_signed {A B C : ℂ} (h : NonCollinear A B C) :
    ∃ k : ℤ, angle_at B A C + angle_at C B A + angle_at A C B = k * Real.pi ∧
             (k = 1 ∨ k = -1) := by
  unfold angle_at
  set r1 := (B - A) / (C - A) with hr1_def
  set r2 := (C - B) / (A - B) with hr2_def
  set r3 := (A - C) / (B - C) with hr3_def

  have hCA : C - A ≠ 0 := sub_ne_zero.mpr h.ne_CA
  have hAB : A - B ≠ 0 := sub_ne_zero.mpr h.ne_AB
  have hBC : B - C ≠ 0 := sub_ne_zero.mpr h.ne_BC

  have hr1_ne : r1 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h.ne_AB.symm) hCA
  have hr2_ne : r2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h.ne_BC.symm) hAB
  have hr3_ne : r3 ≠ 0 := div_ne_zero (sub_ne_zero.mpr h.ne_CA.symm) hBC

  -- Product is -1
  have hprod : r1 * r2 * r3 = -1 := by
    simp only [hr1_def, hr2_def, hr3_def]
    field_simp [hCA, hAB, hBC]
    ring

  -- Let S be the sum of args
  set S := Complex.arg r1 + Complex.arg r2 + Complex.arg r3 with hS_def

  -- Bounds on individual args (each in (-π, π) strictly)
  have h1_lt_pi : Complex.arg r1 < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi r1) (h.symm_AC.cycle.arg_ne_zero_pi).2
  have h2_lt_pi : Complex.arg r2 < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi r2) (h.symm_AC.arg_ne_zero_pi).2
  have h3_lt_pi : Complex.arg r3 < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi r3) (h.cycle.symm_AC.arg_ne_zero_pi).2

  have h1_gt : -Real.pi < Complex.arg r1 := Complex.neg_pi_lt_arg r1
  have h2_gt : -Real.pi < Complex.arg r2 := Complex.neg_pi_lt_arg r2
  have h3_gt : -Real.pi < Complex.arg r3 := Complex.neg_pi_lt_arg r3

  have hS_lt : S < 3 * Real.pi := by linarith
  have hS_gt : -3 * Real.pi < S := by linarith

  -- Key lemma: ‖x‖ * exp (arg x * I) = x
  have hnorm1 : (‖r1‖ : ℂ) ≠ 0 := by simp [hr1_ne]
  have hnorm2 : (‖r2‖ : ℂ) ≠ 0 := by simp [hr2_ne]
  have hnorm3 : (‖r3‖ : ℂ) ≠ 0 := by simp [hr3_ne]

  -- exp(I * S) = -1
  have hexp_S : Complex.exp (Complex.I * S) = -1 := by
    have h1 : Complex.exp (Complex.arg r1 * Complex.I) = r1 / ‖r1‖ := by
      have := Complex.norm_mul_exp_arg_mul_I r1
      field_simp [hnorm1] at this ⊢
      exact this
    have h2 : Complex.exp (Complex.arg r2 * Complex.I) = r2 / ‖r2‖ := by
      have := Complex.norm_mul_exp_arg_mul_I r2
      field_simp [hnorm2] at this ⊢
      exact this
    have h3 : Complex.exp (Complex.arg r3 * Complex.I) = r3 / ‖r3‖ := by
      have := Complex.norm_mul_exp_arg_mul_I r3
      field_simp [hnorm3] at this ⊢
      exact this
    simp only [hS_def]
    have hcast : (↑(Complex.arg r1 + Complex.arg r2 + Complex.arg r3) : ℂ) =
                 ↑(Complex.arg r1) + ↑(Complex.arg r2) + ↑(Complex.arg r3) := by push_cast; ring
    calc Complex.exp (Complex.I * ↑(Complex.arg r1 + Complex.arg r2 + Complex.arg r3))
        = Complex.exp (Complex.I * (↑(Complex.arg r1) + ↑(Complex.arg r2) + ↑(Complex.arg r3))) := by
            rw [hcast]
        _ = Complex.exp ((↑(Complex.arg r1) + ↑(Complex.arg r2) + ↑(Complex.arg r3)) * Complex.I) := by
            ring_nf
        _ = Complex.exp (↑(Complex.arg r1) * Complex.I + ↑(Complex.arg r2) * Complex.I +
            ↑(Complex.arg r3) * Complex.I) := by ring_nf
        _ = Complex.exp (↑(Complex.arg r1) * Complex.I) *
            Complex.exp (↑(Complex.arg r2) * Complex.I) *
            Complex.exp (↑(Complex.arg r3) * Complex.I) := by
            rw [Complex.exp_add, Complex.exp_add]
        _ = (r1 / ‖r1‖) * (r2 / ‖r2‖) * (r3 / ‖r3‖) := by rw [h1, h2, h3]
        _ = (r1 * r2 * r3) / ((‖r1‖ : ℂ) * ‖r2‖ * ‖r3‖) := by ring
        _ = (r1 * r2 * r3) / ‖r1 * r2 * r3‖ := by
            congr 1
            simp only [norm_mul]
            push_cast
            ring
        _ = -1 / ‖(-1 : ℂ)‖ := by rw [hprod]
        _ = -1 / 1 := by simp
        _ = -1 := by ring

  -- exp(I * S) = exp(I * π), so S = π + 2πn for some integer n
  have hexp_pi : Complex.exp (Complex.I * Real.pi) = -1 := by
    rw [mul_comm, Complex.exp_mul_I]
    simp [Complex.cos_pi, Complex.sin_pi]

  rw [← hexp_pi] at hexp_S
  rw [Complex.exp_eq_exp_iff_exists_int] at hexp_S
  obtain ⟨n, hn⟩ := hexp_S
  -- hn : I * S = I * π + n * (2 * π * I)

  -- Extract S = π + 2πn from the complex equation
  have hS_eq : S = Real.pi + 2 * Real.pi * n := by
    -- hn : I * S = I * π + n * (2 * π * I)
    -- Extract imaginary part: S = π + 2πn
    have hL : (Complex.I * S).im = S := by simp
    have hR : (Complex.I * Real.pi + n * (2 * Real.pi * Complex.I)).im =
               Real.pi + n * (2 * Real.pi) := by simp [mul_comm]
    have h : S = Real.pi + n * (2 * Real.pi) := by
      calc S = (Complex.I * S).im := hL.symm
        _ = (Complex.I * Real.pi + n * (2 * Real.pi * Complex.I)).im := by rw [hn]
        _ = Real.pi + n * (2 * Real.pi) := hR
    linarith

  -- From bounds and hS_eq, n ∈ {-1, 0}
  have hn_bound : n = -1 ∨ n = 0 := by
    rw [hS_eq] at hS_lt hS_gt
    have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    -- From hS_lt: π + 2πn < 3π, so 2πn < 2π, so n < 1 (since π > 0)
    -- From hS_gt: -3π < π + 2πn, so -4π < 2πn, so -2 < n
    have h1 : 2 * Real.pi * n < 2 * Real.pi := by linarith
    have h2 : -4 * Real.pi < 2 * Real.pi * n := by linarith
    have hpi2_pos : 0 < 2 * Real.pi := by linarith
    have hn_lt_real : (n : ℝ) < 1 := by nlinarith [sq_nonneg Real.pi]
    have hn_gt_real : (-2 : ℝ) < n := by nlinarith [sq_nonneg Real.pi]
    have hn_lt : n < 1 := by
      by_contra h_neg
      push_neg at h_neg
      have : (1 : ℝ) ≤ n := by exact_mod_cast h_neg
      linarith
    have hn_gt : -2 < n := by
      by_contra h_neg
      push_neg at h_neg
      have : (n : ℝ) ≤ -2 := by exact_mod_cast h_neg
      linarith
    omega

  -- Convert to the form k * π
  rcases hn_bound with rfl | rfl
  · -- n = -1, so S = π - 2π = -π
    use -1
    constructor
    · simp only [hS_eq, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      ring
    · right; rfl
  · -- n = 0, so S = π
    use 1
    constructor
    · simp only [hS_eq, Int.cast_zero, mul_zero, add_zero, Int.cast_one, one_mul]
    · left; rfl

/-- The interior angles of a triangle sum to π (the standard form) -/
theorem angle_sum_pi {A B C : ℂ} (h : NonCollinear A B C) :
    |angle_at B A C| + |angle_at C B A| + |angle_at A C B| = Real.pi := by
  sorry

/-- For non-collinear points with consistent orientation, angles are all same sign.
    This follows from angle_sum_signed: if sum = π, all angles must be positive;
    if sum = -π, all angles must be negative. -/
theorem NonCollinear.angles_same_sign {A B C : ℂ} (h : NonCollinear A B C) :
    (0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) ∨
    (angle_at B A C < 0 ∧ angle_at C B A < 0 ∧ angle_at A C B < 0) := by
  -- Get bounds on each angle: each is in (-π, π) strictly (not including endpoints)
  have h1_range := h.symm_AC.cycle.angle_in_range  -- -π < angle_at B A C < π
  have h2_range := h.symm_AC.angle_in_range        -- -π < angle_at C B A < π
  have h3_range := h.cycle.symm_AC.angle_in_range  -- -π < angle_at A C B < π
  -- Each angle is nonzero
  have h1_ne : angle_at B A C ≠ 0 := h.symm_AC.cycle.arg_ne_zero_pi.1
  have h2_ne : angle_at C B A ≠ 0 := h.symm_AC.arg_ne_zero_pi.1
  have h3_ne : angle_at A C B ≠ 0 := h.cycle.symm_AC.arg_ne_zero_pi.1
  -- From angle_sum_signed, the sum is ±π
  obtain ⟨k, hsum, hk⟩ := angle_sum_signed h
  -- Case split on k
  rcases hk with rfl | rfl
  · -- k = 1: sum = π
    -- If sum = π and each angle is in (-π, π), all must be positive
    -- (if any were ≤ 0, two others would need to sum to > π, each being < π)
    have hsum_eq : angle_at B A C + angle_at C B A + angle_at A C B = Real.pi := by
      simp only [Int.cast_one, one_mul] at hsum; exact hsum
    left
    constructor
    · -- angle_at B A C > 0
      by_contra h1_le
      push_neg at h1_le
      have h1_lt : angle_at B A C < 0 := lt_of_le_of_ne h1_le h1_ne
      -- angle2 + angle3 = π - angle1 > π (since angle1 < 0)
      have hsum23 : angle_at C B A + angle_at A C B > Real.pi := by linarith
      -- If both angle2, angle3 ≤ 0, their sum ≤ 0 < π, contradiction
      -- So at least one is positive
      -- If angle2 ≤ 0, then angle3 > π (since angle3 > π - angle2 ≥ π), contradiction with angle3 < π
      -- Similarly for angle3 ≤ 0
      rcases le_or_lt (angle_at C B A) 0 with h2_le | h2_gt
      · have h2_lt : angle_at C B A < 0 := lt_of_le_of_ne h2_le h2_ne
        have h3_gt_pi : angle_at A C B > Real.pi := by linarith
        exact absurd h3_gt_pi (not_lt.mpr (le_of_lt h3_range.2))
      · rcases le_or_lt (angle_at A C B) 0 with h3_le | h3_gt
        · have h3_lt : angle_at A C B < 0 := lt_of_le_of_ne h3_le h3_ne
          have h2_gt_pi : angle_at C B A > Real.pi := by linarith
          exact absurd h2_gt_pi (not_lt.mpr (le_of_lt h2_range.2))
        · -- Both angle2 > 0 and angle3 > 0, but angle2 + angle3 > π
          -- Since angle2 < π and angle3 < π, this is possible
          -- But this contradicts our assumption that angle1 < 0
          -- Actually, this case shouldn't happen: if angle2 + angle3 > π with both < π,
          -- and sum = π, then angle1 = π - (angle2 + angle3) < 0, which is consistent.
          -- The issue is we need to derive contradiction differently.
          -- Key: angle2 + angle3 > π with angle2 < π, angle3 < π means
          -- at least one of them is > π/2. But together with angle1 < 0 and sum = π,
          -- actually there's no direct contradiction from bounds alone.
          -- We need the geometric constraint that signs are consistent.
          -- For now, accept this may need the cross-product argument.
          sorry
    constructor
    · by_contra h2_le; push_neg at h2_le
      have h2_lt : angle_at C B A < 0 := lt_of_le_of_ne h2_le h2_ne
      have hsum13 : angle_at B A C + angle_at A C B > Real.pi := by linarith
      rcases le_or_lt (angle_at B A C) 0 with h1_le | h1_gt
      · have h1_lt : angle_at B A C < 0 := lt_of_le_of_ne h1_le h1_ne
        have h3_gt_pi : angle_at A C B > Real.pi := by linarith
        exact absurd h3_gt_pi (not_lt.mpr (le_of_lt h3_range.2))
      · rcases le_or_lt (angle_at A C B) 0 with h3_le | h3_gt
        · have h3_lt : angle_at A C B < 0 := lt_of_le_of_ne h3_le h3_ne
          have h1_gt_pi : angle_at B A C > Real.pi := by linarith
          exact absurd h1_gt_pi (not_lt.mpr (le_of_lt h1_range.2))
        · sorry
    · by_contra h3_le; push_neg at h3_le
      have h3_lt : angle_at A C B < 0 := lt_of_le_of_ne h3_le h3_ne
      have hsum12 : angle_at B A C + angle_at C B A > Real.pi := by linarith
      rcases le_or_lt (angle_at B A C) 0 with h1_le | h1_gt
      · have h1_lt : angle_at B A C < 0 := lt_of_le_of_ne h1_le h1_ne
        have h2_gt_pi : angle_at C B A > Real.pi := by linarith
        exact absurd h2_gt_pi (not_lt.mpr (le_of_lt h2_range.2))
      · rcases le_or_lt (angle_at C B A) 0 with h2_le | h2_gt
        · have h2_lt : angle_at C B A < 0 := lt_of_le_of_ne h2_le h2_ne
          have h1_gt_pi : angle_at B A C > Real.pi := by linarith
          exact absurd h1_gt_pi (not_lt.mpr (le_of_lt h1_range.2))
        · sorry
  · -- k = -1: sum = -π (symmetric argument)
    have hsum_eq : angle_at B A C + angle_at C B A + angle_at A C B = -Real.pi := by
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hsum; exact hsum
    right
    constructor
    · by_contra h1_ge; push_neg at h1_ge
      have h1_gt : 0 < angle_at B A C := lt_of_le_of_ne h1_ge h1_ne.symm
      have hsum23 : angle_at C B A + angle_at A C B < -Real.pi := by linarith
      rcases le_or_lt 0 (angle_at C B A) with h2_ge | h2_lt
      · have h2_gt : 0 < angle_at C B A := lt_of_le_of_ne h2_ge h2_ne.symm
        have h3_lt_neg_pi : angle_at A C B < -Real.pi := by linarith
        exact absurd h3_lt_neg_pi (not_lt.mpr (le_of_lt h3_range.1))
      · rcases le_or_lt 0 (angle_at A C B) with h3_ge | h3_lt
        · have h3_gt : 0 < angle_at A C B := lt_of_le_of_ne h3_ge h3_ne.symm
          have h2_lt_neg_pi : angle_at C B A < -Real.pi := by linarith
          exact absurd h2_lt_neg_pi (not_lt.mpr (le_of_lt h2_range.1))
        · sorry
    constructor
    · by_contra h2_ge; push_neg at h2_ge
      have h2_gt : 0 < angle_at C B A := lt_of_le_of_ne h2_ge h2_ne.symm
      have hsum13 : angle_at B A C + angle_at A C B < -Real.pi := by linarith
      rcases le_or_lt 0 (angle_at B A C) with h1_ge | h1_lt
      · have h1_gt : 0 < angle_at B A C := lt_of_le_of_ne h1_ge h1_ne.symm
        have h3_lt_neg_pi : angle_at A C B < -Real.pi := by linarith
        exact absurd h3_lt_neg_pi (not_lt.mpr (le_of_lt h3_range.1))
      · rcases le_or_lt 0 (angle_at A C B) with h3_ge | h3_lt
        · have h3_gt : 0 < angle_at A C B := lt_of_le_of_ne h3_ge h3_ne.symm
          have h1_lt_neg_pi : angle_at B A C < -Real.pi := by linarith
          exact absurd h1_lt_neg_pi (not_lt.mpr (le_of_lt h1_range.1))
        · sorry
    · by_contra h3_ge; push_neg at h3_ge
      have h3_gt : 0 < angle_at A C B := lt_of_le_of_ne h3_ge h3_ne.symm
      have hsum12 : angle_at B A C + angle_at C B A < -Real.pi := by linarith
      rcases le_or_lt 0 (angle_at B A C) with h1_ge | h1_lt
      · have h1_gt : 0 < angle_at B A C := lt_of_le_of_ne h1_ge h1_ne.symm
        have h2_lt_neg_pi : angle_at C B A < -Real.pi := by linarith
        exact absurd h2_lt_neg_pi (not_lt.mpr (le_of_lt h2_range.1))
      · rcases le_or_lt 0 (angle_at C B A) with h2_ge | h2_lt
        · have h2_gt : 0 < angle_at C B A := lt_of_le_of_ne h2_ge h2_ne.symm
          have h1_lt_neg_pi : angle_at B A C < -Real.pi := by linarith
          exact absurd h1_lt_neg_pi (not_lt.mpr (le_of_lt h1_range.1))
        · sorry

/-- When angles α, β, γ are the trisected interior angles of a triangle,
    they sum to π/3 (for positive orientation) -/
theorem trisected_angles_sum {A B C : ℂ} (h : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    angle_at B A C / 3 + angle_at C B A / 3 + angle_at A C B / 3 = Real.pi / 3 := by
  have hsum := angle_sum_pi h
  have h1 : angle_at B A C + angle_at C B A + angle_at A C B = Real.pi := by
    simp only [abs_of_pos hpos.1, abs_of_pos hpos.2.1, abs_of_pos hpos.2.2] at hsum
    exact hsum
  linarith

/-- When angles are negative (clockwise orientation), trisected angles sum to -π/3 -/
theorem trisected_angles_sum_neg {A B C : ℂ} (h : NonCollinear A B C)
    (hneg : angle_at B A C < 0 ∧ angle_at C B A < 0 ∧ angle_at A C B < 0) :
    angle_at B A C / 3 + angle_at C B A / 3 + angle_at A C B / 3 = -Real.pi / 3 := by
  have hsum := angle_sum_pi h
  have h1 : angle_at B A C + angle_at C B A + angle_at A C B = -Real.pi := by
    simp only [abs_of_neg hneg.1, abs_of_neg hneg.2.1, abs_of_neg hneg.2.2] at hsum
    linarith
  linarith

/-- Each angle is bounded: |angle| < π for interior angle -/
theorem angle_bound {A B C : ℂ} (h : NonCollinear A B C) :
    |angle_at B A C| < Real.pi := by
  have hrange := h.symm_AC.cycle.angle_in_range
  rw [abs_lt]
  exact ⟨hrange.1, hrange.2⟩

/-- Each trisected angle is bounded: |α/3| < π/3 for interior angle α -/
theorem trisected_angle_bound {A B C : ℂ} (h : NonCollinear A B C) :
    |angle_at B A C / 3| < Real.pi / 3 := by
  have hbound := angle_bound h
  rw [abs_div, abs_of_pos (by positivity : (3 : ℝ) > 0)]
  exact div_lt_div_of_pos_right hbound (by positivity)

end Morley
