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
  sorry

/-- The interior angles of a triangle sum to π (the standard form) -/
theorem angle_sum_pi {A B C : ℂ} (h : NonCollinear A B C) :
    |angle_at B A C| + |angle_at C B A| + |angle_at A C B| = Real.pi := by
  sorry

/-- For non-collinear points with consistent orientation, angles are all same sign -/
theorem NonCollinear.angles_same_sign {A B C : ℂ} (h : NonCollinear A B C) :
    (0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) ∨
    (angle_at B A C < 0 ∧ angle_at C B A < 0 ∧ angle_at A C B < 0) := by
  sorry

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
