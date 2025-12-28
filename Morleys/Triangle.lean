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
  sorry

/-- Non-collinear is cyclic -/
theorem NonCollinear.cycle {A B C : ℂ} (h : NonCollinear A B C) : NonCollinear B C A := by
  sorry

/-- angle_at is well-defined when points are distinct -/
theorem angle_at_well_defined {A B C : ℂ} (hAB : A ≠ B) (hCB : C ≠ B) :
    (A - B) / (C - B) ≠ 0 := by
  apply div_ne_zero
  · exact sub_ne_zero.mpr hAB
  · exact sub_ne_zero.mpr hCB

/-- For non-collinear points, the ratio (A - B) / (C - B) is not a real number -/
theorem NonCollinear.ratio_not_real {A B C : ℂ} (h : NonCollinear A B C) :
    ∀ r : ℝ, (A - B) / (C - B) ≠ r := by
  sorry

/-- For non-collinear points, the argument is not 0 or π -/
theorem NonCollinear.arg_ne_zero_pi {A B C : ℂ} (h : NonCollinear A B C) :
    Complex.arg ((A - B) / (C - B)) ≠ 0 ∧ Complex.arg ((A - B) / (C - B)) ≠ Real.pi := by
  sorry

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
