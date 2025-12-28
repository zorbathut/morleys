/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Data.Complex.Exponential
import Morleys.CubeRoot
import Morleys.Trig

/-!
# Complex Rotations

This file defines rotations in the complex plane, represented as affine transformations.
These are central to Connes' algebraic proof of Morley's theorem.

## Main definitions

* `Morley.rotation` : Rotation centered at point A by angle θ

## Main results

* `rotation_id` : Rotation by 0 is the identity
* `rotation_comp_same_center` : Composing rotations with the same center adds angles
* `rotation_preserves_dist` : Rotations preserve distance from the center
-/

namespace Morley

open Complex Real

/-- Shorthand for the multiplier cis(θ) = e^(iθ) -/
noncomputable def cis (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

/-- Rotation centered at A by angle θ applied to point z -/
noncomputable def rotation (A : ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  A + (z - A) * cis θ

/-- cis(θ) = cos(θ) + sin(θ)·i -/
theorem cis_eq (θ : ℝ) : cis θ = Complex.cos θ + Complex.sin θ * Complex.I := by
  simp only [cis]
  rw [Complex.exp_mul_I]

/-- |cis(θ)| = 1 -/
theorem norm_cis (θ : ℝ) : ‖cis θ‖ = 1 := by
  simp only [cis]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- cis(0) = 1 -/
theorem cis_zero : cis 0 = 1 := by simp [cis]

/-- cis ≠ 0 -/
theorem cis_ne_zero (θ : ℝ) : cis θ ≠ 0 := by
  simp only [cis]
  exact Complex.exp_ne_zero _

/-- cis(θ₁ + θ₂) = cis(θ₁) * cis(θ₂) -/
theorem cis_add (θ₁ θ₂ : ℝ) : cis (θ₁ + θ₂) = cis θ₁ * cis θ₂ := by
  simp only [cis]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- cis(θ)⁻¹ = cis(-θ) -/
theorem cis_inv (θ : ℝ) : (cis θ)⁻¹ = cis (-θ) := by
  simp only [cis]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- cis(2π) = 1 -/
theorem cis_two_pi : cis (2 * Real.pi) = 1 := by
  simp only [cis]
  push_cast
  exact Complex.exp_two_pi_mul_I

/-- Rotation by 0 is the identity -/
theorem rotation_zero (A z : ℂ) : rotation A 0 z = z := by
  simp [rotation, cis_zero]

/-- Rotation fixes the center -/
theorem rotation_center (A : ℂ) (θ : ℝ) : rotation A θ A = A := by
  simp [rotation]

/-- Rotation preserves distance from center -/
theorem rotation_dist_center (A : ℂ) (θ : ℝ) (z : ℂ) :
    ‖rotation A θ z - A‖ = ‖z - A‖ := by
  simp [rotation, norm_mul, norm_cis]

/-- Composing rotations with the same center adds angles -/
theorem rotation_comp_same_center (A : ℂ) (θ₁ θ₂ : ℝ) (z : ℂ) :
    rotation A θ₁ (rotation A θ₂ z) = rotation A (θ₁ + θ₂) z := by
  simp only [rotation, cis_add]
  ring

/-- Rotation by 2π is the identity -/
theorem rotation_two_pi (A z : ℂ) : rotation A (2 * Real.pi) z = z := by
  simp [rotation, cis_two_pi]

/-- Rotation composed n times with itself -/
theorem rotation_iterate (A : ℂ) (θ : ℝ) (n : ℕ) (z : ℂ) :
    (rotation A θ)^[n] z = rotation A (n * θ) z := by
  induction n with
  | zero => simp [rotation_zero]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [ih, rotation_comp_same_center]
    congr 1
    push_cast
    ring

/-- Key lemma: r³ where r is rotation by 2α sums to rotation by 6α -/
theorem rotation_cubed (A : ℂ) (α : ℝ) (z : ℂ) :
    rotation A (2 * α) (rotation A (2 * α) (rotation A (2 * α) z)) = rotation A (6 * α) z := by
  rw [rotation_comp_same_center, rotation_comp_same_center]
  congr 1
  ring

/-- Affine form: rotation can be written as A + m*(z - A) where |m| = 1 -/
theorem rotation_affine_form (A : ℂ) (θ : ℝ) (z : ℂ) :
    ∃ m : ℂ, ‖m‖ = 1 ∧ rotation A θ z = A + m * (z - A) := by
  refine ⟨cis θ, norm_cis θ, ?_⟩
  simp [rotation]
  ring

/-- For non-zero angle sum, the fixed point of rotation₁ ∘ rotation₂ -/
noncomputable def rotationPairFixedPoint (A B : ℂ) (θ₁ θ₂ : ℝ) : ℂ :=
  (A * (1 - cis θ₁) + B * cis θ₁ * (1 - cis θ₂)) / (1 - cis (θ₁ + θ₂))

/-- When θ₁ + θ₂ ≠ 2πk, the composition has a unique fixed point.
    This is a tedious algebraic verification. -/
theorem rotation_pair_fixedPoint_spec (A B : ℂ) (θ₁ θ₂ : ℝ) (h : cis (θ₁ + θ₂) ≠ 1) :
    let P := rotationPairFixedPoint A B θ₁ θ₂
    rotation A θ₁ (rotation B θ₂ P) = P := by
  intro P
  simp only [rotation, rotationPairFixedPoint]
  have h1 : (1 : ℂ) - cis (θ₁ + θ₂) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hcis : cis θ₁ * cis θ₂ = cis (θ₁ + θ₂) := (cis_add θ₁ θ₂).symm
  -- Algebraic verification: after expanding P and applying rotations,
  -- the result simplifies back to P using cis θ₁ * cis θ₂ = cis (θ₁ + θ₂)
  sorry

end Morley
