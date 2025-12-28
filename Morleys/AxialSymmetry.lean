/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Exponential
import Morleys.Rotation
import Morleys.Triangle

/-!
# Axial Symmetry (Reflection) in the Complex Plane

This file defines axial symmetry (reflection about a line) in the complex plane
and establishes the key connection to rotations used in proving Morley's theorem.

## Main definitions

* `Morley.axialSymmetry` : Reflection of a point across a line through z1 and z2
* `Morley.line` : The set of points on a line through z1 and z2

## Main results

* `axialSymmetry_involutive` : Reflection is an involution (applying twice gives identity)
* `axialSymmetry_preserves_dist` : Reflection preserves distances from points on the axis
* `img_r_sym` : Key lemma relating reflection to rotation by twice the angle

## Reference

This follows the Isabelle AFP proof in Complex_Axial_Symmetry.thy and Morley.thy.
The key insight is that for a point z not on line z1-z2:
  axialSymmetry z1 z2 z = rotation z1 (2 * angle_at z z1 z2) z
-/

namespace Morley

open Complex Real

/-! ## Axial Symmetry Definition -/

/-- The α coefficient for axial symmetry: (z1 - z2) / (conj z1 - conj z2).
    This has norm 1. -/
noncomputable def axialAlpha (z1 z2 : ℂ) : ℂ :=
  (z1 - z2) / (starRingEnd ℂ z1 - starRingEnd ℂ z2)

/-- The β coefficient for axial symmetry: (z2 * conj z1 - z1 * conj z2) / (conj z1 - conj z2) -/
noncomputable def axialBeta (z1 z2 : ℂ) : ℂ :=
  (z2 * starRingEnd ℂ z1 - z1 * starRingEnd ℂ z2) / (starRingEnd ℂ z1 - starRingEnd ℂ z2)

/-- Axial symmetry (reflection) across the line through z1 and z2.
    Formula: conj(z) * α + β where α = (z1-z2)/(conj z1 - conj z2)
    and β = (z2*conj z1 - z1*conj z2)/(conj z1 - conj z2).

    This reflects point z across the line passing through z1 and z2. -/
noncomputable def axialSymmetry (z1 z2 z : ℂ) : ℂ :=
  starRingEnd ℂ z * axialAlpha z1 z2 + axialBeta z1 z2

/-- Line through two points in ℂ -/
def line (z1 z2 : ℂ) : Set ℂ :=
  {z | ∃ t : ℝ, z - z1 = t • (z2 - z1)}

/-! ## Basic Properties of α and β -/

/-- The denominator conj z1 - conj z2 is nonzero when z1 ≠ z2 -/
theorem conj_diff_ne_zero {z1 z2 : ℂ} (h : z1 ≠ z2) :
    starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := by
  simp only [ne_eq, sub_eq_zero]
  intro heq
  apply h
  have : starRingEnd ℂ (starRingEnd ℂ z1) = starRingEnd ℂ (starRingEnd ℂ z2) := by rw [heq]
  simp only [RingHomCompTriple.comp_apply] at this
  exact this

/-- |α| = 1: The α coefficient has unit norm -/
theorem norm_axialAlpha_eq_one {z1 z2 : ℂ} (h : z1 ≠ z2) : ‖axialAlpha z1 z2‖ = 1 := by
  simp only [axialAlpha]
  rw [norm_div]
  have h1 : ‖z1 - z2‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have h2 : starRingEnd ℂ z1 - starRingEnd ℂ z2 = starRingEnd ℂ (z1 - z2) := by
    simp [RingHom.map_sub]
  rw [h2, Complex.norm_conj]
  exact div_self h1

/-- α * conj(α) = 1 -/
theorem axialAlpha_mul_conj {z1 z2 : ℂ} (h : z1 ≠ z2) :
    axialAlpha z1 z2 * starRingEnd ℂ (axialAlpha z1 z2) = 1 := by
  have hn := norm_axialAlpha_eq_one h
  have hne : axialAlpha z1 z2 ≠ 0 := by
    simp only [axialAlpha]
    apply div_ne_zero
    · exact sub_ne_zero.mpr h
    · exact conj_diff_ne_zero h
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.normSq_eq_norm_sq, hn]
  simp

/-- Key identity: α * conj(β) + β = 0 -/
theorem axialAlpha_beta_identity {z1 z2 : ℂ} (h : z1 ≠ z2) :
    axialAlpha z1 z2 * starRingEnd ℂ (axialBeta z1 z2) + axialBeta z1 z2 = 0 := by
  unfold axialAlpha axialBeta
  have hdenom : starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := conj_diff_ne_zero h
  have hdenom' : z1 - z2 ≠ 0 := sub_ne_zero.mpr h
  -- conj of β: conj((z2*conj z1 - z1*conj z2)/(conj z1 - conj z2))
  --          = (conj z2 * z1 - conj z1 * z2)/(z1 - z2)
  have hconj_beta : starRingEnd ℂ ((z2 * starRingEnd ℂ z1 - z1 * starRingEnd ℂ z2) /
      (starRingEnd ℂ z1 - starRingEnd ℂ z2)) =
      (starRingEnd ℂ z2 * z1 - starRingEnd ℂ z1 * z2) / (z1 - z2) := by
    simp only [map_div₀, map_sub, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [hconj_beta]
  field_simp [hdenom, hdenom']
  ring

/-! ## Fixed Point Lemmas -/

/-- z1 is fixed by axial symmetry about the line through z1 and z2 -/
theorem axialSymmetry_z1_fixed {z1 z2 : ℂ} (h : z1 ≠ z2) :
    axialSymmetry z1 z2 z1 = z1 := by
  simp only [axialSymmetry, axialAlpha, axialBeta]
  have hdenom : starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := conj_diff_ne_zero h
  field_simp [hdenom]
  ring

/-- z2 is fixed by axial symmetry about the line through z1 and z2 -/
theorem axialSymmetry_z2_fixed {z1 z2 : ℂ} (h : z1 ≠ z2) :
    axialSymmetry z1 z2 z2 = z2 := by
  simp only [axialSymmetry, axialAlpha, axialBeta]
  have hdenom : starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := conj_diff_ne_zero h
  field_simp [hdenom]
  ring

/-! ## Involution Property -/

/-- Axial symmetry is an involution: applying it twice gives the identity -/
theorem axialSymmetry_involutive {z1 z2 : ℂ} (h : z1 ≠ z2) (z : ℂ) :
    axialSymmetry z1 z2 (axialSymmetry z1 z2 z) = z := by
  unfold axialSymmetry
  -- axialSymmetry z1 z2 (conj z * α + β) = conj(conj z * α + β) * α + β
  --   = (z * conj α + conj β) * α + β
  --   = z * conj α * α + conj β * α + β
  --   = z * 1 + (α * conj β + β)   [using α * conj α = 1]
  --   = z + 0 = z                   [using α * conj β + β = 0]
  have h1 := axialAlpha_mul_conj h
  have h2 := axialAlpha_beta_identity h
  -- Expand conj(conj z * α + β)
  have hexp : starRingEnd ℂ (starRingEnd ℂ z * axialAlpha z1 z2 + axialBeta z1 z2) =
      z * starRingEnd ℂ (axialAlpha z1 z2) + starRingEnd ℂ (axialBeta z1 z2) := by
    simp only [map_add, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [hexp]
  calc (z * starRingEnd ℂ (axialAlpha z1 z2) + starRingEnd ℂ (axialBeta z1 z2)) *
         axialAlpha z1 z2 + axialBeta z1 z2
      = z * starRingEnd ℂ (axialAlpha z1 z2) * axialAlpha z1 z2 +
        starRingEnd ℂ (axialBeta z1 z2) * axialAlpha z1 z2 + axialBeta z1 z2 := by ring
    _ = z * (axialAlpha z1 z2 * starRingEnd ℂ (axialAlpha z1 z2)) +
        (axialAlpha z1 z2 * starRingEnd ℂ (axialBeta z1 z2) + axialBeta z1 z2) := by ring
    _ = z * 1 + 0 := by rw [h1, h2]
    _ = z := by ring

/-! ## Distance Preservation -/

/-- Axial symmetry preserves distances between any two points -/
theorem axialSymmetry_dist_inv {z1 z2 : ℂ} (h : z1 ≠ z2) (a b : ℂ) :
    ‖a - b‖ = ‖axialSymmetry z1 z2 a - axialSymmetry z1 z2 b‖ := by
  have hα := norm_axialAlpha_eq_one h
  -- axialSymmetry a - axialSymmetry b = (conj a * α + β) - (conj b * α + β) = (conj a - conj b) * α
  have hsimp : axialSymmetry z1 z2 a - axialSymmetry z1 z2 b =
      (starRingEnd ℂ a - starRingEnd ℂ b) * axialAlpha z1 z2 := by
    unfold axialSymmetry
    ring
  rw [hsimp, norm_mul, hα, mul_one]
  rw [← Complex.norm_conj (a - b)]
  congr 1
  simp only [map_sub]

/-- Axial symmetry preserves distance from z1 -/
theorem axialSymmetry_dist_from_z1 {z1 z2 : ℂ} (h : z1 ≠ z2) (z : ℂ) :
    ‖z1 - z‖ = ‖z1 - axialSymmetry z1 z2 z‖ := by
  have hfix := axialSymmetry_z1_fixed h
  calc ‖z1 - z‖ = ‖axialSymmetry z1 z2 z1 - axialSymmetry z1 z2 z‖ :=
        axialSymmetry_dist_inv h z1 z
    _ = ‖z1 - axialSymmetry z1 z2 z‖ := by rw [hfix]

/-- Axial symmetry preserves distance from z2 -/
theorem axialSymmetry_dist_from_z2 {z1 z2 : ℂ} (h : z1 ≠ z2) (z : ℂ) :
    ‖z2 - z‖ = ‖z2 - axialSymmetry z1 z2 z‖ := by
  have hfix := axialSymmetry_z2_fixed h
  calc ‖z2 - z‖ = ‖axialSymmetry z1 z2 z2 - axialSymmetry z1 z2 z‖ :=
        axialSymmetry_dist_inv h z2 z
    _ = ‖z2 - axialSymmetry z1 z2 z‖ := by rw [hfix]

/-! ## Symmetry of the Definition -/

/-- Axial symmetry is symmetric in z1 and z2 -/
theorem axialSymmetry_symm {z1 z2 : ℂ} (h : z1 ≠ z2) (z : ℂ) :
    axialSymmetry z1 z2 z = axialSymmetry z2 z1 z := by
  simp only [axialSymmetry, axialAlpha, axialBeta]
  have hdenom1 : starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := conj_diff_ne_zero h
  have hdenom2 : starRingEnd ℂ z2 - starRingEnd ℂ z1 ≠ 0 := conj_diff_ne_zero h.symm
  field_simp [hdenom1, hdenom2]
  ring

/-! ## Connection to Angle

The key angle properties we need are:
1. `angle_at_axialSymmetry_neg`: Reflection negates the angle
2. `angle_sum`: angle_at z z1 w = angle_at z z1 z2 + angle_at z2 z1 w
3. `angle_at_to_reflected`: angle from z to its reflection equals 2 * original angle

Proof sketch for angle_at_to_reflected:
  angle_at z z1 (axialSymmetry z) = angle_at z z1 z2 + angle_at z2 z1 (axialSymmetry z)
                                   = angle_at z z1 z2 + angle_at z z1 z2  [using angle_symmetry_eq]
                                   = 2 * angle_at z z1 z2
-/

/-- The angle flips sign under reflection (for points not on the line).

    Proof outline from Isabelle AFP (Complex_Axial_Symmetry.thy, angle_symmetry_eq):
    1. Either angle_at z z1 z2 = angle_at (axialSymmetry z) z1 z2, or they are negatives
    2. The "equal" case implies z = axialSymmetry z (by uniqueness)
    3. But z = axialSymmetry z only for points on the line
    4. So for z not on line, the angles are negatives -/
theorem angle_at_axialSymmetry_neg {z1 z2 z : ℂ} (h12 : z1 ≠ z2)
    (hz1 : z ≠ z1) (hz2 : z ≠ z2) (hz_line : z ∉ line z1 z2) :
    angle_at (axialSymmetry z1 z2 z) z1 z2 = -angle_at z z1 z2 := by
  -- Step 1: Either equal or negatives (by congruent triangle argument)
  -- Step 2: If equal, then z = axialSymmetry z (by same distance and same angle)
  -- Step 3: z = axialSymmetry z implies z is on line (by axialSymmetry_eq_line)
  -- Step 4: Contradiction with hz_line
  sorry

/-! ## Points on the Line -/

/-- A point on the line is fixed by axial symmetry.

    Proof outline from Isabelle AFP (Complex_Axial_Symmetry.thy, line_is_inv):
    1. For z on line z1-z2 (and z ≠ z1, z ≠ z2), angle_at z z1 z2 = 0 or π
    2. Negating 0 gives 0, and -π ≡ π (mod 2π)
    3. So angle_at (axialSymmetry z) z1 z2 = angle_at z z1 z2
    4. Combined with equal distances, by uniqueness z = axialSymmetry z -/
theorem axialSymmetry_line_fixed {z1 z2 z : ℂ} (h12 : z1 ≠ z2)
    (hz1 : z ≠ z1) (hz2 : z ≠ z2) (hz_line : z ∈ line z1 z2) :
    axialSymmetry z1 z2 z = z := by
  -- Step 1: z on line implies angle is 0 or π
  -- Step 2: -0 = 0 and -π = π (as angles)
  -- Step 3: By angle_symmetry_eq_imp, angles are equal
  -- Step 4: By uniqueness (same distance and angle from z1), z = axialSymmetry z
  sorry

/-! ## The Key Lemma: img_r_sym

This is the critical connection between reflection and rotation that enables
the proof of Morley's theorem.

**Proof Strategy:**
1. Both axialSymmetry and rotation preserve distance from z1:
   - `axialSymmetry_dist_from_z1`: ‖z1 - z‖ = ‖z1 - axialSymmetry z1 z2 z‖
   - `rotation_dist_center`: ‖rotation z1 θ z - z1‖ = ‖z - z1‖

2. The angle from z to its reflection around z1 equals 2 * angle_at z z1 z2:
   - By angle additivity: angle_at z z1 (axialSymmetry z) = angle_at z z1 z2 + angle_at z2 z1 (axialSymmetry z)
   - By angle_at_axialSymmetry_neg: angle_at (axialSymmetry z) z1 z2 = -angle_at z z1 z2
   - Combining: angle_at z z1 (axialSymmetry z) = 2 * angle_at z z1 z2

3. The angle from z to its rotation around z1 equals θ (the rotation angle).

4. A point is uniquely determined by its distance from z1 and angle from z.
   Therefore axialSymmetry z = rotation z1 (2 * angle_at z z1 z2) z. -/
theorem img_r_sym {z1 z2 z : ℂ} (h12 : z1 ≠ z2) (hz_line : z ∉ line z1 z2) :
    axialSymmetry z1 z2 z = rotation z1 (2 * angle_at z z1 z2) z := by
  -- Step 1: Same distance from z1
  have hdist1 : ‖z1 - z‖ = ‖z1 - axialSymmetry z1 z2 z‖ := axialSymmetry_dist_from_z1 h12 z
  have hdist2 : ‖rotation z1 (2 * angle_at z z1 z2) z - z1‖ = ‖z - z1‖ := rotation_dist_center z1 _ z
  -- Step 2: The angle from z to the reflection equals 2 * angle_at z z1 z2
  -- This requires angle_sum and angle_at_axialSymmetry_neg
  -- Step 3: The angle from z to the rotation equals 2 * angle_at z z1 z2 (by definition)
  -- Step 4: Uniqueness implies equality
  sorry

end Morley
