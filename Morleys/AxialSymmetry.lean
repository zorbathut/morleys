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

/-- Key algebraic identity: the ratio for the reflected point equals the conjugate of the original ratio.
    This is the core of the angle negation proof. -/
theorem axialSymmetry_ratio_eq_conj {z1 z2 z : ℂ} (h12 : z1 ≠ z2) :
    (axialSymmetry z1 z2 z - z1) / (z2 - z1) =
    starRingEnd ℂ ((z - z1) / (z2 - z1)) := by
  -- From axialSymmetry z1 z2 z1 = z1, we have conj(z1) * α + β = z1
  -- So: axialSymmetry z - z1 = conj(z) * α + β - (conj(z1) * α + β)
  --                         = (conj(z) - conj(z1)) * α = conj(z - z1) * α
  have hα := axialSymmetry_z1_fixed h12
  -- Express axialSymmetry z - z1
  have hdiff : axialSymmetry z1 z2 z - z1 = starRingEnd ℂ (z - z1) * axialAlpha z1 z2 := by
    have : axialSymmetry z1 z2 z - axialSymmetry z1 z2 z1 =
        (starRingEnd ℂ z - starRingEnd ℂ z1) * axialAlpha z1 z2 := by
      unfold axialSymmetry
      ring
    rw [hα] at this
    rw [this, map_sub]
  have hdenom := conj_diff_ne_zero h12
  have hdenom2 : z2 - z1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have hconj21 : starRingEnd ℂ z2 - starRingEnd ℂ z1 ≠ 0 := conj_diff_ne_zero h12.symm
  rw [hdiff]
  -- α = (z1 - z2) / conj(z1 - z2)
  -- We compute: conj(z-z1) * α / (z2-z1)
  -- = conj(z-z1) * (z1-z2) / (conj(z1-z2) * (z2-z1))
  -- Key: (z1-z2)/(z2-z1) = -1 and conj(z1-z2) = -conj(z2-z1)
  -- So: = conj(z-z1) * (-1) / (-conj(z2-z1))
  --     = conj(z-z1) / conj(z2-z1)
  --     = conj((z-z1)/(z2-z1))
  calc starRingEnd ℂ (z - z1) * axialAlpha z1 z2 / (z2 - z1)
      = starRingEnd ℂ (z - z1) * ((z1 - z2) / (starRingEnd ℂ z1 - starRingEnd ℂ z2)) / (z2 - z1) := rfl
    _ = starRingEnd ℂ (z - z1) * (z1 - z2) / ((starRingEnd ℂ z1 - starRingEnd ℂ z2) * (z2 - z1)) := by
        field_simp [hdenom, hdenom2]
    _ = starRingEnd ℂ (z - z1) * (-(z2 - z1)) / ((-(starRingEnd ℂ z2 - starRingEnd ℂ z1)) * (z2 - z1)) := by
        ring_nf
    _ = starRingEnd ℂ (z - z1) * (-(z2 - z1)) / (-(starRingEnd ℂ z2 - starRingEnd ℂ z1) * (z2 - z1)) := rfl
    _ = starRingEnd ℂ (z - z1) / (starRingEnd ℂ z2 - starRingEnd ℂ z1) := by
        have h1 : (-(z2 - z1) : ℂ) / (-(starRingEnd ℂ z2 - starRingEnd ℂ z1) * (z2 - z1)) =
                  1 / (starRingEnd ℂ z2 - starRingEnd ℂ z1) := by
          field_simp [hdenom2, hconj21]
        rw [mul_div_assoc, h1, mul_one_div]
    _ = starRingEnd ℂ (z - z1) / starRingEnd ℂ (z2 - z1) := by simp only [map_sub]
    _ = starRingEnd ℂ ((z - z1) / (z2 - z1)) := by rw [map_div₀]

/-- The angle flips sign under reflection (for points not on the line).

    Proof: The ratio (axialSymmetry z - z1)/(z2 - z1) equals conj((z - z1)/(z2 - z1)),
    and arg(conj(w)) = -arg(w) for non-real w. -/
theorem angle_at_axialSymmetry_neg {z1 z2 z : ℂ} (h12 : z1 ≠ z2)
    (hz1 : z ≠ z1) (_hz2 : z ≠ z2) (hz_line : z ∉ line z1 z2) :
    angle_at (axialSymmetry z1 z2 z) z1 z2 = -angle_at z z1 z2 := by
  -- First, show the reflected point is also distinct from z1 and z2
  have hsym_ne_z1 : axialSymmetry z1 z2 z ≠ z1 := by
    intro heq
    -- If axialSymmetry z = z1, then by involutive property, z = axialSymmetry z1 = z1
    have : z = axialSymmetry z1 z2 (axialSymmetry z1 z2 z) := (axialSymmetry_involutive h12 z).symm
    rw [heq, axialSymmetry_z1_fixed h12] at this
    exact hz1 this
  -- Use the key algebraic identity
  have hratio := axialSymmetry_ratio_eq_conj h12 (z := z)
  -- angle_at (axialSymmetry z) z1 z2 = arg((axialSymmetry z - z1)/(z2 - z1))
  unfold angle_at
  rw [hratio]
  -- Now we need arg(conj(w)) = -arg(w) for w not on negative real axis
  -- The ratio (z - z1)/(z2 - z1) is non-real because z ∉ line z1 z2
  set w := (z - z1) / (z2 - z1) with hw_def
  -- w ≠ 0
  have hw_ne : w ≠ 0 := by
    simp only [hw_def]
    exact div_ne_zero (sub_ne_zero.mpr hz1) (sub_ne_zero.mpr h12.symm)
  -- w is not real (since z is not on the line through z1 and z2)
  have hw_not_real : ∀ r : ℝ, w ≠ r := by
    intro r hr
    apply hz_line
    -- If (z - z1)/(z2 - z1) = r (real), then z - z1 = r * (z2 - z1)
    -- So z = z1 + r * (z2 - z1), meaning z is on the line
    simp only [line, Set.mem_setOf_eq]
    use r
    have h21 : z2 - z1 ≠ 0 := sub_ne_zero.mpr h12.symm
    have heq : z - z1 = w * (z2 - z1) := by
      simp only [hw_def]
      field_simp [h21]
    rw [heq, hr]
    simp only [Complex.real_smul]
  -- In particular, w.im ≠ 0 (so w is not on real axis)
  have hw_im_ne : w.im ≠ 0 := by
    intro him
    have hreal : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    exact hw_not_real w.re hreal
  -- arg(conj w) = -arg(w) when w.im ≠ 0
  -- Use Complex.arg_conj with the fact that arg w ≠ π (since w.im ≠ 0)
  have harg_ne_pi : Complex.arg w ≠ Real.pi := by
    intro harg
    rw [Complex.arg_eq_pi_iff] at harg
    exact hw_im_ne harg.2
  simp only [Complex.arg_conj, if_neg harg_ne_pi]

/-! ## Points on the Line -/

/-- A point on the line is fixed by axial symmetry.

    Direct computation: if z = z1 + t*(z2-z1) for real t, then
    axialSymmetry z1 z2 z = z. -/
theorem axialSymmetry_line_fixed {z1 z2 z : ℂ} (h12 : z1 ≠ z2)
    (_hz1 : z ≠ z1) (_hz2 : z ≠ z2) (hz_line : z ∈ line z1 z2) :
    axialSymmetry z1 z2 z = z := by
  -- z ∈ line z1 z2 means ∃ t : ℝ, z - z1 = t • (z2 - z1)
  simp only [line, Set.mem_setOf_eq] at hz_line
  obtain ⟨t, ht⟩ := hz_line
  -- So z = z1 + t * (z2 - z1)
  have hz : z = z1 + t * (z2 - z1) := by
    calc z = z1 + (z - z1) := by ring
      _ = z1 + t • (z2 - z1) := by rw [ht]
      _ = z1 + t * (z2 - z1) := by simp [Complex.real_smul]
  -- conj(z) = conj(z1) + t * (conj(z2) - conj(z1)) since t is real
  have hconj_z : starRingEnd ℂ z = starRingEnd ℂ z1 + t * (starRingEnd ℂ z2 - starRingEnd ℂ z1) := by
    rw [hz]; simp only [map_add, map_mul, map_sub, Complex.conj_ofReal]
  have hdenom : starRingEnd ℂ z1 - starRingEnd ℂ z2 ≠ 0 := conj_diff_ne_zero h12
  -- Compute axialSymmetry z = conj(z) * α + β directly
  simp only [axialSymmetry, axialAlpha, axialBeta]
  rw [hconj_z]
  -- The RHS is z = z1 + t*(z2-z1), substitute that too
  conv_rhs => rw [hz]
  -- Now both sides are in terms of z1, z2, t and their conjugates
  field_simp [hdenom]
  ring

/-! ## The Key Lemma: img_r_sym

This is the critical connection between reflection and rotation that enables
the proof of Morley's theorem.

**Algebraic Proof:**

From `axialSymmetry_ratio_eq_conj`:
  (axialSymmetry z1 z2 z - z1) / (z2 - z1) = conj((z - z1) / (z2 - z1))

Let w = (z - z1) / (z2 - z1) and φ = arg(w) = angle_at z z1 z2.
Then conj(w) = |w| * cis(-φ).

For the rotation by θ:
  (rotation z1 θ z - z1) / (z2 - z1) = (z - z1) * cis(θ) / (z2 - z1) = w * cis(θ) = |w| * cis(φ + θ)

For these to be equal: cis(-φ) = cis(φ + θ), so θ = -2φ.

Therefore: axialSymmetry z1 z2 z = rotation z1 (-2 * angle_at z z1 z2) z -/
theorem img_r_sym {z1 z2 z : ℂ} (h12 : z1 ≠ z2) (hz_line : z ∉ line z1 z2) :
    axialSymmetry z1 z2 z = rotation z1 (-2 * angle_at z z1 z2) z := by
  -- z not on line implies z ≠ z1
  have hz1 : z ≠ z1 := by
    intro heq
    apply hz_line
    simp only [line, Set.mem_setOf_eq]
    use 0
    simp [heq]
  have h21 : z2 - z1 ≠ 0 := sub_ne_zero.mpr h12.symm
  -- Let w = (z - z1) / (z2 - z1)
  set w := (z - z1) / (z2 - z1) with hw_def
  have hw_ne : w ≠ 0 := div_ne_zero (sub_ne_zero.mpr hz1) h21
  -- Key identity: conj(w) = w * cis(-2 * arg(w))
  -- Proof: w = |w| * cis(arg w), so conj(w) = |w| * cis(-arg w)
  --        w * cis(-2*arg w) = |w| * cis(arg w - 2*arg w) = |w| * cis(-arg w)
  have hconj_w : starRingEnd ℂ w = w * cis (-2 * Complex.arg w) := by
    -- Key: conj(w) = w * exp(-2*I*arg(w))
    -- Using w = |w| * exp(I*arg(w)), we have conj(w) = |w| * exp(-I*arg(w))
    -- And w * exp(-2*I*arg(w)) = |w| * exp(I*arg(w)) * exp(-2*I*arg(w)) = |w| * exp(-I*arg(w))
    --
    -- Proof using conjugation formula: conj(w) / w = conj(w) * conj(conj(w)) / (w * conj(w))
    --                                              = |conj(w)|² / |w|² = 1
    -- Actually, simpler: conj(w) * w = |w|², so conj(w) = |w|² / w
    -- And cis(-2*arg(w)) = exp(-2i*arg(w)) = (exp(i*arg(w)))^(-2) = (w/|w|)^(-2) = |w|²/w²
    -- So w * cis(-2*arg(w)) = w * |w|²/w² = |w|²/w = conj(w) ✓
    --
    -- Alternative: use conj(w) = |w|² * w⁻¹ and cis(-2θ) = exp(-2iθ) = cis(θ)⁻² = (w/|w|)⁻²
    have hnorm_sq : w * starRingEnd ℂ w = ↑(‖w‖^2) := by
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
      simp [Complex.normSq_eq_norm_sq]
    have hcis_sq : cis (-2 * Complex.arg w) = (cis (Complex.arg w))⁻¹ * (cis (Complex.arg w))⁻¹ := by
      have h1 : (cis (Complex.arg w))⁻¹ = cis (-Complex.arg w) := by
        simp only [cis]
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      rw [h1]
      rw [← cis_add]
      congr 1
      ring
    -- cis(arg w) = exp(i*arg w) = w / |w|
    have hcis_eq : cis (Complex.arg w) = w / ↑‖w‖ := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      simp only [cis]
      have hnorm_ne : (‖w‖ : ℂ) ≠ 0 := by simp [hw_ne]
      field_simp [hnorm_ne]
      rw [mul_comm] at h
      exact h
    -- cis(arg w)⁻¹ = |w| / w (since cis(arg w) = w / |w|)
    have hcis_inv_eq : (cis (Complex.arg w))⁻¹ = ↑‖w‖ / w := by
      rw [hcis_eq]
      field_simp [hw_ne]
    -- conj(w) = |w|² / w and cis(-2*arg w) = (cis(arg w)⁻¹)² = |w|² / w²
    -- So w * cis(-2*arg w) = w * |w|² / w² = |w|² / w = conj(w)
    have hnorm_ne : (‖w‖ : ℂ) ≠ 0 := by simp [hw_ne]
    calc starRingEnd ℂ w
        = ↑(‖w‖^2) / w := by
          rw [← hnorm_sq]
          field_simp [hw_ne]
      _ = w * ((cis (Complex.arg w))⁻¹ * (cis (Complex.arg w))⁻¹) := by
          rw [hcis_inv_eq]
          have h : (↑(‖w‖ ^ 2) : ℂ) = ↑‖w‖ * ↑‖w‖ := by push_cast; ring
          rw [h]
          field_simp [hw_ne, hnorm_ne]
      _ = w * cis (-2 * Complex.arg w) := by rw [hcis_sq]
  -- angle_at z z1 z2 = arg w
  have hangle : angle_at z z1 z2 = Complex.arg w := rfl
  -- From axialSymmetry_ratio_eq_conj: (axialSymmetry z - z1) / (z2 - z1) = conj(w)
  have hratio := axialSymmetry_ratio_eq_conj h12 (z := z)
  -- So axialSymmetry z - z1 = conj(w) * (z2 - z1) = w * cis(-2*arg w) * (z2 - z1)
  have hsym_sub : axialSymmetry z1 z2 z - z1 = w * cis (-2 * Complex.arg w) * (z2 - z1) := by
    have h : (axialSymmetry z1 z2 z - z1) / (z2 - z1) = w * cis (-2 * Complex.arg w) := by
      rw [hratio, hconj_w]
    field_simp [h21] at h ⊢
    exact h
  -- And (z - z1) * cis(-2*angle) = w * (z2-z1) * cis(-2*arg w) [with commutation]
  have hrot_sub : (z - z1) * cis (-2 * angle_at z z1 z2) = w * cis (-2 * Complex.arg w) * (z2 - z1) := by
    simp only [hw_def, hangle]
    field_simp [h21]
  -- Therefore axialSymmetry z = z1 + (z - z1) * cis(-2*angle)
  simp only [rotation]
  calc axialSymmetry z1 z2 z = z1 + (axialSymmetry z1 z2 z - z1) := by ring
    _ = z1 + w * cis (-2 * Complex.arg w) * (z2 - z1) := by rw [hsym_sub]
    _ = z1 + (z - z1) * cis (-2 * angle_at z z1 z2) := by rw [← hrot_sub]

/-! ## Infrastructure for Triple Rotation Proof

The key geometric fact for Morley's theorem is that the LHS polynomial vanishes.
The full proof (following Isabelle AFP) requires showing that the composition of
three cubed rotations fixes vertex A, which then implies LHS = 0.

The machinery developed here (img_r_sym, angle negation, etc.) provides the
foundation for this proof. The complete proof requires tracking how angle
trisector lines interact with axial symmetry.
-/

/-- Applying rotation by 2*angle reverses the effect of axial symmetry.

    This follows from img_r_sym and composition of rotations:
    - img_r_sym: axialSymmetry z1 z2 z = rotation z1 (-2 * angle_at z z1 z2) z
    - So: rotation z1 (2 * angle) (axialSymmetry z1 z2 z) = rotation z1 0 z = z -/
theorem rotation_of_axialSymmetry {z1 z2 z : ℂ} (h12 : z1 ≠ z2) (hz : z ∉ line z1 z2) :
    rotation z1 (2 * angle_at z z1 z2) (axialSymmetry z1 z2 z) = z := by
  have him := img_r_sym h12 hz
  calc rotation z1 (2 * angle_at z z1 z2) (axialSymmetry z1 z2 z)
      = rotation z1 (2 * angle_at z z1 z2) (rotation z1 (-2 * angle_at z z1 z2) z) := by rw [him]
    _ = rotation z1 (2 * angle_at z z1 z2 + (-2 * angle_at z z1 z2)) z := by
        rw [rotation_comp_same_center]
    _ = rotation z1 0 z := by ring_nf
    _ = z := rotation_zero z1 z

/-- For Morley angles, rotation by 6γ at C recovers vertex A from its reflection.

    Specifically, if γ = angle_at A C B / 3, then 6γ = 2 * angle_at A C B,
    so rotation C (6γ) (axialSymmetry C B A) = A by rotation_of_axialSymmetry. -/
theorem rotation_6gamma_recovers_vertex (A B C : ℂ) (hCB : C ≠ B)
    (hA_off_CB : A ∉ line C B) (γ : ℝ) (hγ : γ = angle_at A C B / 3) :
    rotation C (6 * γ) (axialSymmetry C B A) = A := by
  have h6 : 6 * γ = 2 * angle_at A C B := by rw [hγ]; ring
  rw [h6]
  exact rotation_of_axialSymmetry hCB hA_off_CB

/-- rotation C (6γ) A equals rotation by 12γ of the reflected point.

    This follows from: rotation C (6γ) (axialSymmetry C B A) = A
    Applying rotation C (6γ) to both sides gives:
    rotation C (6γ) A = rotation C (12γ) (axialSymmetry C B A) -/
theorem rotation_6gamma_as_double_rotation (A B C : ℂ) (hCB : C ≠ B)
    (hA_off_CB : A ∉ line C B) (γ : ℝ) (hγ : γ = angle_at A C B / 3) :
    rotation C (6 * γ) A = rotation C (12 * γ) (axialSymmetry C B A) := by
  have hrecov := rotation_6gamma_recovers_vertex A B C hCB hA_off_CB γ hγ
  -- From hrecov: rotation C (6γ) (axialSymmetry C B A) = A
  -- Apply rotation C (6γ) to A (which equals rotation C (6γ) (axialSymmetry C B A)):
  calc rotation C (6 * γ) A
      = rotation C (6 * γ) (rotation C (6 * γ) (axialSymmetry C B A)) := by rw [hrecov]
    _ = rotation C (6 * γ + 6 * γ) (axialSymmetry C B A) := by rw [rotation_comp_same_center]
    _ = rotation C (12 * γ) (axialSymmetry C B A) := by ring_nf

/-- For a Morley triangle where 12γ = 4 * angle_at A C B, this equals rotation by 4 times the angle. -/
theorem rotation_6gamma_explicit (A B C : ℂ) (hCB : C ≠ B)
    (hA_off_CB : A ∉ line C B) (γ : ℝ) (hγ : γ = angle_at A C B / 3) :
    rotation C (6 * γ) A = rotation C (4 * angle_at A C B) (axialSymmetry C B A) := by
  have h12 : 12 * γ = 4 * angle_at A C B := by rw [hγ]; ring
  rw [rotation_6gamma_as_double_rotation A B C hCB hA_off_CB γ hγ, h12]

/-- When three rotation angles sum to 2π, the composition is a translation by the LHS vector.

    Specifically: rotation A θ₁ ∘ rotation B θ₂ ∘ rotation C θ₃ = (· + LHS)
    where LHS = (1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B + cis θ₁ * cis θ₂ * (1 - cis θ₃) * C -/
theorem triple_rotation_is_translation_by_lhs (A B C : ℂ) (θ₁ θ₂ θ₃ : ℝ)
    (hsum : θ₁ + θ₂ + θ₃ = 2 * Real.pi) :
    ∀ z : ℂ, rotation A θ₁ (rotation B θ₂ (rotation C θ₃ z)) = z +
      ((1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B + cis θ₁ * cis θ₂ * (1 - cis θ₃) * C) := by
  intro z
  simp only [rotation]
  have hprod : cis θ₁ * cis θ₂ * cis θ₃ = 1 := by
    rw [← cis_add, ← cis_add, hsum, cis_two_pi]
  have hC : cis θ₁ * cis θ₂ * cis θ₃ * C = C := by rw [hprod, one_mul]
  -- Direct ring calculation
  calc A + (B + (C + (z - C) * cis θ₃ - B) * cis θ₂ - A) * cis θ₁
      = A + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂ +
        (z - C) * (cis θ₁ * cis θ₂ * cis θ₃) := by ring
    _ = A + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂ + (z - C) := by rw [hprod]; ring
    _ = z + (A - C + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂) := by ring
    _ = z + (A - cis θ₁ * A + cis θ₁ * B - cis θ₁ * cis θ₂ * B +
            cis θ₁ * cis θ₂ * C - C) := by ring
    _ = z + (A - cis θ₁ * A + cis θ₁ * B - cis θ₁ * cis θ₂ * B +
            cis θ₁ * cis θ₂ * C - cis θ₁ * cis θ₂ * cis θ₃ * C) := by rw [hC]
    _ = z + ((1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B +
            cis θ₁ * cis θ₂ * (1 - cis θ₃) * C) := by ring

/-- When three rotation angles sum to 2π, the composition is a translation.

    Specifically: rotation A θ₁ ∘ rotation B θ₂ ∘ rotation C θ₃ = (· + v)
    for some fixed v when θ₁ + θ₂ + θ₃ = 2π.

    The translation vector v is what the LHS polynomial computes. -/
theorem triple_rotation_is_translation (A B C : ℂ) (θ₁ θ₂ θ₃ : ℝ)
    (hsum : θ₁ + θ₂ + θ₃ = 2 * Real.pi) :
    ∃ v : ℂ, ∀ z : ℂ, rotation A θ₁ (rotation B θ₂ (rotation C θ₃ z)) = z + v := by
  -- The composition is: A + cis(θ₁) * (rotation B θ₂ (rotation C θ₃ z) - A)
  -- Expanding fully and using cis(θ₁)*cis(θ₂)*cis(θ₃) = cis(2π) = 1
  use (1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B + cis θ₁ * cis θ₂ * (1 - cis θ₃) * C
  intro z
  simp only [rotation]
  have hprod : cis θ₁ * cis θ₂ * cis θ₃ = 1 := by
    rw [← cis_add, ← cis_add, hsum, cis_two_pi]
  have hC : cis θ₁ * cis θ₂ * cis θ₃ * C = C := by rw [hprod, one_mul]
  -- Direct ring calculation
  calc A + (B + (C + (z - C) * cis θ₃ - B) * cis θ₂ - A) * cis θ₁
      = A + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂ +
        (z - C) * (cis θ₁ * cis θ₂ * cis θ₃) := by ring
    _ = A + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂ + (z - C) := by rw [hprod]; ring
    _ = z + (A - C + (B - A) * cis θ₁ + (C - B) * cis θ₁ * cis θ₂) := by ring
    _ = z + (A - cis θ₁ * A + cis θ₁ * B - cis θ₁ * cis θ₂ * B +
            cis θ₁ * cis θ₂ * C - C) := by ring
    _ = z + (A - cis θ₁ * A + cis θ₁ * B - cis θ₁ * cis θ₂ * B +
            cis θ₁ * cis θ₂ * C - cis θ₁ * cis θ₂ * cis θ₃ * C) := by rw [hC]
    _ = z + ((1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B +
            cis θ₁ * cis θ₂ * (1 - cis θ₃) * C) := by ring

/-- A translation that fixes any point is the identity (translation by 0). -/
theorem translation_fixing_point_is_zero {v : ℂ} {p : ℂ} (h : p + v = p) : v = 0 := by
  have : v = p + v - p := by ring
  rw [h] at this
  simp at this
  exact this

/-- If the triple rotation fixes A, then LHS = 0.

    Combined with triple_rotation_is_translation_by_lhs, this shows that
    proving the composition fixes A is sufficient to prove LHS = 0. -/
theorem triple_rotation_fixes_A_implies_lhs_zero (A B C : ℂ) (θ₁ θ₂ θ₃ : ℝ)
    (hsum : θ₁ + θ₂ + θ₃ = 2 * Real.pi)
    (hfix : rotation A θ₁ (rotation B θ₂ (rotation C θ₃ A)) = A) :
    (1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B + cis θ₁ * cis θ₂ * (1 - cis θ₃) * C = 0 := by
  -- Use the direct translation formula
  have hA := triple_rotation_is_translation_by_lhs A B C θ₁ θ₂ θ₃ hsum A
  -- hA: rotation composition at A = A + LHS
  -- But by hfix, rotation composition at A = A
  rw [hfix] at hA
  -- So A = A + LHS, meaning LHS = 0
  exact translation_fixing_point_is_zero hA.symm

/-- The OPPOSITE order composition: first at A, then B, then C.

    When θ₁ + θ₂ + θ₃ = 2π, this composition equals z + v where:
    v = (cis θ₂ * cis θ₃ - 1) * A + cis θ₃ * (1 - cis θ₂) * B + (1 - cis θ₃) * C

    This is the order used in the Isabelle AFP proof (g22).
    For the Morley configuration (where θ₁ = 2*angle_at B A C, etc.), v = 0. -/
theorem triple_rotation_ABC_translation (A B C : ℂ) (θ₁ θ₂ θ₃ : ℝ)
    (hsum : θ₁ + θ₂ + θ₃ = 2 * Real.pi) :
    ∀ z : ℂ, rotation C θ₃ (rotation B θ₂ (rotation A θ₁ z)) = z +
      ((cis θ₂ * cis θ₃ - 1) * A + cis θ₃ * (1 - cis θ₂) * B + (1 - cis θ₃) * C) := by
  intro z
  simp only [rotation]
  have hprod : cis θ₁ * cis θ₂ * cis θ₃ = 1 := by
    rw [← cis_add, ← cis_add, hsum, cis_two_pi]
  calc C + (B + (A + (z - A) * cis θ₁ - B) * cis θ₂ - C) * cis θ₃
      = C + (B - C) * cis θ₃ + (A - B) * cis θ₂ * cis θ₃ +
        (z - A) * (cis θ₁ * cis θ₂ * cis θ₃) := by ring
    _ = C + (B - C) * cis θ₃ + (A - B) * cis θ₂ * cis θ₃ + (z - A) := by rw [hprod]; ring
    _ = z + (C - A + (B - C) * cis θ₃ + (A - B) * cis θ₂ * cis θ₃) := by ring
    _ = z + ((cis θ₂ * cis θ₃ - 1) * A + cis θ₃ * (1 - cis θ₂) * B + (1 - cis θ₃) * C) := by ring

/-- The simplified form of LHS using the factorization (x² + x + 1)(1-x) = 1 - x³ -/
theorem lhs_simplified_form (A B C : ℂ) (a b c : ℂ) (habc : a * b * c = 1) :
    (1 - a) * A + a * (1 - b) * B + a * b * (1 - c) * C =
    A - C + a * (B - A) + a * b * (C - B) := by
  have hc : a * b * c * C = C := by rw [habc, one_mul]
  calc (1 - a) * A + a * (1 - b) * B + a * b * (1 - c) * C
      = A - a * A + a * B - a * b * B + a * b * C - a * b * c * C := by ring
    _ = A - a * A + a * B - a * b * B + a * b * C - C := by rw [hc]
    _ = A - C + a * (B - A) + a * b * (C - B) := by ring

/-- When 6α + 6β + 6γ = 2π, the product of cubed cis values is 1 -/
theorem cis_cubed_product_one (α β γ : ℝ) (hsum : α + β + γ = Real.pi / 3) :
    cis (2 * α) ^ 3 * cis (2 * β) ^ 3 * cis (2 * γ) ^ 3 = 1 := by
  have hsum6 : 6 * α + 6 * β + 6 * γ = 2 * Real.pi := by linarith
  have h1 : cis (2 * α) ^ 3 = cis (6 * α) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  have h2 : cis (2 * β) ^ 3 = cis (6 * β) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  have h3 : cis (2 * γ) ^ 3 = cis (6 * γ) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  rw [h1, h2, h3, ← cis_add, ← cis_add, hsum6, cis_two_pi]

/-- The LHS can be rewritten in simplified form using the (x²+x+1)(1-x) = 1-x³ identity -/
theorem lhs_rewrite (A B C : ℂ) (a₁ a₂ a₃ : ℂ) :
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
    a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
    a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) =
    (1 - a₁ ^ 3) * A + a₁ ^ 3 * (1 - a₂ ^ 3) * B + a₁ ^ 3 * a₂ ^ 3 * (1 - a₃ ^ 3) * C := by
  have hf₁ : (a₁ ^ 2 + a₁ + 1) * (1 - a₁) = 1 - a₁ ^ 3 := by ring
  have hf₂ : (a₂ ^ 2 + a₂ + 1) * (1 - a₂) = 1 - a₂ ^ 3 := by ring
  have hf₃ : (a₃ ^ 2 + a₃ + 1) * (1 - a₃) = 1 - a₃ ^ 3 := by ring
  calc (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
      a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃))
      = A * ((a₁ ^ 2 + a₁ + 1) * (1 - a₁)) + a₁ ^ 3 * B * ((a₂ ^ 2 + a₂ + 1) * (1 - a₂)) +
        a₁ ^ 3 * a₂ ^ 3 * C * ((a₃ ^ 2 + a₃ + 1) * (1 - a₃)) := by ring
    _ = A * (1 - a₁ ^ 3) + a₁ ^ 3 * B * (1 - a₂ ^ 3) + a₁ ^ 3 * a₂ ^ 3 * C * (1 - a₃ ^ 3) := by
        rw [hf₁, hf₂, hf₃]
    _ = (1 - a₁ ^ 3) * A + a₁ ^ 3 * (1 - a₂ ^ 3) * B + a₁ ^ 3 * a₂ ^ 3 * (1 - a₃ ^ 3) * C := by ring

/-! ## Connection to Morley LHS

The axiom in Morley.lean claims that for the Morley configuration, the LHS vanishes.
Here we establish the key connection: the axiom's LHS equals the translation from
triple_rotation_is_translation_by_lhs with angles 6α, 6β, 6γ (the cubed rotation angles).

This means: LHS = 0 ⟺ triple rotation fixes A.
-/

/-- The Morley LHS (from the axiom) equals the translation from the (C,B,A) order
    triple rotation with cubed angles.

    The axiom's LHS is:
    (a₁² + a₁ + 1)(A(1-a₁)) + a₁³(a₂² + a₂ + 1)(B(1-a₂)) + a₁³a₂³(a₃² + a₃ + 1)(C(1-a₃))

    which by lhs_rewrite equals:
    (1 - a₁³)A + a₁³(1 - a₂³)B + a₁³a₂³(1 - a₃³)C

    which is exactly the translation from triple_rotation_is_translation_by_lhs
    with θ₁ = 6α, θ₂ = 6β, θ₃ = 6γ (since cis(6α) = a₁³). -/
theorem morley_lhs_eq_translation (A B C : ℂ) (α β γ : ℝ)
    (_hsum : α + β + γ = Real.pi / 3) :
    let a₁ := cis (2 * α)
    let a₂ := cis (2 * β)
    let a₃ := cis (2 * γ)
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
    a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
    a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) =
    (1 - cis (6 * α)) * A + cis (6 * α) * (1 - cis (6 * β)) * B +
    cis (6 * α) * cis (6 * β) * (1 - cis (6 * γ)) * C := by
  simp only
  -- First apply lhs_rewrite
  have hlhs := lhs_rewrite A B C (cis (2 * α)) (cis (2 * β)) (cis (2 * γ))
  rw [hlhs]
  -- Now show cis(2α)³ = cis(6α) etc.
  have h1 : cis (2 * α) ^ 3 = cis (6 * α) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  have h2 : cis (2 * β) ^ 3 = cis (6 * β) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  have h3 : cis (2 * γ) ^ 3 = cis (6 * γ) := by
    simp only [pow_succ, pow_zero, one_mul]
    rw [← cis_add, ← cis_add]; congr 1; ring
  rw [h1, h2, h3]

/-- The translation from triple rotation equals the Morley LHS.

    This allows us to use triple_rotation_fixes_A_implies_lhs_zero to conclude
    that if the triple rotation fixes A, then the Morley LHS = 0. -/
theorem morley_lhs_is_translation (A B C : ℂ) (α β γ : ℝ)
    (hsum : α + β + γ = Real.pi / 3) :
    let θ₁ := 6 * α
    let θ₂ := 6 * β
    let θ₃ := 6 * γ
    let a₁ := cis (2 * α)
    let a₂ := cis (2 * β)
    let a₃ := cis (2 * γ)
    θ₁ + θ₂ + θ₃ = 2 * Real.pi ∧
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
     a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
     a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) =
    (1 - cis θ₁) * A + cis θ₁ * (1 - cis θ₂) * B + cis θ₁ * cis θ₂ * (1 - cis θ₃) * C := by
  simp only
  constructor
  · -- θ₁ + θ₂ + θ₃ = 2π
    linarith
  · -- LHS = translation
    exact morley_lhs_eq_translation A B C α β γ hsum

/-- Key reduction: If the triple rotation (with cubed angles) fixes A,
    then the Morley LHS = 0.

    This combines:
    1. morley_lhs_is_translation: Morley LHS = translation
    2. triple_rotation_fixes_A_implies_lhs_zero: rotation fixes A → translation = 0 -/
theorem morley_lhs_zero_if_rotation_fixes_A (A B C : ℂ) (α β γ : ℝ)
    (hsum : α + β + γ = Real.pi / 3)
    (hfix : rotation A (6 * α) (rotation B (6 * β) (rotation C (6 * γ) A)) = A) :
    let a₁ := cis (2 * α)
    let a₂ := cis (2 * β)
    let a₃ := cis (2 * γ)
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
    a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
    a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) = 0 := by
  simp only
  -- Get that θ₁ + θ₂ + θ₃ = 2π
  have hsum6 : 6 * α + 6 * β + 6 * γ = 2 * Real.pi := by linarith
  -- Get translation = 0 from rotation fixing A
  have htrans := triple_rotation_fixes_A_implies_lhs_zero A B C (6*α) (6*β) (6*γ) hsum6 hfix
  -- Connect to Morley LHS
  have heq := morley_lhs_eq_translation A B C α β γ hsum
  rw [heq, htrans]

/-- The triple rotation with doubled angles (2∠A, 2∠B, 2∠C) is equivalent to
    the triple cubed rotation with trisected angles (6α, 6β, 6γ where α = ∠A/3).

    This is immediate since 6*(∠A/3) = 2*∠A. -/
theorem doubled_angles_eq_cubed_trisected (A B C : ℂ) (α β γ : ℝ)
    (hα : α = angle_at B A C / 3) (hβ : β = angle_at C B A / 3) (hγ : γ = angle_at A C B / 3) :
    6 * α = 2 * angle_at B A C ∧ 6 * β = 2 * angle_at C B A ∧ 6 * γ = 2 * angle_at A C B := by
  constructor
  · rw [hα]; ring
  constructor
  · rw [hβ]; ring
  · rw [hγ]; ring

/-! ## The Core Geometric Identity

The key fact is that for any triangle ABC with positive angles (counterclockwise orientation),
the translation vector for the triple rotation with doubled angles is zero.

This is a deep geometric identity relating vertex positions to their angles:
  (1 - cis(2∠A))*A + cis(2∠A)*(1 - cis(2∠B))*B + cis(2∠A)*cis(2∠B)*(1 - cis(2∠C))*C = 0

Proof approach: Use the relationship cis(2∠) = w/conj(w) where w is the ratio defining the angle.
-/

/-- cis(2*arg(w)) = w/conj(w) for nonzero w.

    This is the key identity that relates cis(2*angle) to ratios of complex numbers. -/
theorem cis_twice_arg (w : ℂ) (hw : w ≠ 0) : cis (2 * Complex.arg w) = w / starRingEnd ℂ w := by
  -- w = |w| * cis(arg w), so w/conj(w) = cis(arg w) / cis(-arg w) = cis(2*arg w)
  have hnorm : (‖w‖ : ℂ) ≠ 0 := by simp [hw]
  have hnorm_sq : w * starRingEnd ℂ w = ↑(‖w‖^2) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]
  have hconj_ne : starRingEnd ℂ w ≠ 0 := by simp [hw]
  -- Key insight: cis(2*arg w) = w² / |w|² / w = w / conj(w)
  -- We use: cis(2θ) = cis(θ)² and cis(arg w) = w / |w|
  have hcis_arg : cis (Complex.arg w) = w / ↑‖w‖ := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    simp only [cis]
    field_simp [hnorm]
    rw [mul_comm] at h
    exact h
  have hcis_sq : cis (2 * Complex.arg w) = (w / ↑‖w‖) ^ 2 := by
    have h1 : cis (2 * Complex.arg w) = cis (Complex.arg w) * cis (Complex.arg w) := by
      rw [← cis_add]; congr 1; ring
    rw [h1, hcis_arg, sq]
  rw [hcis_sq]
  -- Now show (w / |w|)² = w / conj(w)
  -- (w/|w|)² = w²/|w|² and w/conj(w) = w * w / (w * conj(w)) = w² / |w|²
  have h1 : (w / ↑‖w‖) ^ 2 = w ^ 2 / ↑‖w‖ ^ 2 := by field_simp [hnorm]
  have h2 : w / starRingEnd ℂ w = w ^ 2 / (w * starRingEnd ℂ w) := by
    field_simp [hw, hconj_ne]
  rw [h1, h2, hnorm_sq]
  congr 1
  push_cast
  ring

/-- For a nonzero complex number, cis(2*arg(w)) * conj(w) = w. -/
theorem cis_twice_arg_mul_conj (w : ℂ) (hw : w ≠ 0) :
    cis (2 * Complex.arg w) * starRingEnd ℂ w = w := by
  rw [cis_twice_arg w hw]
  have hconj_ne : starRingEnd ℂ w ≠ 0 := by simp [hw]
  field_simp [hconj_ne]

/-- The translation vector for triple rotation with doubled triangle angles.

    For a triangle ABC with angles ∠A, ∠B, ∠C summing to π, we define:
    - a = cis(2∠A), b = cis(2∠B), c = cis(2∠C)
    - Translation v = (1-a)A + a(1-b)B + ab(1-c)C

    The key identity is that this translation is zero for any triangle.

    **Proof Strategy** (from algebraic manipulation):

    Let u = (B-A)/(C-A), v = (C-B)/(A-B), w = (A-C)/(B-C).
    Then:
    - ∠A = arg(u), so a = cis(2∠A) = u/conj(u)
    - ∠B = arg(v), so b = cis(2∠B) = v/conj(v)
    - ∠C = arg(w), so c = cis(2∠C) = w/conj(w)
    - u*v*w = -1 (product of ratios around triangle)

    The identity v = 0 can then be verified by direct algebraic manipulation
    using these substitutions. -/
theorem translation_zero_for_doubled_angles (A B C : ℂ) (hnd : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    let a := cis (2 * angle_at B A C)
    let b := cis (2 * angle_at C B A)
    let c := cis (2 * angle_at A C B)
    (1 - a) * A + a * (1 - b) * B + a * b * (1 - c) * C = 0 := by
  simp only
  -- Define the vertex difference ratios
  set u := (B - A) / (C - A) with hu_def
  set v := (C - B) / (A - B) with hv_def
  set w := (A - C) / (B - C) with hw_def
  -- The angles are arg of these ratios
  have hCA : C - A ≠ 0 := sub_ne_zero.mpr hnd.ne_CA
  have hAB : A - B ≠ 0 := sub_ne_zero.mpr hnd.ne_AB
  have hBC : B - C ≠ 0 := sub_ne_zero.mpr hnd.ne_BC
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr hnd.ne_AB.symm
  have hCB : C - B ≠ 0 := sub_ne_zero.mpr hnd.ne_BC.symm
  have hAC : A - C ≠ 0 := sub_ne_zero.mpr hnd.ne_CA.symm
  have hu_ne : u ≠ 0 := div_ne_zero hBA hCA
  have hv_ne : v ≠ 0 := div_ne_zero hCB hAB
  have hw_ne : w ≠ 0 := div_ne_zero hAC hBC
  -- Product u*v*w = -1
  have hprod : u * v * w = -1 := by
    simp only [hu_def, hv_def, hw_def]
    field_simp [hCA, hAB, hBC]
    ring
  -- Relate cis(2*angle) to ratios
  have ha : cis (2 * angle_at B A C) = u / starRingEnd ℂ u := cis_twice_arg u hu_ne
  have hb : cis (2 * angle_at C B A) = v / starRingEnd ℂ v := cis_twice_arg v hv_ne
  have hc : cis (2 * angle_at A C B) = w / starRingEnd ℂ w := cis_twice_arg w hw_ne
  -- Now substitute and verify algebraically
  rw [ha, hb, hc]
  -- The proof requires showing that after substitution, everything cancels
  -- This is a lengthy algebraic verification
  have hu_conj : starRingEnd ℂ u ≠ 0 := by simp [hu_ne]
  have hv_conj : starRingEnd ℂ v ≠ 0 := by simp [hv_ne]
  have hw_conj : starRingEnd ℂ w ≠ 0 := by simp [hw_ne]
  -- Express vertex differences in terms of the ratios
  have hBA_eq : B - A = u * (C - A) := by
    simp only [hu_def]
    field_simp [hCA]
  have hCB_eq : C - B = v * (A - B) := by
    simp only [hv_def]
    field_simp [hAB]
  have hAC_eq : A - C = w * (B - C) := by
    simp only [hw_def]
    field_simp [hBC]
  -- The algebraic identity is complex; use polyrith or native_decide if available
  -- For now, we'll use a direct field_simp approach
  field_simp [hu_conj, hv_conj, hw_conj]
  -- After clearing denominators, this becomes a polynomial identity
  -- The identity holds because of the constraint u*v*w = -1 and the triangle geometry
  -- Full proof requires expanding and using the product constraint
  sorry

/-- The Morley LHS vanishes for any triangle with positive angles.

    This is the key theorem that will replace the axiom in Morley.lean. -/
theorem morley_lhs_zero (A B C : ℂ) (hnd : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    let α := angle_at B A C / 3
    let β := angle_at C B A / 3
    let γ := angle_at A C B / 3
    let a₁ := cis (2 * α)
    let a₂ := cis (2 * β)
    let a₃ := cis (2 * γ)
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
    a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
    a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) = 0 := by
  simp only
  -- Get the trisected angles sum
  have hsum := trisected_angles_sum hnd hpos
  -- Apply our key reduction
  have hfix : rotation A (6 * (angle_at B A C / 3))
      (rotation B (6 * (angle_at C B A / 3))
        (rotation C (6 * (angle_at A C B / 3)) A)) = A := by
    -- The angles simplify: 6 * (∠/3) = 2∠
    have h1 : 6 * (angle_at B A C / 3) = 2 * angle_at B A C := by ring
    have h2 : 6 * (angle_at C B A / 3) = 2 * angle_at C B A := by ring
    have h3 : 6 * (angle_at A C B / 3) = 2 * angle_at A C B := by ring
    simp only [h1, h2, h3]
    -- Now we need: rotation A (2∠A) (rotation B (2∠B) (rotation C (2∠C) A)) = A
    -- Since rotation A θ A = A, this reduces to:
    -- rotation B (2∠B) (rotation C (2∠C) A) = A
    -- Which follows from translation_zero_for_doubled_angles
    have hsum6 : 2 * angle_at B A C + 2 * angle_at C B A + 2 * angle_at A C B = 2 * Real.pi := by
      have hpi := angle_sum_pi hnd
      simp only [abs_of_pos hpos.1, abs_of_pos hpos.2.1, abs_of_pos hpos.2.2] at hpi
      linarith
    have htrans := triple_rotation_is_translation_by_lhs A B C
      (2 * angle_at B A C) (2 * angle_at C B A) (2 * angle_at A C B) hsum6 A
    have hzero := translation_zero_for_doubled_angles A B C hnd hpos
    simp only at htrans hzero
    rw [htrans, hzero, add_zero]
  exact morley_lhs_zero_if_rotation_fixes_A A B C _ _ _ hsum hfix

end Morley
