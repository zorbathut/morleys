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

end Morley
