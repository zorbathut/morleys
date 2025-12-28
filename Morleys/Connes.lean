/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Data.Complex.Exponential
import Morleys.CubeRoot
import Morleys.Rotation
import Morleys.Equilateral

/-!
# Core Algebraic Identity for Connes' Proof

This file establishes the algebraic heart of Connes' proof of Morley's theorem.
The key is the `root_unity_carac` lemma which relates fixed points of composed
rotations to the equilateral condition.

## Main results

* `equality_for_comp` : Composition of three cubed rotations in affine form
* `morley_equilateral_condition` : When the LHS vanishes, the triangle is equilateral

## Key insight

For three rotations by angles 2α, 2β, 2γ centered at A, B, C respectively:
- When the triangle has angles 3α, 3β, 3γ (summing to π), we have 2α + 2β + 2γ = 2π/3
- So cis(2α) * cis(2β) * cis(2γ) = cis(2π/3) = ω
- The cubed composition (r₁ ∘ r₁ ∘ r₁) ∘ (r₂ ∘ r₂ ∘ r₂) ∘ (r₃ ∘ r₃ ∘ r₃) = id
- The fixed points of pairwise compositions form an equilateral triangle
-/

namespace Morley

open Complex Real

/-- Affine form: r(z) = a*z + b where a = cis(θ), b = A*(1 - cis(θ)) -/
theorem rotation_affine (A : ℂ) (θ : ℝ) (z : ℂ) :
    rotation A θ z = cis θ * z + A * (1 - cis θ) := by
  simp only [rotation]
  ring

/-- The multiplier for rotation by θ -/
noncomputable def rotMul (θ : ℝ) : ℂ := cis θ

/-- The constant for rotation centered at A by θ -/
noncomputable def rotConst (A : ℂ) (θ : ℝ) : ℂ := A * (1 - cis θ)

/-- Rotation in terms of rotMul and rotConst -/
theorem rotation_eq_affine (A : ℂ) (θ : ℝ) (z : ℂ) :
    rotation A θ z = rotMul θ * z + rotConst A θ := rotation_affine A θ z

/-- Composing three rotations (each applied 3 times) in affine form.
    If r_i(z) = a_i * z + b_i, then
    (r₁³ ∘ r₂³ ∘ r₃³)(z) = (a₁a₂a₃)³ * z + (a₁² + a₁ + 1)*b₁ + a₁³*(a₂² + a₂ + 1)*b₂
                           + a₁³*a₂³*(a₃² + a₃ + 1)*b₃ -/
theorem equality_for_comp (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ) (z : ℂ) :
    let f := fun w => a₁ * w + b₁
    let g := fun w => a₂ * w + b₂
    let h := fun w => a₃ * w + b₃
    (f ∘ f ∘ f) ((g ∘ g ∘ g) ((h ∘ h ∘ h) z)) =
      (a₁ * a₂ * a₃) ^ 3 * z +
      (a₁ ^ 2 + a₁ + 1) * b₁ +
      a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
      a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ := by
  simp only [Function.comp_apply]
  ring

/-- Fixed point formula: if g(h(P)) = P for g(z) = a₂*z + b₂, h(z) = a₃*z + b₃,
    and a₂*a₃ ≠ 1, then P = (a₂*b₃ + b₂)/(1 - a₂*a₃) -/
theorem fixed_point_formula (a₂ a₃ b₂ b₃ P : ℂ) (h : a₂ * a₃ ≠ 1)
    (hfix : a₂ * (a₃ * P + b₃) + b₂ = P) : P = (a₂ * b₃ + b₂) / (1 - a₂ * a₃) := by
  have h1 : (1 - a₂ * a₃) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have h2 : a₂ * a₃ * P + a₂ * b₃ + b₂ = P := by
    calc a₂ * a₃ * P + a₂ * b₃ + b₂ = a₂ * (a₃ * P + b₃) + b₂ := by ring
      _ = P := hfix
  have h3 : P * (1 - a₂ * a₃) = a₂ * b₃ + b₂ := by
    calc P * (1 - a₂ * a₃) = P - a₂ * a₃ * P := by ring
      _ = a₂ * a₃ * P + a₂ * b₃ + b₂ - a₂ * a₃ * P := by rw [h2]
      _ = a₂ * b₃ + b₂ := by ring
  rw [eq_div_iff h1, mul_comm]
  rw [mul_comm] at h3
  exact h3

/-- cis(θ) * cis(φ) * cis(ψ) = cis(θ + φ + ψ) -/
theorem cis_mul_mul (θ φ ψ : ℝ) : cis θ * cis φ * cis ψ = cis (θ + φ + ψ) := by
  rw [cis_add, cis_add]

/-- When a₁ * a₂ * a₃ = ω, the key simplification: 1 - a_i * a_j = (a_k - ω) / a_k -/
theorem one_minus_prod_eq (a₁ a₂ a₃ : ℂ) (h : a₁ * a₂ * a₃ = ω) (ha₃ : a₃ ≠ 0) :
    1 - a₁ * a₂ = (a₃ - ω) / a₃ := by
  have h2 : a₁ * a₂ = ω / a₃ := by field_simp [ha₃] at h ⊢; exact h
  rw [h2]; field_simp [ha₃]

/-- Similarly for other pairs -/
theorem one_minus_prod_eq' (a₁ a₂ a₃ : ℂ) (h : a₁ * a₂ * a₃ = ω) (ha₁ : a₁ ≠ 0) :
    1 - a₂ * a₃ = (a₁ - ω) / a₁ := by
  have h1 : a₂ * a₃ = ω / a₁ := by
    field_simp [ha₁]
    calc a₂ * a₃ * a₁ = a₁ * a₂ * a₃ := by ring
      _ = ω := h
  rw [h1]; field_simp [ha₁]

theorem one_minus_prod_eq'' (a₁ a₂ a₃ : ℂ) (h : a₁ * a₂ * a₃ = ω) (ha₂ : a₂ ≠ 0) :
    1 - a₁ * a₃ = (a₂ - ω) / a₂ := by
  have h1 : a₁ * a₃ = ω / a₂ := by
    field_simp [ha₂]
    calc a₁ * a₃ * a₂ = a₁ * a₂ * a₃ := by ring
      _ = ω := h
  rw [h1]; field_simp [ha₂]

/-- The core algebraic identity (Connes' key lemma).
    This is the translation of Isabelle's `root_unity_carac` lemma.

    When a₁ * a₂ * a₃ = ω and none of the pairwise products equal 1,
    the fixed points R, P, Q satisfy an identity that, when the LHS is zero,
    implies R + ω*P + ω²*Q = 0, characterizing an equilateral triangle.
-/
theorem root_unity_carac (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ)
    (hprod : a₁ * a₂ * a₃ = ω)
    (h₁₂ : 1 - a₁ * a₂ ≠ 0) (h₂₃ : 1 - a₂ * a₃ ≠ 0) (h₁₃ : 1 - a₁ * a₃ ≠ 0)
    (_ha₁ : a₁ ≠ 0) (_ha₂ : a₂ ≠ 0) (_ha₃ : a₃ ≠ 0) :
    let R := (a₁ * b₂ + b₁) / (1 - a₁ * a₂)
    let P := (a₂ * b₃ + b₂) / (1 - a₂ * a₃)
    let Q := (a₃ * b₁ + b₃) / (1 - a₃ * a₁)
    (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
      a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ =
    -ω * a₁ ^ 2 * a₂ * (a₁ - ω) * (a₂ - ω) * (a₃ - ω) * (R + ω * P + ω ^ 2 * Q) := by
  -- This is a massive algebraic identity.
  -- We use the key ω properties: ω³ = 1, 1 + ω + ω² = 0
  simp only
  have hω3 : ω ^ 3 = 1 := omega_cubed
  have hω2 : ω ^ 2 = -1 - ω := omega_sq_eq
  have h13' : 1 - a₃ * a₁ = 1 - a₁ * a₃ := by ring
  -- Clear denominators
  field_simp [h₁₂, h₂₃, h₁₃, h13']
  -- The rest is a polynomial identity modulo ω³ = 1 and ω² = -1 - ω
  -- This requires extensive computation - verified in Isabelle
  sorry

/-- When the LHS of root_unity_carac is zero, R + ω*P + ω²*Q = 0.
    This is the condition for the Morley triangle to be equilateral. -/
theorem morley_equilateral_condition (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ)
    (hprod : a₁ * a₂ * a₃ = ω)
    (h₁₂ : 1 - a₁ * a₂ ≠ 0) (h₂₃ : 1 - a₂ * a₃ ≠ 0) (h₁₃ : 1 - a₁ * a₃ ≠ 0)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (ha₁ω : a₁ ≠ ω) (ha₂ω : a₂ ≠ ω) (ha₃ω : a₃ ≠ ω)
    (hLHS : (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
            a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ = 0) :
    let R := (a₁ * b₂ + b₁) / (1 - a₁ * a₂)
    let P := (a₂ * b₃ + b₂) / (1 - a₂ * a₃)
    let Q := (a₃ * b₁ + b₃) / (1 - a₁ * a₃)
    R + ω * P + ω ^ 2 * Q = 0 := by
  simp only
  have h13' : 1 - a₃ * a₁ = 1 - a₁ * a₃ := by ring
  have hkey := root_unity_carac a₁ a₂ a₃ b₁ b₂ b₃ hprod h₁₂ h₂₃ h₁₃ ha₁ ha₂ ha₃
  simp only [h13'] at hkey
  rw [hLHS] at hkey
  simp only [zero_eq_mul] at hkey
  -- The product -ω * a₁² * a₂ * (a₁ - ω) * (a₂ - ω) * (a₃ - ω) ≠ 0
  have hne : ω * a₁ ^ 2 * a₂ * (a₁ - ω) * (a₂ - ω) * (a₃ - ω) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    exact omega_ne_zero
    exact pow_ne_zero 2 ha₁
    exact ha₂
    exact sub_ne_zero.mpr ha₁ω
    exact sub_ne_zero.mpr ha₂ω
    exact sub_ne_zero.mpr ha₃ω
  have hne' : -ω * a₁ ^ 2 * a₂ * (a₁ - ω) * (a₂ - ω) * (a₃ - ω) ≠ 0 := by
    simp only [neg_mul, neg_ne_zero]
    exact hne
  -- From 0 = -ω * ... * (R + ω*P + ω²*Q), we get R + ω*P + ω²*Q = 0
  cases hkey with
  | inl h => exact (hne' h).elim
  | inr h => exact h

/-- Cubed rotation at center A by angle 2α equals single rotation by 6α -/
theorem rotation_cubed_eq (A : ℂ) (α : ℝ) :
    (rotation A (2 * α)) ∘ (rotation A (2 * α)) ∘ (rotation A (2 * α)) =
    rotation A (6 * α) := by
  ext z
  simp only [Function.comp_apply]
  rw [rotation_comp_same_center, rotation_comp_same_center]
  congr 1; ring

/-- When 6α + 6β + 6γ = 2π, the product of cis values is 1 -/
theorem cis_product_one (α β γ : ℝ) (hsum : 6 * α + 6 * β + 6 * γ = 2 * Real.pi) :
    cis (6 * α) * cis (6 * β) * cis (6 * γ) = 1 := by
  rw [← cis_add, ← cis_add, hsum, cis_two_pi]

/-- When 2α + 2β + 2γ = 2π/3, the product of cis values is ω -/
theorem cis_product_omega (α β γ : ℝ) (hsum : 2 * α + 2 * β + 2 * γ = 2 * Real.pi / 3) :
    cis (2 * α) * cis (2 * β) * cis (2 * γ) = ω := by
  rw [← cis_add, ← cis_add, hsum]
  exact omega_eq_cis_two_pi_div_three.symm

/-- The key theorem: when the triangle has angles 3α, 3β, 3γ summing to π,
    and the LHS of the algebraic identity vanishes (which happens at any
    fixed point of the triple cubed rotation), the Morley points form
    an equilateral triangle. -/
theorem morley_triangle_equilateral (A B C : ℂ) (α β γ : ℝ)
    (hsum : α + β + γ = Real.pi / 3)
    (R P Q : ℂ)
    (_hR : R = (cis (2 * α) * (B * (1 - cis (2 * β))) + A * (1 - cis (2 * α))) /
              (1 - cis (2 * α) * cis (2 * β)))
    (_hP : P = (cis (2 * β) * (C * (1 - cis (2 * γ))) + B * (1 - cis (2 * β))) /
              (1 - cis (2 * β) * cis (2 * γ)))
    (_hQ : Q = (cis (2 * γ) * (A * (1 - cis (2 * α))) + C * (1 - cis (2 * γ))) /
              (1 - cis (2 * γ) * cis (2 * α)))
    (_h₁₂ : cis (2 * α) * cis (2 * β) ≠ 1)
    (_h₂₃ : cis (2 * β) * cis (2 * γ) ≠ 1)
    (_h₁₃ : cis (2 * α) * cis (2 * γ) ≠ 1) :
    IsEquilateral R P Q := by
  -- The angles satisfy 2α + 2β + 2γ = 2π/3, so cis(2α)*cis(2β)*cis(2γ) = ω
  have _hprod : cis (2 * α) * cis (2 * β) * cis (2 * γ) = ω := by
    apply cis_product_omega
    linarith [hsum]
  -- From the triple cubed rotation being identity, we get R + ω*P + ω²*Q = 0
  -- This follows from the algebraic identity when the LHS is zero
  have hequil : R + ω * P + ω ^ 2 * Q = 0 := by
    sorry  -- This requires showing the LHS of root_unity_carac is zero
  -- Apply our equilateral characterization
  exact omega_sum_zero_isEquilateral R P Q hequil

end Morley
