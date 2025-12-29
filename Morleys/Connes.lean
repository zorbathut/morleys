/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Exponential
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

    The identity was verified in Isabelle's AFP (Morley_Theorem/Third_Unity_Root.thy).
    The Lean proof requires extensive polynomial manipulation that exceeds tactic limits.
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
  simp only
  have _hω3 : ω ^ 3 = 1 := omega_cubed
  have _hω2 : ω ^ 2 = -1 - ω := omega_sq_eq
  have _hωsum : 1 + ω + ω ^ 2 = 0 := one_add_omega_add_omega_sq
  have h13' : 1 - a₃ * a₁ = 1 - a₁ * a₃ := by ring
  -- Key simplification: (1 - aᵢ*aⱼ)*aₖ = aₖ - ω when a₁*a₂*a₃ = ω
  have _hsimp₁₂ : (1 - a₁ * a₂) * a₃ = a₃ - ω := by
    calc (1 - a₁ * a₂) * a₃ = a₃ - a₁ * a₂ * a₃ := by ring
      _ = a₃ - ω := by rw [hprod]
  have _hsimp₂₃ : (1 - a₂ * a₃) * a₁ = a₁ - ω := by
    calc (1 - a₂ * a₃) * a₁ = a₁ - a₂ * a₃ * a₁ := by ring
      _ = a₁ - a₁ * a₂ * a₃ := by ring
      _ = a₁ - ω := by rw [hprod]
  have _hsimp₁₃ : (1 - a₁ * a₃) * a₂ = a₂ - ω := by
    calc (1 - a₁ * a₃) * a₂ = a₂ - a₁ * a₃ * a₂ := by ring
      _ = a₂ - a₁ * a₂ * a₃ := by ring
      _ = a₂ - ω := by rw [hprod]
  -- Clear denominators and verify the polynomial identity
  -- This is a massive computation verified in Isabelle (see Third_Unity_Root.thy)
  field_simp [h₁₂, h₂₃, h₁₃, h13']
  -- The polynomial identity is proven using Lean 4.21's grind tactic with Gröbner basis
  -- The identity holds using ω³ = 1 and 1 + ω + ω² = 0 (from hωsum, hω3 in context)
  grind

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

/-- When the triple cubed rotation is the identity, the constant term (LHS) is zero.
    This follows from equality_for_comp: composition = (a₁a₂a₃)³ * z + LHS.
    When (a₁a₂a₃)³ = 1 and composition = id, we have z = z + LHS, so LHS = 0. -/
theorem lhs_zero_when_identity (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ)
    (_hcubed : (a₁ * a₂ * a₃) ^ 3 = 1)
    (hid : ∀ z, (fun w => a₁ * (a₁ * (a₁ * (a₂ * (a₂ * (a₂ * (a₃ * (a₃ * (a₃ * w + b₃) + b₃) + b₃) + b₂) + b₂) + b₂) + b₁) + b₁) + b₁) z = z) :
    (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
      a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ = 0 := by
  -- Use equality_for_comp at z = 0
  have hid0 := hid 0
  -- The composition at 0 equals LHS (since (a₁a₂a₃)³ * 0 = 0)
  -- Simplify: the nested composition at 0 gives LHS
  have hsimp : a₁ * (a₁ * (a₁ * (a₂ * (a₂ * (a₂ * (a₃ * (a₃ * (a₃ * 0 + b₃) + b₃) + b₃) + b₂) + b₂) + b₂) + b₁) + b₁) + b₁ =
      (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ + a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ := by
    ring
  simp only [hsimp] at hid0
  exact hid0

/-- The key theorem: when the triangle has angles 3α, 3β, 3γ summing to π,
    and the LHS of the algebraic identity vanishes (which happens when
    the triple cubed rotation is the identity), the Morley points form
    an equilateral triangle.

    The condition hLHS encapsulates that the composition of three cubed rotations
    is the identity, which is derived from the geometric setup in the full proof.

    **Variable assignment** (for (A,B,C) order - first rotate at A, then B, then C):
    - a₁ = cis(2γ), b₁ = C*(1-a₁)  (outermost rotation at C)
    - a₂ = cis(2β), b₂ = B*(1-a₂)  (middle rotation at B)
    - a₃ = cis(2α), b₃ = A*(1-a₃)  (innermost rotation at A)

    This swaps (A,α) ↔ (C,γ) compared to the (C,B,A) order, giving an LHS that
    equals the (A,B,C) translation formula which IS zero for any triangle. -/
theorem morley_triangle_equilateral (A B C : ℂ) (α β γ : ℝ)
    (hsum : α + β + γ = Real.pi / 3)
    (R P Q : ℂ)
    -- R = fixed point of (rotation at C) ∘ (rotation at B)
    (hR : R = (cis (2 * γ) * (B * (1 - cis (2 * β))) + C * (1 - cis (2 * γ))) /
              (1 - cis (2 * γ) * cis (2 * β)))
    -- P = fixed point of (rotation at B) ∘ (rotation at A)
    (hP : P = (cis (2 * β) * (A * (1 - cis (2 * α))) + B * (1 - cis (2 * β))) /
              (1 - cis (2 * β) * cis (2 * α)))
    -- Q = fixed point of (rotation at A) ∘ (rotation at C)
    (hQ : Q = (cis (2 * α) * (C * (1 - cis (2 * γ))) + A * (1 - cis (2 * α))) /
              (1 - cis (2 * α) * cis (2 * γ)))
    (h₁₂ : cis (2 * γ) * cis (2 * β) ≠ 1)
    (h₂₃ : cis (2 * β) * cis (2 * α) ≠ 1)
    (h₁₃ : cis (2 * γ) * cis (2 * α) ≠ 1)
    -- This is the key condition: LHS = 0 (swapped assignment for (A,B,C) order)
    (hLHS : (cis (2 * γ) ^ 2 + cis (2 * γ) + 1) * (C * (1 - cis (2 * γ))) +
            cis (2 * γ) ^ 3 * (cis (2 * β) ^ 2 + cis (2 * β) + 1) * (B * (1 - cis (2 * β))) +
            cis (2 * γ) ^ 3 * cis (2 * β) ^ 3 * (cis (2 * α) ^ 2 + cis (2 * α) + 1) *
              (A * (1 - cis (2 * α))) = 0) :
    IsEquilateral R P Q := by
  -- Set up notation (swapped: a₁↔γ/C, a₃↔α/A)
  let a₁ := cis (2 * γ)
  let a₂ := cis (2 * β)
  let a₃ := cis (2 * α)
  let b₁ := C * (1 - a₁)
  let b₂ := B * (1 - a₂)
  let b₃ := A * (1 - a₃)
  -- The angles satisfy 2α + 2β + 2γ = 2π/3, so cis(2γ)*cis(2β)*cis(2α) = ω
  have hprod : a₁ * a₂ * a₃ = ω := by
    apply cis_product_omega
    linarith [hsum]
  -- Show cis values are nonzero
  have ha₁ : a₁ ≠ 0 := cis_ne_zero (2 * γ)
  have ha₂ : a₂ ≠ 0 := cis_ne_zero (2 * β)
  have ha₃ : a₃ ≠ 0 := cis_ne_zero (2 * α)
  -- Convert h₁₂, h₂₃, h₁₃ to the form needed
  have h₁₂' : 1 - a₁ * a₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₂)
  have h₂₃' : 1 - a₂ * a₃ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂₃)
  have h₁₃' : 1 - a₁ * a₃ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₃)
  -- Need to show a_i ≠ ω
  have ha₁ω : a₁ ≠ ω := by
    intro heq
    have hp := hprod
    rw [heq] at hp
    -- hp: ω * a₂ * a₃ = ω, so a₂ * a₃ = 1
    have h3 : a₂ * a₃ = 1 := by
      have h1 : ω * a₂ * a₃ = ω := hp
      have h2 : ω * (a₂ * a₃) = ω * 1 := by simp only [mul_one]; ring_nf at h1 ⊢; exact h1
      exact mul_left_cancel₀ omega_ne_zero h2
    exact h₂₃ h3
  have ha₂ω : a₂ ≠ ω := by
    intro heq
    have hp := hprod
    rw [heq] at hp
    -- hp: a₁ * ω * a₃ = ω, so a₁ * a₃ = 1
    have h3 : a₁ * a₃ = 1 := by
      have h1 : a₁ * ω * a₃ = ω := hp
      have h2 : (a₁ * a₃) * ω = 1 * ω := by simp only [one_mul]; ring_nf at h1 ⊢; exact h1
      exact mul_right_cancel₀ omega_ne_zero h2
    exact h₁₃ h3
  have ha₃ω : a₃ ≠ ω := by
    intro heq
    have hp := hprod
    rw [heq] at hp
    -- hp: a₁ * a₂ * ω = ω, so a₁ * a₂ = 1
    have h3 : a₁ * a₂ = 1 := by
      have h1 : a₁ * a₂ * ω = ω := hp
      have h2 : (a₁ * a₂) * ω = 1 * ω := by simp only [one_mul]; exact h1
      exact mul_right_cancel₀ omega_ne_zero h2
    exact h₁₂ h3
  -- Now use morley_equilateral_condition
  have hLHS' : (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
               a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃ = 0 := hLHS
  have hequil := morley_equilateral_condition a₁ a₂ a₃ b₁ b₂ b₃
                   hprod h₁₂' h₂₃' h₁₃' ha₁ ha₂ ha₃ ha₁ω ha₂ω ha₃ω hLHS'
  -- hequil gives us: (a₁ * b₂ + b₁) / (1 - a₁ * a₂) + ω * P' + ω² * Q' = 0
  -- where P' = (a₂ * b₃ + b₂) / (1 - a₂ * a₃) and Q' = (a₃ * b₁ + b₃) / (1 - a₁ * a₃)
  -- Show R, P, Q match the forms in morley_equilateral_condition
  have hRdef : (a₁ * b₂ + b₁) / (1 - a₁ * a₂) =
      (cis (2 * γ) * (B * (1 - cis (2 * β))) + C * (1 - cis (2 * γ))) / (1 - cis (2 * γ) * cis (2 * β)) := by
    rfl
  have hPdef : (a₂ * b₃ + b₂) / (1 - a₂ * a₃) =
      (cis (2 * β) * (A * (1 - cis (2 * α))) + B * (1 - cis (2 * β))) / (1 - cis (2 * β) * cis (2 * α)) := by
    rfl
  have h13' : (1 : ℂ) - a₃ * a₁ = 1 - a₁ * a₃ := by ring
  have hQdef : (a₃ * b₁ + b₃) / (1 - a₁ * a₃) =
      (cis (2 * α) * (C * (1 - cis (2 * γ))) + A * (1 - cis (2 * α))) / (1 - cis (2 * α) * cis (2 * γ)) := by
    simp only [a₁, a₃, b₁, b₃, h13']
  -- Convert to R, P, Q
  have hequil' : R + ω * P + ω ^ 2 * Q = 0 := by
    rw [hR, hP, hQ, ← hRdef, ← hPdef, ← hQdef]
    exact hequil
  exact omega_sum_zero_isEquilateral R P Q hequil'

end Morley
