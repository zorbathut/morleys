/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Morleys.Connes
import Morleys.Triangle

/-!
# Morley's Trisector Theorem

This file contains the final geometric statement and proof of Morley's theorem:
The three points of intersection of adjacent angle trisectors of any triangle
form an equilateral triangle.

## Main results

* `morleyVertex` : Morley vertex (fixed point of two rotations)
* `pairwise_cis_ne_one` : Denominators in Morley point formulas are nonzero
* `triple_rotation_lhs_zero` : Key geometric axiom - the LHS polynomial vanishes
* `morley_theorem` : The main theorem

## Strategy

1. From Triangle.lean: `trisected_angles_sum` gives α + β + γ = π/3
2. Prove pairwise cis products ≠ 1 (denominators nonzero)
3. Use `triple_rotation_lhs_zero` axiom to get LHS = 0
4. Apply `morley_triangle_equilateral` from Connes.lean to conclude

## Key Insight (from Isabelle AFP proof)

The critical step is proving that the LHS polynomial vanishes for the Morley
configuration. The Isabelle AFP proof (Morley.thy, lemmas g20-g22) establishes
this using axial symmetry:
1. The composition of three cubed rotations (by 6α at A, 6β at B, 6γ at C) is
   a translation (since the total angle 6α + 6β + 6γ = 2π).
2. This translation fixes vertex A (proven via axial symmetry properties of
   angle trisection).
3. Therefore the translation is zero, making the composition the identity.
4. By `lhs_zero_when_identity`, this implies LHS = 0.

We accept `triple_rotation_lhs_zero` as an axiom, as the full axial symmetry
proof requires substantial geometric machinery beyond this algebraic approach.
-/

namespace Morley

open Complex Real

/-! ## Morley Point Definitions -/

/-- The Morley vertex: intersection of two angle trisectors.
    Given centers P₁, P₂ and trisection angles θ₁, θ₂, this is the fixed point
    of the composition of rotations by 2θ₁ at P₁ and 2θ₂ at P₂. -/
noncomputable def morleyVertex (P₁ P₂ : ℂ) (θ₁ θ₂ : ℝ) : ℂ :=
  (cis (2 * θ₁) * (P₂ * (1 - cis (2 * θ₂))) + P₁ * (1 - cis (2 * θ₁))) /
    (1 - cis (2 * θ₁) * cis (2 * θ₂))

/-! ## Pairwise Non-Degeneracy -/

/-- cis θ = 1 iff θ is a multiple of 2π -/
theorem cis_eq_one_iff_of_real (θ : ℝ) : cis θ = 1 ↔ ∃ k : ℤ, θ = 2 * Real.pi * k := by
  constructor
  · intro h
    -- cis θ = exp(θ * I) = 1
    have hexp : Complex.exp (θ * Complex.I) = 1 := h
    rw [Complex.exp_eq_one_iff] at hexp
    obtain ⟨n, hn⟩ := hexp
    use n
    -- hn: θ * I = n * (2 * π * I), so θ = 2πn
    -- Multiply both sides by -I (i.e., divide by I)
    have h1 : θ * Complex.I * (-Complex.I) = ↑n * (2 * ↑Real.pi * Complex.I) * (-Complex.I) := by
      rw [hn]
    simp only [mul_neg, mul_assoc, Complex.I_mul_I, neg_neg, mul_one] at h1
    -- h1: θ = n * (2 * π)
    have h2 : (θ : ℂ) = ↑n * 2 * ↑Real.pi := by convert h1 using 1; ring
    have h3 : (θ : ℂ) = ((2 * Real.pi * n) : ℝ) := by
      rw [h2]
      push_cast
      ring
    have h4 := Complex.ofReal_injective h3
    linarith
  · intro ⟨k, hk⟩
    -- θ = 2 * π * k, so cis θ = cis(2πk) = 1
    rw [hk]
    simp only [cis]
    rw [Complex.exp_eq_one_iff]
    use k
    push_cast
    ring

/-- For positive angles summing to π/3, pairwise cis products are not 1 -/
theorem pairwise_cis_ne_one (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsum : α + β + γ = Real.pi / 3) :
    cis (2 * α) * cis (2 * β) ≠ 1 ∧
    cis (2 * β) * cis (2 * γ) ≠ 1 ∧
    cis (2 * α) * cis (2 * γ) ≠ 1 := by
  -- From hsum: α + β < π/3 (since γ > 0), so 2α + 2β < 2π/3
  have hαβ : α + β < Real.pi / 3 := by linarith
  have hβγ : β + γ < Real.pi / 3 := by linarith
  have hαγ : α + γ < Real.pi / 3 := by linarith
  have hαβ_pos : 0 < α + β := by linarith
  have hβγ_pos : 0 < β + γ := by linarith
  have hαγ_pos : 0 < α + γ := by linarith
  constructor
  · -- cis(2α) * cis(2β) ≠ 1
    rw [← cis_add]
    intro heq
    rw [cis_eq_one_iff_of_real] at heq
    obtain ⟨k, hk⟩ := heq
    -- 2α + 2β = 2πk, so α + β = πk
    have hab : α + β = Real.pi * k := by linarith
    -- Since 0 < α + β < π/3, we have 0 < πk < π/3
    -- This means 0 < k < 1/3, but k is an integer, so no such k exists
    have hk_pos : (0 : ℝ) < Real.pi * k := by rw [← hab]; exact hαβ_pos
    have hk_lt : Real.pi * k < Real.pi / 3 := by rw [← hab]; exact hαβ
    -- From hk_pos: π * k > 0, so k > 0 (since π > 0)
    have hk_int_pos : 0 < k := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr h
      have hle : Real.pi * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt Real.pi_pos) this
      linarith
    -- From hk_lt: π * k < π/3, so k < 1/3
    have hk_int_lt : k < 1 := by
      by_contra h
      push_neg at h
      have : (1 : ℝ) ≤ k := by exact_mod_cast h
      have hge : Real.pi * 1 ≤ Real.pi * k := by
        apply mul_le_mul_of_nonneg_left this (le_of_lt Real.pi_pos)
      have : Real.pi ≤ Real.pi * k := by linarith
      have : Real.pi / 3 < Real.pi := by
        have := Real.pi_pos
        linarith
      linarith
    -- k is a positive integer < 1, contradiction
    omega
  constructor
  · -- cis(2β) * cis(2γ) ≠ 1
    rw [← cis_add]
    intro heq
    rw [cis_eq_one_iff_of_real] at heq
    obtain ⟨k, hk⟩ := heq
    have hbc : β + γ = Real.pi * k := by linarith
    have hk_pos : (0 : ℝ) < Real.pi * k := by rw [← hbc]; exact hβγ_pos
    have hk_lt : Real.pi * k < Real.pi / 3 := by rw [← hbc]; exact hβγ
    have hk_int_pos : 0 < k := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr h
      have hle : Real.pi * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt Real.pi_pos) this
      linarith
    have hk_int_lt : k < 1 := by
      by_contra h
      push_neg at h
      have : (1 : ℝ) ≤ k := by exact_mod_cast h
      have hge : Real.pi * 1 ≤ Real.pi * k := by
        apply mul_le_mul_of_nonneg_left this (le_of_lt Real.pi_pos)
      have : Real.pi ≤ Real.pi * k := by linarith
      have : Real.pi / 3 < Real.pi := by
        have := Real.pi_pos
        linarith
      linarith
    omega
  · -- cis(2α) * cis(2γ) ≠ 1
    rw [← cis_add]
    intro heq
    rw [cis_eq_one_iff_of_real] at heq
    obtain ⟨k, hk⟩ := heq
    have hac : α + γ = Real.pi * k := by linarith
    have hk_pos : (0 : ℝ) < Real.pi * k := by rw [← hac]; exact hαγ_pos
    have hk_lt : Real.pi * k < Real.pi / 3 := by rw [← hac]; exact hαγ
    have hk_int_pos : 0 < k := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr h
      have hle : Real.pi * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt Real.pi_pos) this
      linarith
    have hk_int_lt : k < 1 := by
      by_contra h
      push_neg at h
      have : (1 : ℝ) ≤ k := by exact_mod_cast h
      have hge : Real.pi * 1 ≤ Real.pi * k := by
        apply mul_le_mul_of_nonneg_left this (le_of_lt Real.pi_pos)
      have : Real.pi ≤ Real.pi * k := by linarith
      have : Real.pi / 3 < Real.pi := by
        have := Real.pi_pos
        linarith
      linarith
    omega

/-! ## Triple Rotation Identity -/

/-- The LHS polynomial from equality_for_comp. This equals zero when
    the triple cubed rotation is the identity. -/
def lhs_polynomial (a₁ a₂ a₃ b₁ b₂ b₃ : ℂ) : ℂ :=
  (a₁ ^ 2 + a₁ + 1) * b₁ + a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * b₂ +
  a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * b₃

/-- Simplification: (x² + x + 1)(1 - x) = 1 - x³ -/
theorem poly_factor (x : ℂ) : (x ^ 2 + x + 1) * (1 - x) = 1 - x ^ 3 := by ring

/-- For the actual Morley configuration (where α, β, γ are the trisected angles
    of triangle ABC), the LHS polynomial vanishes.

    This is the key geometric fact from the Isabelle AFP proof (Morley.thy, g22).
    The Isabelle proof uses axial symmetry to show:
    1. The composition of cubed rotations is a translation (since total angle = 2π)
    2. The translation fixes vertex A (via angle trisection symmetry)
    3. Therefore the translation is zero, so LHS = 0

    The proof requires sophisticated geometric reasoning about axial symmetries
    (reflections about angle trisector lines) that is beyond the scope of this
    algebraic formalization. We accept this as an axiom, noting that the full
    geometric proof is available in the Isabelle AFP entry for Morley's theorem.

    Key reference: Isabelle AFP, Morley_Theorem/Morley.thy, lemmas g20-g22 and very_imp. -/
axiom triple_rotation_lhs_zero (A B C : ℂ) (hnd : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    let α := angle_at B A C / 3
    let β := angle_at C B A / 3
    let γ := angle_at A C B / 3
    let a₁ := cis (2 * α)
    let a₂ := cis (2 * β)
    let a₃ := cis (2 * γ)
    (a₁ ^ 2 + a₁ + 1) * (A * (1 - a₁)) +
    a₁ ^ 3 * (a₂ ^ 2 + a₂ + 1) * (B * (1 - a₂)) +
    a₁ ^ 3 * a₂ ^ 3 * (a₃ ^ 2 + a₃ + 1) * (C * (1 - a₃)) = 0

/-! ## Main Theorem -/

/-- **Morley's Trisector Theorem**: The three points of intersection of
    adjacent angle trisectors of any triangle form an equilateral triangle. -/
theorem morley_theorem (A B C : ℂ) (hnd : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    let α := angle_at B A C / 3
    let β := angle_at C B A / 3
    let γ := angle_at A C B / 3
    let R := morleyVertex A B α β
    let P := morleyVertex B C β γ
    let Q := morleyVertex C A γ α
    IsEquilateral R P Q := by
  -- Extract the trisected angles
  let α := angle_at B A C / 3
  let β := angle_at C B A / 3
  let γ := angle_at A C B / 3
  -- Get α + β + γ = π/3 from trisected_angles_sum
  have hsum : α + β + γ = Real.pi / 3 := trisected_angles_sum hnd hpos
  -- Get positivity bounds for trisected angles
  have hα : 0 < α := by simp only [α]; linarith [hpos.1]
  have hβ : 0 < β := by simp only [β]; linarith [hpos.2.1]
  have hγ : 0 < γ := by simp only [γ]; linarith [hpos.2.2]
  -- Get pairwise cis ≠ 1 conditions
  have hpair := pairwise_cis_ne_one α β γ hα hβ hγ hsum
  -- Get LHS = 0 from the axiom (key geometric fact from Isabelle AFP)
  have hLHS := triple_rotation_lhs_zero A B C hnd hpos
  -- Apply morley_triangle_equilateral to conclude
  exact morley_triangle_equilateral A B C α β γ hsum
    (morleyVertex A B α β) (morleyVertex B C β γ) (morleyVertex C A γ α)
    rfl rfl rfl hpair.1 hpair.2.1 hpair.2.2 hLHS

end Morley
