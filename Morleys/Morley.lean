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

* `morleyR`, `morleyP`, `morleyQ` : The three Morley vertices
* `pairwise_cis_ne_one` : Denominators in Morley point formulas are nonzero
* `morley_sum_zero` : Direct proof that R + ωP + ω²Q = 0
* `morley_theorem` : The main theorem

## Strategy

1. From Triangle.lean: `trisected_angles_sum` gives α + β + γ = π/3
2. Prove pairwise cis products ≠ 1 (denominators nonzero)
3. Prove R + ωP + ω²Q = 0 directly via `grind` on the polynomial identity
4. Apply `omega_sum_zero_isEquilateral` to conclude
-/

namespace Morley

open Complex Real

/-! ## Morley Point Definitions -/

/-- The Morley vertex R: intersection of trisectors from A and B.
    This is the fixed point of the composition of rotations by 2α at A and 2β at B. -/
noncomputable def morleyR (A B : ℂ) (α β : ℝ) : ℂ :=
  (cis (2 * α) * (B * (1 - cis (2 * β))) + A * (1 - cis (2 * α))) /
    (1 - cis (2 * α) * cis (2 * β))

/-- The Morley vertex P: intersection of trisectors from B and C. -/
noncomputable def morleyP (B C : ℂ) (β γ : ℝ) : ℂ :=
  (cis (2 * β) * (C * (1 - cis (2 * γ))) + B * (1 - cis (2 * β))) /
    (1 - cis (2 * β) * cis (2 * γ))

/-- The Morley vertex Q: intersection of trisectors from C and A. -/
noncomputable def morleyQ (C A : ℂ) (γ α : ℝ) : ℂ :=
  (cis (2 * γ) * (A * (1 - cis (2 * α))) + C * (1 - cis (2 * γ))) /
    (1 - cis (2 * γ) * cis (2 * α))

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
    have h2 : (θ : ℂ) = ↑n * 2 * ↑Real.pi := by convert h1 using 1 <;> ring
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

/-! ## Equilateral Condition -/

/-- Direct proof that R + ωP + ω²Q = 0 for Morley points.
    This is the equilateral condition proved directly via algebraic manipulation. -/
theorem morley_sum_zero (A B C : ℂ) (α β γ : ℝ)
    (hsum : α + β + γ = Real.pi / 3)
    (h₁₂ : cis (2 * α) * cis (2 * β) ≠ 1)
    (h₂₃ : cis (2 * β) * cis (2 * γ) ≠ 1)
    (h₁₃ : cis (2 * α) * cis (2 * γ) ≠ 1) :
    let R := morleyR A B α β
    let P := morleyP B C β γ
    let Q := morleyQ C A γ α
    R + ω * P + ω ^ 2 * Q = 0 := by
  simp only
  -- Set up notation
  let a₁ := cis (2 * α)
  let a₂ := cis (2 * β)
  let a₃ := cis (2 * γ)
  let b₁ := A * (1 - a₁)
  let b₂ := B * (1 - a₂)
  let b₃ := C * (1 - a₃)
  -- The product a₁a₂a₃ = ω from angle sum
  have hprod : a₁ * a₂ * a₃ = ω := cis_product_omega α β γ (by linarith)
  -- Convert denominators to nonzero form
  have h₁₂' : 1 - a₁ * a₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₂)
  have h₂₃' : 1 - a₂ * a₃ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂₃)
  have h₁₃' : 1 - a₁ * a₃ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₃)
  have h₃₁' : 1 - a₃ * a₁ ≠ 0 := by rw [mul_comm]; exact h₁₃'
  -- cis values are nonzero
  have ha₁ : a₁ ≠ 0 := cis_ne_zero (2 * α)
  have ha₂ : a₂ ≠ 0 := cis_ne_zero (2 * β)
  have ha₃ : a₃ ≠ 0 := cis_ne_zero (2 * γ)
  -- aᵢ ≠ ω (else product constraint would force another pair to 1)
  have ha₁ω : a₁ ≠ ω := by
    intro heq
    rw [heq] at hprod
    have h3 : a₂ * a₃ = 1 := by
      have h1 : ω * a₂ * a₃ = ω := hprod
      have h2 : ω * (a₂ * a₃) = ω * 1 := by simp only [mul_one]; ring_nf at h1 ⊢; exact h1
      exact mul_left_cancel₀ omega_ne_zero h2
    exact h₂₃ h3
  have ha₂ω : a₂ ≠ ω := by
    intro heq
    rw [heq] at hprod
    have h3 : a₁ * a₃ = 1 := by
      have h1 : a₁ * ω * a₃ = ω := hprod
      have h2 : (a₁ * a₃) * ω = 1 * ω := by simp only [one_mul]; ring_nf at h1 ⊢; exact h1
      exact mul_right_cancel₀ omega_ne_zero h2
    exact h₁₃ h3
  have ha₃ω : a₃ ≠ ω := by
    intro heq
    rw [heq] at hprod
    have h3 : a₁ * a₂ = 1 := by
      have h1 : a₁ * a₂ * ω = ω := hprod
      have h2 : (a₁ * a₂) * ω = 1 * ω := by simp only [one_mul]; exact h1
      exact mul_right_cancel₀ omega_ne_zero h2
    exact h₁₂ h3
  -- Unfold the Morley point definitions
  unfold morleyR morleyP morleyQ
  -- Use root_unity_carac: LHS = coeff * (R + ωP + ω²Q)
  -- When LHS = 0 (which we can verify algebraically), R + ωP + ω²Q = 0
  -- Actually, we prove R + ωP + ω²Q = 0 directly by field_simp and grind
  have h13' : (1 : ℂ) - a₃ * a₁ = 1 - a₁ * a₃ := by ring
  rw [h13']
  field_simp [h₁₂', h₂₃', h₁₃']
  -- The polynomial identity: when a₁a₂a₃ = ω, the numerator vanishes
  -- This is verified using grind with the ω identities
  have _hω3 : ω ^ 3 = 1 := omega_cubed
  have _hω2 : ω ^ 2 = -1 - ω := omega_sq_eq
  have _hωsum : 1 + ω + ω ^ 2 = 0 := one_add_omega_add_omega_sq
  grind

/-! ## Main Theorem -/

/-- **Morley's Trisector Theorem**: The three points of intersection of
    adjacent angle trisectors of any triangle form an equilateral triangle. -/
theorem morley_theorem (A B C : ℂ) (hnd : NonCollinear A B C)
    (hpos : 0 < angle_at B A C ∧ 0 < angle_at C B A ∧ 0 < angle_at A C B) :
    let α := angle_at B A C / 3
    let β := angle_at C B A / 3
    let γ := angle_at A C B / 3
    let R := morleyR A B α β
    let P := morleyP B C β γ
    let Q := morleyQ C A γ α
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
  -- Get R + ωP + ω²Q = 0 directly from morley_sum_zero
  have hequil := morley_sum_zero A B C α β γ hsum hpair.1 hpair.2.1 hpair.2.2
  -- Apply omega_sum_zero_isEquilateral to conclude
  exact omega_sum_zero_isEquilateral (morleyR A B α β) (morleyP B C β γ) (morleyQ C A γ α) hequil

end Morley
