/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Morleys.CubeRoot

/-!
# Trigonometric Identities for Morley's Theorem

This file provides trigonometric identities needed for Morley's theorem.
The main triple angle formulas are already in Mathlib:

* `Real.sin_three_mul` : sin(3x) = 3·sin(x) - 4·sin³(x)
* `Real.cos_three_mul` : cos(3x) = 4·cos³(x) - 3·cos(x)
* `Complex.sin_three_mul` : sin(3x) = 3·sin(x) - 4·sin³(x)  (for Complex)
* `Complex.cos_three_mul` : cos(3x) = 4·cos³(x) - 3·cos(x)  (for Complex)

This file adds convenience results about ω = e^(2πi/3).
-/

namespace Morley

open Complex Real

/-- The ω we defined equals cos(2π/3) + i·sin(2π/3) -/
theorem omega_eq_cis : ω = Complex.cos (2 * Real.pi / 3) + Complex.I * Complex.sin (2 * Real.pi / 3) := by
  rw [omega_eq]
  rw [Complex.exp_mul_I]
  ring

/-- Complex.cos at a real argument equals the real cos cast to complex -/
theorem complex_cos_of_real (x : ℝ) : Complex.cos (x : ℂ) = (Real.cos x : ℂ) := by
  rw [← Complex.ofReal_cos]

/-- Complex.sin at a real argument equals the real sin cast to complex -/
theorem complex_sin_of_real (x : ℝ) : Complex.sin (x : ℂ) = (Real.sin x : ℂ) := by
  rw [← Complex.ofReal_sin]

/-- cos(2π/3) = -1/2 (as a real number) -/
theorem real_cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1/2 := by
  -- Use cos(2π/3) = cos(π - π/3) = -cos(π/3) = -1/2
  have h2 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h2, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

/-- sin(2π/3) = √3/2 (as a real number) -/
theorem real_sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  -- Use sin(2π/3) = sin(π - π/3) = sin(π/3) = √3/2
  have h2 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [h2, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- Real part of ω is -1/2 -/
theorem omega_re : ω.re = -1/2 := by
  rw [omega_eq_cis]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h1 : (2 * Real.pi / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) := by simp
  rw [h1]
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  simp [real_cos_two_pi_div_three]

/-- Imaginary part of ω is √3/2 -/
theorem omega_im : ω.im = Real.sqrt 3 / 2 := by
  rw [omega_eq_cis]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 : (2 * Real.pi / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) := by simp
  rw [h1]
  rw [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
  simp [real_sin_two_pi_div_three]

/-- ω written in rectangular form -/
theorem omega_rect : ω = -1/2 + Complex.I * (Real.sqrt 3 / 2) := by
  apply Complex.ext
  · simp [omega_re]
  · simp [omega_im]

end Morley
