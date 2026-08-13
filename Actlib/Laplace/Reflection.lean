import Mathlib

/-!
# Reflection with conventions

This file formalizes the lemma labelled `lem:reflection` and titled
**Reflection with conventions** in `wright_laplace.tex` ("A contour-free proof of the
unit-scale positive-stable Laplace-transform identity"):

> For every real `x > 0` (including `x ∈ ℤ_{>0}`, using Convention `conv:junk`),
> `1/Γ(-x) = -sin(π x) Γ(x+1)/π`.

Convention `conv:junk` of the source is exactly Lean's/Mathlib's junk-value convention:
`Real.Gamma` vanishes at the non-positive integers, and division by zero is zero, so
`1/Γ(-x) = 0` when `x` is a positive integer, matching the right-hand side because
`sin(π x) = 0` there.
-/

namespace WrightLaplace

open Real

/-- **Reflection with conventions**, the lemma `lem:reflection` of `wright_laplace.tex`.

For every real `x > 0` one has `1/Γ(-x) = -sin(π x) Γ(x+1)/π`, where, following
Convention `conv:junk` of the source (and Mathlib's junk-value conventions), both sides are
`0` when `x` is a positive integer. -/
theorem one_div_Gamma_neg (x : ℝ) (hx : 0 < x) :
    1 / Real.Gamma (-x) = -(Real.sin (π * x) * Real.Gamma (x + 1)) / π := by
  -- Euler's reflection formula at `s = -x`.
  have hrefl : Real.Gamma (-x) * Real.Gamma (1 - -x) = π / Real.sin (π * -x) :=
    Real.Gamma_mul_Gamma_one_sub (-x)
  have hsub : (1 : ℝ) - -x = x + 1 := by ring
  rw [hsub, mul_neg, Real.sin_neg] at hrefl
  by_cases hint : ∃ m : ℕ, x = m
  · -- `x` is a positive integer: both sides vanish.
    obtain ⟨m, rfl⟩ := hint
    have hGam : Real.Gamma (-(m : ℝ)) = 0 := (Real.Gamma_eq_zero_iff _).2 ⟨m, rfl⟩
    have hsin : Real.sin (π * m) = 0 := by
      simpa [mul_comm] using Real.sin_int_mul_pi (m : ℤ)
    rw [hGam, hsin]
    simp
  · -- `x` is not an integer: divide the reflection formula.
    have hpi : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
    have hsin : Real.sin (π * x) ≠ 0 := by
      rw [Real.sin_ne_zero_iff]
      intro n hn
      have hnx : (n : ℝ) = x := mul_right_cancel₀ hpi (by linear_combination hn)
      have hn0 : 0 < n := by
        have : (0 : ℝ) < (n : ℝ) := by rw [hnx]; exact hx
        exact_mod_cast this
      exact hint ⟨n.toNat, by rw [← hnx]; exact_mod_cast (Int.toNat_of_nonneg hn0.le).symm⟩
    have hGam : Real.Gamma (-x) ≠ 0 := by
      refine Real.Gamma_ne_zero ?_
      intro m hm
      exact hint ⟨m, by linarith [hm]⟩
    have key : Real.Gamma (-x) * Real.Gamma (x + 1) * (-Real.sin (x * π)) = π := by
      rw [mul_comm x π, hrefl]; field_simp
    rw [mul_comm π x]
    field_simp
    linear_combination -key

/-- The lemma `lem:reflection` of `wright_laplace.tex` extended to `x = 0`, where both sides
vanish by Convention `conv:junk` (`Γ(0) = 0`, hence `1/Γ(0) = 0`, and `sin 0 = 0`).  This is the
form in which the reflection formula is applied in the proof of the lemma `lem:ray`, where the
index `k = 0` gives `x = a·0 = 0`. -/
theorem one_div_Gamma_neg_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    1 / Real.Gamma (-x) = -(Real.sin (π * x) * Real.Gamma (x + 1)) / π := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h, Real.Gamma_zero]
  · exact one_div_Gamma_neg x h

end WrightLaplace
