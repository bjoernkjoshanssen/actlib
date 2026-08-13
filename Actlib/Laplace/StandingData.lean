import Mathlib

/-!
# Standing data

This file formalizes the **standing data** of `wright_laplace.tex` ("A contour-free proof of the
unit-scale positive-stable Laplace-transform identity"), namely the angle `θ` of equation
`eq:theta`,
`θ := ½(π/2 + min(π, π/(2a)))`, together with the strictly positive constants
`c₁ := -cos θ` and `c₂ := cos(a θ)`, all attached to the standing datum `a ∈ (0,1)`.

The basic facts recorded in the source right after `eq:theta` are proved here:
`π/2 < θ < min(π, π/(2a))`, `c₁ > 0`, `c₂ > 0` and `sin θ > 0`.
-/

namespace WrightLaplace

open Real

/-- The angle `θ` of equation `eq:theta` in `wright_laplace.tex`:
`θ := ½(π/2 + min(π, π/(2a)))`, for the standing datum `a ∈ (0,1)`. -/
noncomputable def theta (a : ℝ) : ℝ := (π / 2 + min π (π / (2 * a))) / 2

/-- The constant `c₁ := -cos θ` of the standing data of `wright_laplace.tex`. -/
noncomputable def c₁ (a : ℝ) : ℝ := -Real.cos (theta a)

/-- The constant `c₂ := cos(a θ)` of the standing data of `wright_laplace.tex`. -/
noncomputable def c₂ (a : ℝ) : ℝ := Real.cos (a * theta a)

/-- Lower bound `π/2 < θ` from equation `eq:theta` of `wright_laplace.tex`. -/
theorem pi_div_two_lt_theta {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : π / 2 < theta a := by
  have hpi := Real.pi_pos
  have h1 : π / 2 < π / (2 * a) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h2 : π / 2 < π := by linarith
  have : π / 2 < min π (π / (2 * a)) := lt_min h2 h1
  unfold theta
  linarith

/-- Upper bound `θ < min(π, π/(2a))` from equation `eq:theta` of `wright_laplace.tex`. -/
theorem theta_lt_min {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    theta a < min π (π / (2 * a)) := by
  have hpi := Real.pi_pos
  have h1 : π / 2 < π / (2 * a) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h2 : π / 2 < π := by linarith
  have : π / 2 < min π (π / (2 * a)) := lt_min h2 h1
  unfold theta
  linarith

/-- `θ < π`, part of equation `eq:theta` of `wright_laplace.tex`. -/
theorem theta_lt_pi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : theta a < π :=
  lt_of_lt_of_le (theta_lt_min ha0 ha1) (min_le_left _ _)

/-- `a θ < π/2`, a consequence of `θ < π/(2a)` in equation `eq:theta` of `wright_laplace.tex`. -/
theorem mul_theta_lt_pi_div_two {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : a * theta a < π / 2 := by
  have h := lt_of_lt_of_le (theta_lt_min ha0 ha1) (min_le_right _ _)
  have h2 : a * theta a < a * (π / (2 * a)) := by
    exact mul_lt_mul_of_pos_left h ha0
  rw [show a * (π / (2 * a)) = π / 2 by field_simp] at h2
  exact h2

/-- Positivity of `θ`. -/
theorem theta_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < theta a :=
  lt_trans (by positivity) (pi_div_two_lt_theta ha0 ha1)

/-- `c₁ = -cos θ > 0`, as noted in the standing data of `wright_laplace.tex`
(because `θ ∈ (π/2, π)`). -/
theorem c₁_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < c₁ a := by
  have h : Real.cos (theta a) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (pi_div_two_lt_theta ha0 ha1)
      (by linarith [theta_lt_pi ha0 ha1, Real.pi_pos])
  simpa [c₁] using h

/-- `c₂ = cos(a θ) > 0`, as noted in the standing data of `wright_laplace.tex`
(because `0 < a θ < π/2`). -/
theorem c₂_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < c₂ a := by
  refine Real.cos_pos_of_mem_Ioo ⟨?_, mul_theta_lt_pi_div_two ha0 ha1⟩
  have : 0 < a * theta a := mul_pos ha0 (theta_pos ha0 ha1)
  linarith [Real.pi_pos]

/-- `sin θ > 0`, as noted in the standing data of `wright_laplace.tex`. -/
theorem sin_theta_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < Real.sin (theta a) :=
  Real.sin_pos_of_pos_of_lt_pi (theta_pos ha0 ha1) (theta_lt_pi ha0 ha1)

end WrightLaplace
