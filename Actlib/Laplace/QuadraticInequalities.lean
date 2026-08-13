import Mathlib
import Actlib.Laplace.StandingData

/-!
# Two quadratic inequalities

This file formalizes the lemma labelled `lem:quad` and titled **Two quadratic inequalities**
in `wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable
Laplace-transform identity"):

> For all `v ≥ 0` and `ψ ∈ [0, π]`,
> `|t - v e^{iψ}|² = (v - t cos ψ)² + t² sin²ψ ≥ t² sin²ψ`  (equation `eq:quad1`),
> `|t - v e^{iψ}|² = (t - v)² + 2 t v (1 - cos ψ) ≥ (t - v)²`  (equation `eq:quad2`).
> In particular `t - v e^{iψ} ≠ 0` whenever `sin ψ > 0`, and
> `Re(t - v e^{iψ}) = t - v cos ψ ≥ t + c₁ v > 0` when `ψ = θ`.

Here `t > 0` is the standing datum of the paper and `θ`, `c₁` are as in
`RequestProject/StandingData.lean`.  The two displayed identities are stated without
hypotheses on `t`, `v`, `ψ` (they hold for all reals); the hypotheses `t ≥ 0`, `v ≥ 0` of the
source are used only for the inequality in `eq:quad2`.  The hypothesis `ψ ∈ [0, π]` of the
source is not needed for any of the statements.
-/

namespace WrightLaplace

open Real Complex

/-- The identity in equation `eq:quad1` of the lemma `lem:quad` ("Two quadratic inequalities")
of `wright_laplace.tex`: `|t - v e^{iψ}|² = (v - t cos ψ)² + t² sin²ψ`. -/
theorem normSq_sub_mul_exp_eq (t v ψ : ℝ) :
    ‖(t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ ^ 2
      = (v - t * Real.cos ψ) ^ 2 + t ^ 2 * Real.sin ψ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.exp_ofReal_mul_I_re]
  linear_combination (v ^ 2 - t ^ 2) * Real.sin_sq_add_cos_sq ψ

/-- The inequality in equation `eq:quad1` of the lemma `lem:quad`
("Two quadratic inequalities") of `wright_laplace.tex`: `|t - v e^{iψ}|² ≥ t² sin²ψ`. -/
theorem sq_sin_mul_le_normSq_sub_mul_exp (t v ψ : ℝ) :
    t ^ 2 * Real.sin ψ ^ 2
      ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ ^ 2 := by
  rw [normSq_sub_mul_exp_eq]
  nlinarith [sq_nonneg (v - t * Real.cos ψ)]

/-- The identity in equation `eq:quad2` of the lemma `lem:quad` ("Two quadratic inequalities")
of `wright_laplace.tex`: `|t - v e^{iψ}|² = (t - v)² + 2 t v (1 - cos ψ)`. -/
theorem normSq_sub_mul_exp_eq' (t v ψ : ℝ) :
    ‖(t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ ^ 2
      = (t - v) ^ 2 + 2 * t * v * (1 - Real.cos ψ) := by
  rw [normSq_sub_mul_exp_eq]
  nlinarith [Real.sin_sq_add_cos_sq ψ]

/-- The inequality in equation `eq:quad2` of the lemma `lem:quad`
("Two quadratic inequalities") of `wright_laplace.tex`: `|t - v e^{iψ}|² ≥ (t - v)²`,
valid for `t ≥ 0` and `v ≥ 0`. -/
theorem sq_sub_le_normSq_sub_mul_exp {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v) (ψ : ℝ) :
    (t - v) ^ 2 ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ ^ 2 := by
  rw [normSq_sub_mul_exp_eq']
  have h : 0 ≤ 1 - Real.cos ψ := by linarith [Real.cos_le_one ψ]
  have h2 : 0 ≤ 2 * t * v * (1 - Real.cos ψ) := mul_nonneg (by positivity) h
  linarith

/-- The first "in particular" clause of the lemma `lem:quad` ("Two quadratic inequalities")
of `wright_laplace.tex`: `t - v e^{iψ} ≠ 0` whenever `t > 0` and `sin ψ > 0`. -/
theorem sub_mul_exp_ne_zero {t ψ : ℝ} (ht : 0 < t) (hψ : 0 < Real.sin ψ) (v : ℝ) :
    (t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have h0 := sq_sin_mul_le_normSq_sub_mul_exp t v ψ
  rw [h] at h0
  have hpos : 0 < t ^ 2 * Real.sin ψ ^ 2 := mul_pos (pow_pos ht 2) (pow_pos hψ 2)
  apply lt_irrefl (0 : ℝ)
  apply lt_of_lt_of_le hpos
  convert h0 using 0
  simp

/-- The real part computation in the lemma `lem:quad` ("Two quadratic inequalities") of
`wright_laplace.tex`: `Re(t - v e^{iψ}) = t - v cos ψ`. -/
theorem re_sub_mul_exp (t v ψ : ℝ) :
    ((t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)).re = t - v * Real.cos ψ := by
  simp [Complex.exp_ofReal_mul_I_re]

/-- The last "in particular" clause of the lemma `lem:quad` ("Two quadratic inequalities")
of `wright_laplace.tex`: at the standing angle `ψ = θ` one has
`Re(t - v e^{iθ}) = t - v cos θ = t + c₁ v`. -/
theorem re_sub_mul_exp_theta (a t v : ℝ) :
    ((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)).re = t + c₁ a * v := by
  rw [re_sub_mul_exp]
  simp [c₁]
  ring

/-- The last "in particular" clause of the lemma `lem:quad` ("Two quadratic inequalities")
of `wright_laplace.tex`: at the standing angle `ψ = θ` the real part
`Re(t - v e^{iθ}) = t + c₁ v` is strictly positive, for `t > 0` and `v ≥ 0`. -/
theorem re_sub_mul_exp_theta_pos {a t v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hv : 0 ≤ v) :
    0 < ((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)).re := by
  rw [re_sub_mul_exp_theta]
  have h := c₁_pos ha0 ha1
  nlinarith

end WrightLaplace
