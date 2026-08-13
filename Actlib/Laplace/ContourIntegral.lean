import Mathlib
import Actlib.Laplace.Integrand
import Actlib.Laplace.QuadraticInequalities
import Actlib.Laplace.StretchedExponential

/-!
# The contour integral `D(ψ)` of equation `eq:D`

This file introduces the quantity

> `D(ψ) := ∫_0^∞ e^{iψ} E(ψ, v) / (t - v e^{iψ}) dv`   (equation `eq:D` of `wright_laplace.tex`)

of the section "The Laplace transform" of `wright_laplace.tex` ("A contour-free proof of the
unit-scale positive-stable Laplace-transform identity"), together with the facts recorded in the
source right after `eq:D` which make it well defined:

* the denominator is nonvanishing (lemma `lem:quad`, as `sin ψ > 0`);
* the integrand is dominated by `e^{-v^a cos(aψ)}/(t sin ψ) ≤ e^{-c₂ v^a}/(t sin ψ)`, using
  equation `eq:quad1` and `cos(aψ) ≥ cos(aθ) = c₂` for `0 ≤ ψ ≤ θ`;
* hence the integrand is integrable on `(0,∞)` by the stretched-exponential integral
  `lem:stretched`.

The definitions are `WrightLaplace.Dintegrand` and `WrightLaplace.D`; they are used to state the
lemmas `lem:fubini` (in `RequestProject/Fubini.lean`) and `lem:rotation` (in
`RequestProject/Rotation.lean`).
-/

namespace WrightLaplace

open MeasureTheory Set Complex

/-- The integrand `v ↦ e^{iψ} E(ψ, v) / (t - v e^{iψ})` of equation `eq:D` of
`wright_laplace.tex`. -/
noncomputable def Dintegrand (a t psi v : ℝ) : ℂ :=
  Complex.exp ((psi : ℂ) * Complex.I) * E a psi v /
    ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))

/-- The quantity `D(ψ) := ∫_0^∞ e^{iψ} E(ψ, v)/(t - v e^{iψ}) dv` of equation `eq:D` of
`wright_laplace.tex`. -/
noncomputable def D (a t psi : ℝ) : ℂ := ∫ v in Ioi (0 : ℝ), Dintegrand a t psi v

/-- The lower bound `|t - v e^{iψ}| ≥ t sin ψ`, the square root of the inequality of equation
`eq:quad1` of the lemma `lem:quad` ("Two quadratic inequalities") of `wright_laplace.tex`. -/
theorem mul_sin_le_norm_sub_mul_exp (t ψ v : ℝ) :
    t * Real.sin ψ ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ := by
  have h := sq_sin_mul_le_normSq_sub_mul_exp t v ψ
  have hn := norm_nonneg ((t : ℂ) - (v : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I))
  nlinarith

/-- The inequality `cos(aψ) ≥ cos(aθ) = c₂` for `0 ≤ ψ ≤ θ`, recorded right after equation
`eq:D` of `wright_laplace.tex` (valid since `0 ≤ aψ ≤ aθ < π/2` and `cos` is decreasing). -/
theorem c₂_le_cos {a psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (h0 : 0 ≤ psi)
    (hle : psi ≤ theta a) : c₂ a ≤ Real.cos (a * psi) := by
  have hpi := Real.pi_pos
  have hθ := mul_theta_lt_pi_div_two ha0 ha1
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) ?_
  exact mul_le_mul_of_nonneg_left hle ha0.le

/-- The modulus of the integrand of equation `eq:D` of `wright_laplace.tex`:
`|e^{iψ}E(ψ,v)/(t - v e^{iψ})| = e^{-v^a cos(aψ)}/|t - v e^{iψ}|`. -/
theorem norm_Dintegrand (a t psi v : ℝ) :
    ‖Dintegrand a t psi v‖ = Real.exp (-(v ^ a * Real.cos (a * psi))) /
      ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ := by
  rw [Dintegrand, norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_E]

/-- The domination recorded right after equation `eq:D` of `wright_laplace.tex`, in the general
form used for the lemma `lem:rotation` ("Rotation invariance"): if `s ≤ sin ψ` and
`κ ≤ cos(aψ)`, the integrand of `D(ψ)` is bounded by `e^{-κ v^a}/(t s)`. -/
theorem norm_Dintegrand_le' {a t psi v k s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hsin : s ≤ Real.sin psi) (hcos : k ≤ Real.cos (a * psi)) (hv : 0 ≤ v) :
    ‖Dintegrand a t psi v‖ ≤ Real.exp (-(k * v ^ a)) / (t * s) := by
  have hts : 0 < t * s := by positivity
  have hden : t * s ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ :=
    le_trans (by nlinarith) (mul_sin_le_norm_sub_mul_exp t psi v)
  have hva : (0 : ℝ) ≤ v ^ a := Real.rpow_nonneg hv a
  have hnum : Real.exp (-(v ^ a * Real.cos (a * psi))) ≤ Real.exp (-(k * v ^ a)) := by
    rw [Real.exp_le_exp]
    nlinarith
  rw [norm_Dintegrand]
  gcongr

/-- The domination recorded right after equation `eq:D` of `wright_laplace.tex`: for
`0 < ψ ≤ θ` the integrand of `D(ψ)` is bounded by `e^{-c₂ v^a}/(t sin ψ)`. -/
theorem norm_Dintegrand_le {a t psi v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (h0 : 0 < psi) (hle : psi ≤ theta a) (hv : 0 ≤ v) :
    ‖Dintegrand a t psi v‖ ≤ Real.exp (-(c₂ a * v ^ a)) / (t * Real.sin psi) := by
  have hsin : 0 < Real.sin psi :=
    Real.sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_lt hle (theta_lt_pi ha0 ha1))
  have hden : t * Real.sin psi ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ :=
    mul_sin_le_norm_sub_mul_exp t psi v
  have hnum : Real.exp (-(v ^ a * Real.cos (a * psi))) ≤ Real.exp (-(c₂ a * v ^ a)) := by
    rw [Real.exp_le_exp]
    have := c₂_le_cos ha0 ha1 h0.le hle
    nlinarith [Real.rpow_nonneg hv a]
  rw [norm_Dintegrand]
  have hpos : 0 < t * Real.sin psi := by positivity
  gcongr

/-- Continuity on `(0,∞)` of the function `E(ψ, ·)` of equation `eq:E` of
`wright_laplace.tex`. -/
theorem continuousOn_E (a psi : ℝ) : ContinuousOn (fun v : ℝ => E a psi v) (Ioi 0) := by
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.mul ?_ continuousOn_const
  exact ContinuousOn.neg (Complex.continuous_ofReal.comp_continuousOn
    (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx)))

/-- Continuity on `(0,∞)` of the integrand of equation `eq:D` of `wright_laplace.tex`. -/
theorem continuousOn_Dintegrand {a t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) :
    ContinuousOn (Dintegrand a t psi) (Ioi 0) := by
  refine ContinuousOn.div (ContinuousOn.mul continuousOn_const (continuousOn_E a psi)) ?_ ?_
  · fun_prop
  · exact fun v _ => sub_mul_exp_ne_zero ht hsin v

/-- Well-definedness of `D(ψ)` (equation `eq:D` of `wright_laplace.tex`): for `0 < ψ ≤ θ` the
integrand is Lebesgue integrable on `(0,∞)`, by the domination recorded in the source and the
stretched-exponential integral `lem:stretched`. -/
theorem integrableOn_Dintegrand {a t psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (h0 : 0 < psi) (hle : psi ≤ theta a) :
    IntegrableOn (Dintegrand a t psi) (Ioi 0) := by
  have hsin : 0 < Real.sin psi :=
    Real.sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_lt hle (theta_lt_pi ha0 ha1))
  have hdom : IntegrableOn
      (fun v : ℝ => Real.exp (-(c₂ a * v ^ a)) / (t * Real.sin psi)) (Ioi 0) :=
    (integrableOn_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)).div_const _
  refine hdom.mono' ((continuousOn_Dintegrand ht hsin).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : (0 : ℝ) < v := hv
  exact norm_Dintegrand_le ha0 ha1 ht h0 hle hv'.le

/-- Well-definedness of `D(ψ)` in the generality needed for the lemma `lem:rotation`
("Rotation invariance") of `wright_laplace.tex`: the integrand of equation `eq:D` is Lebesgue
integrable on `(0,∞)` as soon as `sin ψ > 0` and `cos(aψ) > 0`. -/
theorem integrableOn_Dintegrand' {a t psi : ℝ} (ha0 : 0 < a) (ht : 0 < t)
    (hsin : 0 < Real.sin psi) (hcos : 0 < Real.cos (a * psi)) :
    IntegrableOn (Dintegrand a t psi) (Ioi 0) := by
  have hdom : IntegrableOn
      (fun v : ℝ => Real.exp (-(Real.cos (a * psi) * v ^ a)) / (t * Real.sin psi)) (Ioi 0) :=
    (integrableOn_exp_neg_mul_rpow ha0 hcos).div_const _
  refine hdom.mono' ((continuousOn_Dintegrand ht hsin).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : (0 : ℝ) < v := hv
  exact norm_Dintegrand_le' ht hsin le_rfl le_rfl hv'.le

end WrightLaplace
