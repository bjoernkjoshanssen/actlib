import Mathlib
import Actlib.Laplace.Integrand
import Actlib.Laplace.RayRepresentation
import Actlib.Laplace.StretchedExponential

/-!
# Bounds, continuity, integrability

This file formalizes the corollary labelled `cor:bounds` and titled
**Bounds, continuity, integrability** in `wright_laplace.tex` ("A contour-free proof of the
unit-scale positive-stable Laplace-transform identity"):

> Let `M := Γ(1 + 1/a) / (π c₂^{1/a})`.  Then
> (i) `|g(y)| ≤ M` for every `y > 0`;
> (ii) `g` is continuous on `(0, ∞)`, hence Borel measurable;
> (iii) for every `t > 0` the function `y ↦ g(y) e^{-ty}` is Lebesgue integrable on `(0, ∞)`,
> with `∫_0^∞ |g(y)| e^{-ty} dy ≤ M/t`.

The constant is `WrightLaplace.M`, and the three parts are `WrightLaplace.abs_g_le`,
`WrightLaplace.continuousOn_g` (with `WrightLaplace.aestronglyMeasurable_g` for the "hence Borel
measurable"), and `WrightLaplace.integrableOn_g_mul_exp_neg` together with
`WrightLaplace.integral_abs_g_mul_exp_neg_le`.  The proofs are those of the source: everything
comes from the ray representation `lem:ray`, the uniform bound
`|exp(y v e^{iθ}) E(θ,v)| ≤ e^{-c₂ v^a}` and the stretched-exponential integral
`lem:stretched`.
-/

namespace WrightLaplace

open MeasureTheory Set Complex

/-- The constant `M := Γ(1 + 1/a) / (π c₂^{1/a})` of the corollary `cor:bounds`
("Bounds, continuity, integrability") of `wright_laplace.tex`. -/
noncomputable def M (a : ℝ) : ℝ := Real.Gamma (1 + 1 / a) / (Real.pi * c₂ a ^ (1 / a))

/-- Positivity of the constant `M` of the corollary `cor:bounds` of `wright_laplace.tex`. -/
theorem M_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < M a := by
  have h1 : 0 < Real.Gamma (1 + 1 / a) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < c₂ a ^ (1 / a) := Real.rpow_pos_of_pos (c₂_pos ha0 ha1) _
  have h3 := Real.pi_pos
  rw [M]
  positivity

/-- Part (i) of the corollary `cor:bounds` ("Bounds, continuity, integrability") of
`wright_laplace.tex`: `|g(y)| ≤ M` for every `y > 0`. -/
theorem abs_g_le {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) : |g a y| ≤ M a := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : |(rayIntegral a y).im| ≤ ‖rayIntegral a y‖ := Complex.abs_im_le_norm _
  have h2 : ‖rayIntegral a y‖ = ‖∫ v in Ioi (0 : ℝ), rayIntegrand a y v‖ := by
    rw [rayIntegral, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h3 : ‖∫ v in Ioi (0 : ℝ), rayIntegrand a y v‖
      ≤ ∫ v in Ioi (0 : ℝ), ‖rayIntegrand a y v‖ := norm_integral_le_integral_norm _
  have h4 : (∫ v in Ioi (0 : ℝ), ‖rayIntegrand a y v‖)
      ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-(c₂ a * v ^ a)) := by
    refine setIntegral_mono_on ((integrableOn_rayIntegrand ha0 ha1 hy).norm)
      (integrableOn_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)) measurableSet_Ioi fun v hv => ?_
    exact norm_rayIntegrand_le ha0 ha1 hy.le (le_of_lt hv)
  rw [integral_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)] at h4
  have hkey : |(rayIntegral a y).im| ≤ Real.Gamma (1 + 1 / a) / c₂ a ^ (1 / a) :=
    h1.trans (le_of_eq h2) |>.trans (h3.trans h4)
  have hM : M a = (1 / Real.pi) * (Real.Gamma (1 + 1 / a) / c₂ a ^ (1 / a)) := by
    rw [M]; field_simp
  rw [g_eq_im_rayIntegral ha0 ha1 hy, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi),
    hM]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Continuity in `y`, for fixed `v`, of the integrand of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex`; used for part (ii) of the corollary
`cor:bounds`. -/
theorem continuous_rayIntegrand_fst (a v : ℝ) : Continuous fun y : ℝ => rayIntegrand a y v := by
  refine Continuous.mul ?_ continuous_const
  exact Complex.continuous_exp.comp (by fun_prop)

/-- Continuity of `y ↦ ∫_0^∞ exp(y v e^{iθ}) E(θ, v) dv` on `(0, ∞)`, the dominated-convergence
step in part (ii) of the corollary `cor:bounds` ("Bounds, continuity, integrability") of
`wright_laplace.tex`; the dominating function is `e^{-c₂ v^a} ∈ L¹(0,∞)`. -/
theorem continuousAt_integral_rayIntegrand {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    ContinuousAt (fun y : ℝ => ∫ v in Ioi (0 : ℝ), rayIntegrand a y v) y := by
  have hmem : Ioi (0 : ℝ) ∈ nhds y := Ioi_mem_nhds hy
  refine continuousAt_of_dominated (bound := fun v : ℝ => Real.exp (-(c₂ a * v ^ a)))
    (Filter.Eventually.of_forall fun z =>
      (continuousOn_rayIntegrand a z).aestronglyMeasurable measurableSet_Ioi) ?_
    (integrableOn_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)) ?_
  · filter_upwards [hmem] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact norm_rayIntegrand_le ha0 ha1 (le_of_lt hz) (le_of_lt hv)
  · filter_upwards with v
    exact (continuous_rayIntegrand_fst a v).continuousAt

/-- Part (ii) of the corollary `cor:bounds` ("Bounds, continuity, integrability") of
`wright_laplace.tex`: `g` is continuous on `(0, ∞)`. -/
theorem continuousOn_g {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ContinuousOn (g a) (Ioi 0) := by
  intro y hy
  have hy' : (0 : ℝ) < y := hy
  refine ContinuousAt.continuousWithinAt ?_
  have heq : (fun z : ℝ => (1 / Real.pi) * (rayIntegral a z).im) =ᶠ[nhds y] g a := by
    filter_upwards [Ioi_mem_nhds hy'] with z hz
    exact (g_eq_im_rayIntegral ha0 ha1 hz).symm
  refine ContinuousAt.congr ?_ heq
  refine continuousAt_const.mul ?_
  refine Complex.continuous_im.continuousAt.comp ?_
  exact continuousAt_const.mul (continuousAt_integral_rayIntegrand ha0 ha1 hy')

/-- The "hence Borel measurable" of part (ii) of the corollary `cor:bounds` of
`wright_laplace.tex`, in the form needed below: `g` is a.e. strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_g {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    AEStronglyMeasurable (g a) (volume.restrict (Ioi 0)) :=
  (continuousOn_g ha0 ha1).aestronglyMeasurable measurableSet_Ioi

/-- Part (iii) of the corollary `cor:bounds` ("Bounds, continuity, integrability") of
`wright_laplace.tex`: for every `t > 0` the function `y ↦ g(y) e^{-ty}` is Lebesgue integrable
on `(0, ∞)`. -/
theorem integrableOn_g_mul_exp_neg {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => g a y * Real.exp (-t * y)) (Ioi 0) := by
  have hdom : IntegrableOn (fun y : ℝ => M a * Real.exp (-t * y)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ht).const_mul _
  refine Integrable.mono' hdom
    ((aestronglyMeasurable_g ha0 ha1).mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy' : (0 : ℝ) < y := hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (abs_g_le ha0 ha1 hy') (Real.exp_pos _).le

/-- The bound `∫_0^∞ |g(y)| e^{-ty} dy ≤ M/t` of part (iii) of the corollary `cor:bounds`
("Bounds, continuity, integrability") of `wright_laplace.tex`. -/
theorem integral_abs_g_mul_exp_neg_le {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    (∫ y in Ioi (0 : ℝ), |g a y| * Real.exp (-t * y)) ≤ M a / t := by
  have hdom : IntegrableOn (fun y : ℝ => M a * Real.exp (-t * y)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ht).const_mul _
  have habs : IntegrableOn (fun y : ℝ => |g a y| * Real.exp (-t * y)) (Ioi 0) := by
    have h := (integrableOn_g_mul_exp_neg ha0 ha1 ht).norm
    refine MeasureTheory.IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hmono : (∫ y in Ioi (0 : ℝ), |g a y| * Real.exp (-t * y))
      ≤ ∫ y in Ioi (0 : ℝ), M a * Real.exp (-t * y) := by
    refine setIntegral_mono_on habs hdom measurableSet_Ioi fun y hy => ?_
    exact mul_le_mul_of_nonneg_right (abs_g_le ha0 ha1 hy) (Real.exp_pos _).le
  have hexp : (∫ y in Ioi (0 : ℝ), Real.exp (-t * y)) = 1 / t := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := t) one_pos ht
    simp only [sub_self, Real.rpow_zero, one_mul, Real.Gamma_one, mul_one, Real.rpow_one] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    ring_nf
  rw [integral_const_mul, hexp] at hmono
  rw [← mul_one_div]
  exact hmono

end WrightLaplace
