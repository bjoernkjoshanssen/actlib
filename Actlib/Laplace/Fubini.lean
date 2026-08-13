import Mathlib
import Actlib.Laplace.ContourIntegral
import Actlib.Laplace.Bounds
import Actlib.Laplace.RayRepresentation
import Actlib.Laplace.ComplexScaleGamma

/-!
# Fubini

This file formalizes the lemma labelled `lem:fubini` and titled **Fubini** in
`wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable Laplace-transform
identity"):

> For every `t > 0`,
> `∫_0^∞ g(y) e^{-ty} dy = (1/π) Im D(θ)`.

The statement is `WrightLaplace.integral_g_mul_exp_neg_eq_im_D`.  The proof is the one of the
source: by the ray representation `lem:ray`, `g(y) e^{-ty} = (1/π) Im [e^{-ty} I(y)]` and
`e^{-ty} I(y) = e^{iθ}∫_0^∞ e^{-(t - v e^{iθ})y} E(θ,v) dv`.  The function
`(y,v) ↦ e^{iθ} e^{-(t - v e^{iθ})y} E(θ,v)` (here `WrightLaplace.fubiniIntegrand`) is continuous
and its modulus is `e^{-(t + c₁ v)y} e^{-c₂ v^a}`, whose double integral is at most
`(1/t)∫_0^∞ e^{-c₂ v^a} dv < ∞` by the stretched-exponential integral `lem:stretched`; so Fubini
applies.  The inner `y`-integral is `1/(t - v e^{iθ})` — the case `c = 1` of the complex-scale
Gamma integral `lem:cgamma`, since `Re(t - v e^{iθ}) = t + c₁ v > 0` by `lem:quad` — and `Im`
commutes with the integral because it is a continuous linear map.
-/

namespace WrightLaplace

open MeasureTheory Set Complex Function

/-- The case `c = 1` of the lemma `lem:cgamma` ("Complex-scale Gamma integral") of
`wright_laplace.tex`, used in the proof of the lemma `lem:fubini` ("Fubini"):
`∫_0^∞ e^{-μ y} dy = 1/μ` whenever `Re μ > 0`. -/
theorem integral_cexp_neg_mul_Ioi {m : ℂ} (hm : 0 < m.re) :
    ∫ y in Ioi (0 : ℝ), Complex.exp (-(m * y)) = m⁻¹ := by
  have h := integral_cpow_mul_cexp_neg_mul (c := 1) one_pos hm
  rw [show ((1 : ℝ) : ℂ) - 1 = 0 by norm_num] at h
  simp only [Complex.cpow_zero, one_mul, Real.Gamma_one] at h
  rw [h, show (-((1 : ℝ) : ℂ)) = -1 by norm_num, Complex.cpow_neg_one]
  norm_num

/-- The two-variable integrand `(y, v) ↦ e^{iθ} e^{-(t - v e^{iθ})y} E(θ, v)` to which Fubini's
theorem is applied in the proof of the lemma `lem:fubini` ("Fubini") of `wright_laplace.tex`. -/
noncomputable def fubiniIntegrand (a t y v : ℝ) : ℂ :=
  Complex.exp ((theta a : ℂ) * Complex.I) *
    (Complex.exp (-(((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)) * (y : ℂ))) *
      E a (theta a) v)

/-- The identity `e^{-ty} I(y) = e^{iθ}∫_0^∞ e^{-(t - v e^{iθ})y}E(θ,v)dv` of the proof of the
lemma `lem:fubini` ("Fubini") of `wright_laplace.tex`, in its pointwise form
`e^{iθ}e^{-(t - v e^{iθ})y}E(θ,v) = e^{-ty} · e^{iθ} · exp(y v e^{iθ})E(θ,v)`. -/
theorem fubiniIntegrand_eq (a t y v : ℝ) :
    fubiniIntegrand a t y v =
      ((Real.exp (-t * y) : ℝ) : ℂ) *
        (Complex.exp ((theta a : ℂ) * Complex.I) * rayIntegrand a y v) := by
  have key : Complex.exp
      (-(((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)) * (y : ℂ)))
      = ((Real.exp (-t * y) : ℝ) : ℂ) *
        Complex.exp ((y * v : ℝ) * Complex.exp ((theta a : ℂ) * Complex.I)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [fubiniIntegrand, rayIntegrand, key]
  ring

/-- The modulus `|e^{iθ}e^{-(t - v e^{iθ})y}E(θ,v)| = e^{-(t + c₁ v)y}e^{-c₂ v^a}` computed in
the proof of the lemma `lem:fubini` ("Fubini") of `wright_laplace.tex`. -/
theorem norm_fubiniIntegrand (a t v y : ℝ) :
    ‖fubiniIntegrand a t y v‖ =
      Real.exp (-t * y) * (Real.exp (-(c₁ a * (y * v))) * Real.exp (-(c₂ a * v ^ a))) := by
  rw [fubiniIntegrand_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, one_mul, norm_rayIntegrand]

/-- The bound `|e^{iθ}e^{-(t - v e^{iθ})y}E(θ,v)| ≤ e^{-ty}e^{-c₂ v^a}` used in the proof of the
lemma `lem:fubini` ("Fubini") of `wright_laplace.tex`. -/
theorem norm_fubiniIntegrand_le {a t y v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 ≤ y)
    (hv : 0 ≤ v) :
    ‖fubiniIntegrand a t y v‖ ≤ Real.exp (-t * y) * Real.exp (-(c₂ a * v ^ a)) := by
  rw [norm_fubiniIntegrand a t v y]
  have h1 : Real.exp (-(c₁ a * (y * v))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hc := (c₁_pos ha0 ha1).le
    nlinarith [mul_nonneg hc (mul_nonneg hy hv)]
  have h2 : (0 : ℝ) < Real.exp (-(c₂ a * v ^ a)) := Real.exp_pos _
  have h3 : (0 : ℝ) < Real.exp (-t * y) := Real.exp_pos _
  nlinarith [mul_nonneg (mul_pos h3 h2).le (sub_nonneg.2 h1)]

/-- Integrability in `v` of the Fubini integrand of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex`, for fixed `y > 0`. -/
theorem integrableOn_fubiniIntegrand_right {a t y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => fubiniIntegrand a t y v) (Ioi 0) := by
  have h := ((integrableOn_rayIntegrand ha0 ha1 hy).const_mul
    (Complex.exp ((theta a : ℂ) * Complex.I))).const_mul ((Real.exp (-t * y) : ℝ) : ℂ)
  exact MeasureTheory.IntegrableOn.congr_fun h (fun v _ => (fubiniIntegrand_eq a t y v).symm)
    measurableSet_Ioi

/-- The `v`-integral of the Fubini integrand of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex` is `e^{-ty} I(y)`. -/
theorem integral_fubiniIntegrand_right (a t y : ℝ) :
    (∫ v in Ioi (0 : ℝ), fubiniIntegrand a t y v)
      = ((Real.exp (-t * y) : ℝ) : ℂ) * rayIntegral a y := by
  rw [rayIntegral, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [fubiniIntegrand_eq]

/-- Continuity of the Fubini integrand of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex` on `(0,∞) × (0,∞)`, giving joint measurability. -/
theorem continuousOn_uncurry_fubiniIntegrand (a t : ℝ) :
    ContinuousOn (uncurry (fubiniIntegrand a t)) (Ioi 0 ×ˢ Ioi 0) := by
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
  · refine Complex.continuous_exp.comp_continuousOn ?_
    fun_prop
  · refine Complex.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.mul (ContinuousOn.neg ?_) continuousOn_const
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl (ne_of_gt hx.2)
    exact continuous_snd.continuousOn

/-- Joint measurability of the Fubini integrand of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex`. -/
theorem aestronglyMeasurable_uncurry_fubiniIntegrand (a t : ℝ) :
    AEStronglyMeasurable (uncurry (fubiniIntegrand a t))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [Measure.prod_restrict]
  exact (continuousOn_uncurry_fubiniIntegrand a t).aestronglyMeasurable
    (measurableSet_Ioi.prod measurableSet_Ioi)

/-- The application of Tonelli's theorem in the proof of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex`: the Fubini integrand is integrable on `(0,∞) × (0,∞)`, because
`∫∫ e^{-(t+c₁v)y}e^{-c₂v^a} dy dv ≤ (1/t)∫_0^∞ e^{-c₂ v^a}dv < ∞`. -/
theorem integrable_uncurry_fubiniIntegrand {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    Integrable (uncurry (fubiniIntegrand a t))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set K : ℝ := ∫ v in Ioi (0 : ℝ), Real.exp (-(c₂ a * v ^ a)) with hK
  have hKint : IntegrableOn (fun v : ℝ => Real.exp (-(c₂ a * v ^ a))) (Ioi 0) :=
    integrableOn_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)
  refine (integrable_prod_iff (aestronglyMeasurable_uncurry_fubiniIntegrand a t)).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact integrableOn_fubiniIntegrand_right ha0 ha1 hy
  · have hdom : IntegrableOn (fun y : ℝ => K * Real.exp (-t * y)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 ht).const_mul _
    refine hdom.mono' ((aestronglyMeasurable_uncurry_fubiniIntegrand a t).norm.integral_prod_right')
      ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy' : (0 : ℝ) < y := hy
    have hnn : 0 ≤ ∫ v in Ioi (0 : ℝ), ‖fubiniIntegrand a t y v‖ :=
      integral_nonneg fun v => norm_nonneg _
    simp only [uncurry]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hle : (∫ v in Ioi (0 : ℝ), ‖fubiniIntegrand a t y v‖)
        ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-t * y) * Real.exp (-(c₂ a * v ^ a)) := by
      refine setIntegral_mono_on ((integrableOn_fubiniIntegrand_right ha0 ha1 hy').norm)
        (hKint.const_mul _) measurableSet_Ioi fun v hv => ?_
      exact norm_fubiniIntegrand_le ha0 ha1 hy'.le (le_of_lt hv)
    rw [integral_const_mul] at hle
    rw [hK]
    linarith [hle, mul_comm (Real.exp (-t * y)) K]

/-- The inner `y`-integral of the proof of the lemma `lem:fubini` ("Fubini") of
`wright_laplace.tex`: `∫_0^∞ e^{-(t - v e^{iθ})y}dy = 1/(t - v e^{iθ})`, so that the `y`-integral
of the Fubini integrand is the integrand of `D(θ)` (equation `eq:D`). -/
theorem integral_fubiniIntegrand_left {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ y in Ioi (0 : ℝ), fubiniIntegrand a t y v) = Dintegrand a t (theta a) v := by
  have hre : 0 < ((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)).re :=
    re_sub_mul_exp_theta_pos ha0 ha1 ht hv
  have hne : ((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  rw [show (fun y : ℝ => fubiniIntegrand a t y v)
      = fun y : ℝ => (Complex.exp ((theta a : ℂ) * Complex.I) * E a (theta a) v) *
        Complex.exp (-(((t : ℂ) - (v : ℂ) * Complex.exp ((theta a : ℂ) * Complex.I)) * y)) from
    funext fun y => by rw [fubiniIntegrand]; ring]
  rw [integral_const_mul, integral_cexp_neg_mul_Ioi hre, Dintegrand, div_eq_mul_inv]

/-- The lemma `lem:fubini` ("Fubini") of `wright_laplace.tex`: for every `t > 0`,
`∫_0^∞ g(y) e^{-ty} dy = (1/π) Im D(θ)`. -/
theorem integral_g_mul_exp_neg_eq_im_D {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    (∫ y in Ioi (0 : ℝ), g a y * Real.exp (-t * y)) = (1 / Real.pi) * (D a t (theta a)).im := by
  have hint := integrable_uncurry_fubiniIntegrand ha0 ha1 ht
  have hleft : Integrable (fun y : ℝ => ∫ v in Ioi (0 : ℝ), fubiniIntegrand a t y v)
      (volume.restrict (Ioi 0)) := hint.integral_prod_left
  have hpt : ∀ y ∈ Ioi (0 : ℝ), g a y * Real.exp (-t * y)
      = (1 / Real.pi) * (∫ v in Ioi (0 : ℝ), fubiniIntegrand a t y v).im := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    rw [integral_fubiniIntegrand_right, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [g_eq_im_rayIntegral ha0 ha1 hy']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  congr 1
  rw [show (fun y : ℝ => (∫ v in Ioi (0 : ℝ), fubiniIntegrand a t y v).im)
      = fun y : ℝ => Complex.imCLM (∫ v in Ioi (0 : ℝ), fubiniIntegrand a t y v) from rfl,
    ContinuousLinearMap.integral_comp_comm _ hleft]
  rw [MeasureTheory.integral_integral_swap hint]
  have hD : (∫ v in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), fubiniIntegrand a t y v)
      = D a t (theta a) := by
    rw [D]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    exact integral_fubiniIntegrand_left ha0 ha1 ht (le_of_lt hv)
  rw [hD]
  rfl

end WrightLaplace
