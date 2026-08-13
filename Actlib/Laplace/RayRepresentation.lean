import Mathlib
import Actlib.Laplace.Integrand
import Actlib.Laplace.LogConvexityBound
import Actlib.Laplace.Reflection
import Actlib.Laplace.StretchedExponential
import Actlib.Laplace.ComplexScaleGamma

/-!
# Ray representation

This file formalizes the lemma labelled `lem:ray` and titled **Ray representation** in
`wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable Laplace-transform
identity"):

> For every `y > 0`, the function `v ↦ exp(y v e^{iθ}) E(θ, v)` is integrable on `(0, ∞)`, and
> with `I(y) := e^{iθ} ∫_0^∞ exp(y v e^{iθ}) E(θ, v) dv` one has `g(y) = (1/π) Im I(y)`.

The two assertions are `WrightLaplace.integrableOn_rayIntegrand` and
`WrightLaplace.g_eq_im_rayIntegral`.  The proof follows the source: the modulus of the integrand
is `e^{-c₁ y v} e^{-c₂ v^a} ≤ e^{-c₁ y v}`, the exponential series for `E(θ, v)` is integrated
term by term (justified by the log-convexity bound `lem:gammabound`), each term is evaluated by
the complex-scale Gamma integral `lem:cgamma`, giving the closed form `eq:Iclosed`, and the
imaginary part is computed with the reflection formula `lem:reflection`.
-/

namespace WrightLaplace

open MeasureTheory Set Complex

/-- The `k`-th term of the series obtained by expanding `E(θ, v)` inside the integral defining
`I(y)`, in the proof of the lemma `lem:ray` ("Ray representation") of `wright_laplace.tex`:
`v ↦ exp(y v e^{iθ}) · (-v^a e^{iaθ})^k / k!`. -/
noncomputable def rayTermFun (a y : ℝ) (k : ℕ) (v : ℝ) : ℂ :=
  Complex.exp ((y * v : ℝ) * Complex.exp ((theta a : ℝ) * Complex.I)) *
    ((-((v ^ a : ℝ) : ℂ) * Complex.exp ((a * theta a : ℝ) * Complex.I)) ^ k / (k.factorial : ℂ))

/-- Expansion of the entire function `exp` inside the integrand of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex`:
`exp(y v e^{iθ}) E(θ,v) = ∑_k exp(y v e^{iθ}) (-v^a e^{iaθ})^k/k!`. -/
theorem rayIntegrand_eq_tsum (a y v : ℝ) :
    rayIntegrand a y v = ∑' k : ℕ, rayTermFun a y k v := by
  simp only [rayIntegrand, E, rayTermFun]
  rw [tsum_mul_left]
  congr 1
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-- The modulus of the `k`-th term in the proof of the lemma `lem:ray` ("Ray representation")
of `wright_laplace.tex`: `|exp(y v e^{iθ}) (-v^a e^{iaθ})^k/k!| = v^{ak} e^{-c₁ y v}/k!`. -/
theorem norm_rayTermFun (a y : ℝ) (k : ℕ) {v : ℝ} (hv : 0 < v) :
    ‖rayTermFun a y k v‖ = v ^ (a * k) * Real.exp (-(c₁ a * y * v)) / (k.factorial : ℝ) := by
  rw [rayTermFun, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_exp, Complex.norm_exp,
    norm_neg]
  have h1 : ‖((v ^ a : ℝ) : ℂ)‖ = v ^ a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hv.le a)]
  have h2 : ((theta a : ℝ) * Complex.I).re = 0 := by simp
  have h3 : (((y * v : ℝ) : ℂ) * Complex.exp ((theta a : ℝ) * Complex.I)).re
      = -(c₁ a * y * v) := by
    simp only [Complex.mul_re, Complex.exp_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_im, c₁]
    simp
    ring
  have h4 : (((a * theta a : ℝ)) * Complex.I).re = 0 := by simp
  simp only [h1, h3, h4, Real.exp_zero, mul_one, Complex.norm_natCast]
  rw [← Real.rpow_natCast (v ^ a) k, ← Real.rpow_mul hv.le]
  ring

/-- Continuity on `(0, ∞)` of the `k`-th term in the proof of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex`. -/
theorem continuousOn_rayTermFun (a y : ℝ) (k : ℕ) :
    ContinuousOn (rayTermFun a y k) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine ContinuousOn.div_const (ContinuousOn.pow ?_ k) _
    refine ContinuousOn.mul ?_ continuousOn_const
    exact ContinuousOn.neg (Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx)))

/-- Integrability on `(0, ∞)` of the `k`-th term in the proof of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex`. -/
theorem integrableOn_rayTermFun {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) (k : ℕ) :
    IntegrableOn (rayTermFun a y k) (Ioi 0) := by
  have hb : 0 < c₁ a * y := mul_pos (c₁_pos ha0 ha1) hy
  have hs : 0 < a * k + 1 := by positivity
  have hdom : IntegrableOn
      (fun v : ℝ => (v ^ (a * k + 1 - 1) * Real.exp (-(c₁ a * y * v))) / (k.factorial : ℝ))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi hb hs).div_const _
  refine Integrable.mono' hdom
    ((continuousOn_rayTermFun a y k).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_rayTermFun a y k hv]
  simp only [add_sub_cancel_right]
  exact le_rfl

/-- The evaluation of `∫_0^∞ |exp(y v e^{iθ}) (-v^a e^{iaθ})^k/k!| dv` in the proof of the lemma
`lem:ray` ("Ray representation") of `wright_laplace.tex`:
`∫_0^∞ v^{ak} e^{-c₁ y v} dv / k! = Γ(ak+1)/(k! (c₁ y)^{ak+1})`. -/
theorem integral_norm_rayTermFun {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) (k : ℕ) :
    ∫ v in Ioi (0 : ℝ), ‖rayTermFun a y k v‖
      = (1 / (c₁ a * y)) *
          (Real.Gamma (a * k + 1) / (k.factorial : ℝ) * ((1 / (c₁ a * y)) ^ a) ^ k) := by
  have hb : 0 < c₁ a * y := mul_pos (c₁_pos ha0 ha1) hy
  have hs : 0 < a * k + 1 := by positivity
  have hcongr : ∫ v in Ioi (0 : ℝ), ‖rayTermFun a y k v‖
      = ∫ v in Ioi (0 : ℝ), (v ^ (a * k + 1 - 1) * Real.exp (-(c₁ a * y * v))) /
          (k.factorial : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    rw [norm_rayTermFun a y k hv]
    simp only [add_sub_cancel_right]
  rw [hcongr, integral_div, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hb]
  have hpow : (1 / (c₁ a * y)) ^ (a * k + 1)
      = ((1 / (c₁ a * y)) ^ a) ^ k * (1 / (c₁ a * y)) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one, ← Real.rpow_natCast ((1 / (c₁ a * y)) ^ a) k,
      ← Real.rpow_mul (by positivity)]
  rw [hpow]
  ring

/-- Summability of the `L¹` norms of the terms, the hypothesis justifying the interchange of
`∑_k` and `∫_0^∞` in the proof of the lemma `lem:ray` ("Ray representation") of
`wright_laplace.tex`.  This is where the log-convexity bound `lem:gammabound` is used. -/
theorem summable_integral_norm_rayTermFun {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    Summable fun k : ℕ => ∫ v in Ioi (0 : ℝ), ‖rayTermFun a y k v‖ := by
  have hb : 0 < c₁ a * y := mul_pos (c₁_pos ha0 ha1) hy
  have hx : (0 : ℝ) ≤ (1 / (c₁ a * y)) ^ a := Real.rpow_nonneg (by positivity) a
  have := (summable_gamma_div_factorial_mul_pow ha0 ha1 hx).mul_left (1 / (c₁ a * y))
  refine this.congr fun k => ?_
  rw [integral_norm_rayTermFun ha0 ha1 hy k]

/-- The integrability assertion of the lemma `lem:ray` ("Ray representation") of
`wright_laplace.tex`: for `y > 0`, the function `v ↦ exp(y v e^{iθ}) E(θ, v)` is Lebesgue
integrable on `(0, ∞)`, the modulus of the integrand being at most `e^{-c₁ y v}`. -/
theorem integrableOn_rayIntegrand {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    IntegrableOn (rayIntegrand a y) (Ioi 0) := by
  have hb : 0 < c₁ a * y := mul_pos (c₁_pos ha0 ha1) hy
  have hdom : IntegrableOn (fun v : ℝ => Real.exp (-(c₁ a * y) * v)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hb
  refine Integrable.mono' hdom
    ((continuousOn_rayIntegrand a y).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : (0 : ℝ) ≤ v := le_of_lt hv
  have := norm_rayIntegrand_le' ha0 ha1 (y := y) hv'
  calc ‖rayIntegrand a y v‖ ≤ Real.exp (-(c₁ a * (y * v))) := this
    _ = Real.exp (-(c₁ a * y) * v) := by ring_nf

/-- Equation `eq:Iterms` of the proof of the lemma `lem:ray` ("Ray representation") of
`wright_laplace.tex`: the termwise expansion
`I(y) = ∑_k e^{iθ} ∫_0^∞ exp(y v e^{iθ}) (-v^a e^{iaθ})^k/k! dv`. -/
theorem rayIntegral_eq_tsum {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    rayIntegral a y
      = ∑' k : ℕ, Complex.exp ((theta a : ℝ) * Complex.I) *
          ∫ v in Ioi (0 : ℝ), rayTermFun a y k v := by
  rw [rayIntegral, tsum_mul_left]
  congr 1
  rw [show (∫ v in Ioi (0 : ℝ), rayIntegrand a y v)
      = ∫ v in Ioi (0 : ℝ), ∑' k : ℕ, rayTermFun a y k v from
    setIntegral_congr_fun measurableSet_Ioi fun v _ => rayIntegrand_eq_tsum a y v]
  exact (integral_tsum_of_summable_integral_norm (fun k => integrableOn_rayTermFun ha0 ha1 hy k)
    (summable_integral_norm_rayTermFun ha0 ha1 hy)).symm

/-- The principal logarithm computation of the proof of the lemma `lem:ray` ("Ray
representation") of `wright_laplace.tex`: with `μ := -y e^{iθ} = y e^{i(θ-π)}` and
`θ - π ∈ (-π/2, 0)`, one has `Log μ = ln y + i(θ-π)`, hence
`μ^{-c} = y^{-c} e^{-i c (θ-π)}` for real `c`. -/
theorem cpow_neg_mu {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) (c : ℝ) :
    (-((y : ℂ) * Complex.exp ((theta a : ℝ) * Complex.I))) ^ (-(c : ℂ))
      = ((y ^ (-c) : ℝ) : ℂ) * Complex.exp ((-c * (theta a - Real.pi) : ℝ) * Complex.I) := by
  have hlog : -((y : ℂ) * Complex.exp ((theta a : ℝ) * Complex.I))
      = Complex.exp ((Real.log y : ℝ) + ((theta a - Real.pi : ℝ) : ℝ) * Complex.I) := by
    rw [Complex.exp_add, Complex.ofReal_sub, sub_mul, Complex.exp_sub]
    rw [show ((Real.pi : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by norm_num]
    rw [Complex.exp_pi_mul_I]
    have : Complex.exp ((Real.log y : ℝ) : ℂ) = (y : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hy]
    rw [this]
    field_simp
  rw [hlog, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [pi_div_two_lt_theta ha0 ha1, theta_lt_pi ha0 ha1,
      Real.pi_pos]) (by simp; nlinarith [theta_lt_pi ha0 ha1, Real.pi_pos])]
  have hy' : ((y ^ (-c) : ℝ) : ℂ) = Complex.exp (((Real.log y * -c : ℝ) : ℂ)) := by
    rw [Real.rpow_def_of_pos hy, Complex.ofReal_exp]
  rw [hy', ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Evaluation of the `k`-th term of `eq:Iterms` in the proof of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex`, by the complex-scale Gamma integral
`lem:cgamma` with `c = ak+1` and `μ = -y e^{iθ}`; after simplification of the total phase, the
`k`-th term of the closed form `eq:Iclosed` is
`((-1)^k/k!) Γ(ak+1) y^{-ak-1} e^{iπ(ak+1)}`. -/
theorem rayTerm_closed {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) (k : ℕ) :
    Complex.exp ((theta a : ℝ) * Complex.I) * (∫ v in Ioi (0 : ℝ), rayTermFun a y k v)
      = (((-1) ^ k / (k.factorial : ℝ) * Real.Gamma (a * k + 1) * y ^ (-(a * k) - 1) : ℝ) : ℂ) *
          Complex.exp ((Real.pi * (a * k + 1) : ℝ) * Complex.I) := by
  set c : ℝ := a * k + 1 with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  set m : ℂ := -((y : ℂ) * Complex.exp ((theta a : ℝ) * Complex.I)) with hm_def
  have hmre : 0 < m.re := by
    have : m.re = c₁ a * y := by
      simp only [hm_def, Complex.neg_re, Complex.mul_re, Complex.exp_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im, c₁]
      simp
      ring
    rw [this]
    exact mul_pos (c₁_pos ha0 ha1) hy
  have hpt : ∀ v ∈ Ioi (0 : ℝ), rayTermFun a y k v
      = (((-1) ^ k * Complex.exp ((a * theta a : ℝ) * Complex.I) ^ k / (k.factorial : ℂ))) *
          ((v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))) := by
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have h1 : ((v : ℂ)) ^ ((c : ℂ) - 1) = ((v ^ (a * k) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hv0.le]
      congr 1
      rw [hc_def]; push_cast; ring
    have h2 : ((v ^ (a * k) : ℝ) : ℂ) = ((v ^ a : ℝ) : ℂ) ^ k := by
      rw [← Complex.ofReal_pow, ← Real.rpow_natCast (v ^ a) k, ← Real.rpow_mul hv0.le]
    have h3 : Complex.exp (-(m * v)) = Complex.exp (((y * v : ℝ) : ℂ) *
        Complex.exp ((theta a : ℝ) * Complex.I)) := by
      congr 1
      rw [hm_def]; push_cast; ring
    rw [rayTermFun, h1, h2, h3, mul_pow, neg_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_cpow_mul_cexp_neg_mul hc hmre, hm_def, cpow_neg_mu ha0 ha1 hy c]
  have hexp : Complex.exp ((theta a : ℝ) * Complex.I) *
      Complex.exp ((a * theta a : ℝ) * Complex.I) ^ k *
      Complex.exp ((-c * (theta a - Real.pi) : ℝ) * Complex.I)
      = Complex.exp ((Real.pi * (a * k + 1) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hc_def]; push_cast; ring
  have hreal : ((((-1) ^ k / (k.factorial : ℝ) * Real.Gamma (a * k + 1) *
        y ^ (-(a * k) - 1)) : ℝ) : ℂ)
      = ((-1 : ℂ)) ^ k / (k.factorial : ℂ) * (Real.Gamma c : ℂ) * ((y ^ (-c) : ℝ) : ℂ) := by
    have hexpo : -(a * k) - 1 = -c := by rw [hc_def]; ring
    rw [hexpo, hc_def]
    push_cast
    ring
  rw [hreal, ← hexp]
  ring

/-- Equation `eq:Iclosed` of the proof of the lemma `lem:ray` ("Ray representation") of
`wright_laplace.tex`:
`I(y) = ∑_k ((-1)^k/k!) Γ(ak+1) y^{-ak-1} e^{iπ(ak+1)}`. -/
theorem rayIntegral_eq_tsum_closed {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    rayIntegral a y
      = ∑' k : ℕ,
          (((-1) ^ k / (k.factorial : ℝ) * Real.Gamma (a * k + 1) * y ^ (-(a * k) - 1) : ℝ) : ℂ) *
            Complex.exp ((Real.pi * (a * k + 1) : ℝ) * Complex.I) := by
  rw [rayIntegral_eq_tsum ha0 ha1 hy]
  exact tsum_congr fun k => rayTerm_closed ha0 ha1 hy k

/-- Summability of the terms of the closed form `eq:Iclosed` in the proof of the lemma
`lem:ray` ("Ray representation") of `wright_laplace.tex`. -/
theorem summable_rayTerm_closed {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    Summable fun k : ℕ =>
      (((-1) ^ k / (k.factorial : ℝ) * Real.Gamma (a * k + 1) * y ^ (-(a * k) - 1) : ℝ) : ℂ) *
        Complex.exp ((Real.pi * (a * k + 1) : ℝ) * Complex.I) := by
  have hx : (0 : ℝ) ≤ y ^ (-a) := Real.rpow_nonneg hy.le _
  have hs := (summable_gamma_div_factorial_mul_pow ha0 ha1 hx).mul_left (y ^ (-1 : ℝ))
  refine Summable.of_norm (hs.congr fun k => ?_)
  have hG : 0 < Real.Gamma (a * k + 1) := by
    refine Real.Gamma_pos_of_pos ?_
    have : (0 : ℝ) ≤ a * k := by positivity
    linarith
  have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hpow : y ^ (-(a * k) - 1) = y ^ (-1 : ℝ) * (y ^ (-a)) ^ k := by
    rw [← Real.rpow_natCast (y ^ (-a)) k, ← Real.rpow_mul hy.le,
      ← Real.rpow_add hy]
    ring_nf
  have hP : (0 : ℝ) < y ^ (-(a * k) - 1) := Real.rpow_pos_of_pos hy _
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hF,
    abs_of_pos hG, abs_of_pos hP, hpow]
  ring

/-- **Ray representation**, the conclusion of the lemma `lem:ray` of `wright_laplace.tex`:
for every `y > 0`, `g(y) = (1/π) Im I(y)`. -/
theorem g_eq_im_rayIntegral {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    g a y = (1 / Real.pi) * (rayIntegral a y).im := by
  rw [g_eq_tsum hy, rayIntegral_eq_tsum_closed ha0 ha1 hy,
    Complex.im_tsum (summable_rayTerm_closed ha0 ha1 hy), ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have him : ∀ R p : ℝ, (((R : ℝ) : ℂ) * Complex.exp ((p : ℝ) * Complex.I)).im
      = R * Real.sin p := by
    intro R p
    simp [Complex.mul_im, Complex.exp_im, Complex.exp_re]
  rw [him]
  have hsin : Real.sin (Real.pi * (a * k + 1)) = -Real.sin (Real.pi * (a * k)) := by
    rw [show Real.pi * (a * k + 1) = Real.pi * (a * k) + Real.pi by ring, Real.sin_add_pi]
  have hrefl := one_div_Gamma_neg_of_nonneg (a * k) (by positivity)
  have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hsplit : (-1 : ℝ) ^ k * y ^ (-(a * k) - 1) /
      ((k.factorial : ℝ) * Real.Gamma (-(a * k)))
      = ((-1 : ℝ) ^ k * y ^ (-(a * k) - 1) / (k.factorial : ℝ)) *
        (1 / Real.Gamma (-(a * k))) := by
    rw [div_mul_eq_div_div, div_eq_mul_one_div]
  rw [hsplit, hrefl, hsin]
  field_simp

end WrightLaplace
