import Mathlib
import Actlib.Laplace.StretchedExponential

/-!
# The Gamma integral with complex scale

This file formalizes the lemma labelled `lem:cgamma` and titled **Complex-scale Gamma integral**
in `wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable
Laplace-transform identity"):

> Let `c ∈ (0, ∞)` be real and let `μ ∈ ℂ` with `Re μ > 0`.  Then `v ↦ v^{c-1} e^{-μ v}` is
> Lebesgue integrable on `(0, ∞)` and
> `∫_0^∞ v^{c-1} e^{-μ v} dv = Γ(c) μ^{-c}`,
> with the principal power `μ^{-c} = exp(-c Log μ)`.

The two assertions are `WrightLaplace.integrableOn_cpow_mul_cexp_neg_mul` and
`WrightLaplace.integral_cpow_mul_cexp_neg_mul`.  Powers of complex numbers are `Complex.cpow`,
which is the principal power of Convention `conv:powers` of the source.

The proof follows the source: integrability comes from the modulus computation
`|v^{c-1} e^{-μ v}| = v^{c-1} e^{-(Re μ) v}`; the integral is holomorphic in `μ` on the right
half-plane by differentiation under the integral sign with the dominating function
`v^{c} e^{-δ v}` (`WrightLaplace.hasDerivAt_integral_cpow_mul_cexp_neg_mul`); the right-hand side
is holomorphic there because the principal power is; both sides agree on the positive reals; and
the identity theorem for analytic functions on the (convex, hence preconnected) right half-plane
finishes the proof.
-/

namespace WrightLaplace

open MeasureTheory Set Filter Complex

/-- Continuity on `(0, ∞)` of the integrand `v ↦ v^{c-1} e^{-μ v}` of the lemma `lem:cgamma`
("Complex-scale Gamma integral") of `wright_laplace.tex`. -/
theorem continuousOn_cpow_mul_cexp_neg_mul (c : ℝ) (m : ℂ) :
    ContinuousOn (fun v : ℝ => (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))) (Ioi 0) := by
  apply ContinuousOn.mul
  · intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x _
      (Or.inr (by exact_mod_cast ne_of_gt hx))).continuousWithinAt
  · fun_prop

/-- The modulus computation `|v^{c-1} e^{-μ v}| = v^{c-1} e^{-(Re μ) v}` used in the proof of the
lemma `lem:cgamma` ("Complex-scale Gamma integral") of `wright_laplace.tex`. -/
theorem norm_cpow_mul_cexp_neg_mul (c : ℝ) (m : ℂ) {v : ℝ} (hv : 0 < v) :
    ‖(v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))‖
      = v ^ (c - 1) * Real.exp (-(m.re * v)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp]
  simp

/-- The integrability assertion of the lemma `lem:cgamma` ("Complex-scale Gamma integral") of
`wright_laplace.tex`: for real `c > 0` and `μ ∈ ℂ` with `Re μ > 0`, the function
`v ↦ v^{c-1} e^{-μ v}` is Lebesgue integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul {c : ℝ} (hc : 0 < c) {m : ℂ} (hm : 0 < m.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_Ioi hm hc).mono'
    ((continuousOn_cpow_mul_cexp_neg_mul c m).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  simp only [mem_Ioi] at hv
  exact le_of_eq (norm_cpow_mul_cexp_neg_mul c m hv)

/-- Differentiation under the integral sign in the proof of the lemma `lem:cgamma`
("Complex-scale Gamma integral") of `wright_laplace.tex`: the function
`L(μ) = ∫_0^∞ v^{c-1} e^{-μ v} dv` is complex differentiable at every `μ₀` with `Re μ₀ > 0`,
with derivative `-∫_0^∞ v · v^{c-1} e^{-μ₀ v} dv`.  As in the source, the dominating function on
the ball `B(μ₀, δ)`, `δ = ½ Re μ₀`, is `v ↦ v^{c} e^{-δ v}`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul {c : ℝ} (hc : 0 < c) {m₀ : ℂ}
    (hm₀ : 0 < m₀.re) :
    HasDerivAt (fun m : ℂ => ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v)))
      (∫ v in Ioi (0 : ℝ), -(v : ℂ) * ((v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m₀ * v)))) m₀ := by
  set d : ℝ := m₀.re / 2 with hd
  have hdpos : 0 < d := by simp only [hd]; linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (m : ℂ) (v : ℝ) => (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v)))
    (F' := fun (m : ℂ) (v : ℝ) => -(v : ℂ) * ((v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))))
    (bound := fun v : ℝ => v ^ c * Real.exp (-(d * v)))
    (Metric.ball_mem_nhds m₀ hdpos) ?_ (integrableOn_cpow_mul_cexp_neg_mul hc hm₀) ?_ ?_ ?_ ?_).2
  · filter_upwards with m using
      (continuousOn_cpow_mul_cexp_neg_mul c m).aestronglyMeasurable measurableSet_Ioi
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact Complex.continuous_ofReal.continuousOn.neg.mul (continuousOn_cpow_mul_cexp_neg_mul c m₀)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv m hm
    simp only [mem_Ioi] at hv
    have hmre : d ≤ m.re := by
      have h1 : ‖m - m₀‖ < d := by simpa [Complex.dist_eq] using Metric.mem_ball.1 hm
      have h2 : |m.re - m₀.re| ≤ ‖m - m₀‖ := by
        simpa using Complex.abs_re_le_norm (m - m₀)
      have h3 := abs_le.1 h2
      simp only [hd] at *
      linarith [h3.1]
    rw [norm_mul, norm_cpow_mul_cexp_neg_mul c m hv, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hv, ← mul_assoc]
    have hvc : v * v ^ (c - 1) = v ^ c := by
      have h : v ^ c = v ^ (1 : ℝ) * v ^ (c - 1) := by rw [← Real.rpow_add hv]; ring_nf
      rw [h, Real.rpow_one]
    rw [hvc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
  · have h : IntegrableOn (fun v : ℝ => v ^ (c + 1 - 1) * Real.exp (-(d * v))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_Ioi hdpos (by linarith : (0 : ℝ) < c + 1)
    simpa [IntegrableOn] using h
  · filter_upwards with v m _
    have h1 : HasDerivAt (fun z : ℂ => -(z * (v : ℂ))) (-(v : ℂ)) m := by
      simpa [mul_neg] using (hasDerivAt_id m).mul_const (-(v : ℂ))
    have h3 : HasDerivAt (fun z : ℂ => (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(z * (v : ℂ))))
        ((v : ℂ) ^ ((c : ℂ) - 1) * (Complex.exp (-(m * (v : ℂ))) * -(v : ℂ))) m :=
      h1.cexp.const_mul ((v : ℂ) ^ ((c : ℂ) - 1))
    have hval : -(v : ℂ) * ((v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * (v : ℂ))))
        = (v : ℂ) ^ ((c : ℂ) - 1) * (Complex.exp (-(m * (v : ℂ))) * -(v : ℂ)) := by ring
    rw [hval]
    exact h3

/-- The lemma `lem:cgamma` ("Complex-scale Gamma integral") of `wright_laplace.tex`: for real
`c > 0` and `μ ∈ ℂ` with `Re μ > 0`,
`∫_0^∞ v^{c-1} e^{-μ v} dv = Γ(c) μ^{-c}`,
the power being the principal one. -/
theorem integral_cpow_mul_cexp_neg_mul {c : ℝ} (hc : 0 < c) {m : ℂ} (hm : 0 < m.re) :
    ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v))
      = (Real.Gamma c : ℂ) * m ^ (-(c : ℂ)) := by
  set L : ℂ → ℂ :=
    fun m => ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ ((c : ℂ) - 1) * Complex.exp (-(m * v)) with hL
  set R : ℂ → ℂ := fun m => (Real.Gamma c : ℂ) * m ^ (-(c : ℂ)) with hR
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt 0
  have hLan : AnalyticOnNhd ℂ L U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => DifferentiableAt.differentiableWithinAt
        (hasDerivAt_integral_cpow_mul_cexp_neg_mul hc hz).differentiableAt) hUopen
  have hRan : AnalyticOnNhd ℂ R U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((differentiableAt_id.cpow_const
      (Complex.mem_slitPlane_iff.2 (Or.inl hz))).const_mul _).differentiableWithinAt
  have hreal : ∀ r : ℝ, 0 < r → L r = R r := by
    intro r hr
    have hint := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := (c : ℂ)) (r := r)
      (by simpa using hc) hr
    have hne : ((r : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact fun h => absurd h.symm (ne_of_gt Real.pi_pos)
    rw [hL, hR]
    simp only
    rw [hint, Complex.Gamma_ofReal, Complex.cpow_neg, one_div, Complex.inv_cpow _ _ hne, mul_comm]
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, L z = R z := by
    have hmap : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhdsWithin 1 (Ioi 1))
        (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num] at h
        exact absurd (Complex.ofReal_inj.1 h) (ne_of_gt hx)
    refine hmap.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hreal x (by linarith [mem_Ioi.1 hx])
  exact hLan.eqOn_of_preconnected_of_frequently_eq hRan hUconv.isPreconnected
    (by simp [hU]) hfreq hm

end WrightLaplace
