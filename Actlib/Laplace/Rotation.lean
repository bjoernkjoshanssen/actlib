import Mathlib
import Actlib.Laplace.ContourIntegral
import Actlib.Laplace.StretchedExponential

/-!
# Rotation invariance

This file formalizes the lemma labelled `lem:rotation` and titled **Rotation invariance** in
`wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable Laplace-transform
identity"):

> `D` is constant on `(0, θ]`.

The statement is `WrightLaplace.D_eq_of_mem_Ioc` (and, in the form used later,
`WrightLaplace.D_eq_D_theta`).

The proof is the one of the source, but carried out with explicit formulas rather than with the
holomorphic function `Φ(w) = e^{-w^a}/(t-w)`: writing `H(ψ,v)` for the integrand of `eq:D`, the
key pointwise identity `eq:key`

> `∂_ψ H(ψ,v) = i ∂_v [v H(ψ,v)]`

is verified by differentiating both sides explicitly; the common value is
`WrightLaplace.rotDeriv` (`i · rotDeriv` for the left-hand side).  Uniformly for `ψ` in a compact
subinterval, `|∂_ψ H| ≤ β(v)` with `β` the dominating function `WrightLaplace.rotBound` of the
source, integrable by `lem:stretched` (more precisely by
`WrightLaplace.integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi`).  Differentiation under the integral
sign then gives `D'(ψ) = i ∫_0^∞ ∂_v[v H] dv`, which vanishes by the fundamental theorem of
calculus on `(0,∞)`, both boundary terms being zero.  Hence `D' ≡ 0` on the open interval
`(0, min(π, π/(2a)))`, which contains `(0, θ]`, and `D` is constant there.
-/

namespace WrightLaplace

open MeasureTheory Set Filter Complex

/-- The function `∂_v[v H(ψ,v)]` of the key identity `eq:key` in the proof of the lemma
`lem:rotation` ("Rotation invariance") of `wright_laplace.tex`, written out explicitly:
`∂_v[v H] = e^{iψ}E(ψ,v)(1 - a v^a e^{iaψ})/(t - v e^{iψ}) + v e^{2iψ}E(ψ,v)/(t - v e^{iψ})²`. -/
noncomputable def rotDeriv (a t psi v : ℝ) : ℂ :=
  Complex.exp ((psi : ℂ) * Complex.I) * E a psi v *
      (1 - ((a * v ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I)) /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))
    + (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ^ 2 * E a psi v /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) ^ 2

/-- Half of the key identity `eq:key` of the lemma `lem:rotation` ("Rotation invariance") of
`wright_laplace.tex`: for `v > 0`, `v ↦ v H(ψ,v)` is differentiable with derivative
`WrightLaplace.rotDeriv`. -/
theorem hasDerivAt_mul_Dintegrand {a t psi v : ℝ} (hv : 0 < v)
    (hDen : (t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun v : ℝ => (v : ℂ) * Dintegrand a t psi v) (rotDeriv a t psi v) v := by
  have hr : HasDerivAt (fun v : ℝ => (v ^ a : ℝ)) (a * v ^ (a - 1)) v :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hv))
  have hE : HasDerivAt (fun v : ℝ => E a psi v)
      (E a psi v * (-(((a * v ^ (a - 1) : ℝ))) * Complex.exp ((a * psi : ℝ) * Complex.I))) v := by
    have := ((hr.ofReal_comp).neg.mul_const (Complex.exp ((a * psi : ℝ) * Complex.I))).cexp
    simpa [E] using this
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := by
    simpa using (hasDerivAt_id v).ofReal_comp
  have hnum := (hid.mul_const (Complex.exp ((psi : ℂ) * Complex.I))).mul hE
  have hden := (hid.mul_const (Complex.exp ((psi : ℂ) * Complex.I))).const_sub (t : ℂ)
  have hdiv := hnum.div hden hDen
  simp only [Pi.mul_apply] at hdiv
  have hfun : (fun v : ℝ => (v : ℂ) * Dintegrand a t psi v)
      = (fun v : ℝ => (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) * E a psi v)
        / (fun v : ℝ => (t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) := by
    funext w
    simp only [Pi.div_apply, Dintegrand]
    ring
  rw [hfun]
  refine hdiv.congr_deriv ?_
  have hAv : (v : ℂ) * ((a * v ^ (a - 1) : ℝ) : ℂ) = ((a * v ^ a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [show v * (a * v ^ (a - 1)) = a * (v ^ (1 : ℝ) * v ^ (a - 1)) by rw [Real.rpow_one]; ring,
      ← Real.rpow_add hv]
    ring_nf
  simp only [rotDeriv]
  rw [← hAv]
  field_simp
  ring

/-- The key identity `eq:key` of the lemma `lem:rotation` ("Rotation invariance") of
`wright_laplace.tex`: `∂_ψ H(ψ,v) = i ∂_v[v H(ψ,v)] = i · rotDeriv`. -/
theorem hasDerivAt_Dintegrand_psi {a t psi v : ℝ}
    (hDen : (t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun psi : ℝ => Dintegrand a t psi v) (Complex.I * rotDeriv a t psi v) psi := by
  have hid : HasDerivAt (fun psi : ℝ => (psi : ℂ)) 1 psi := by
    simpa using (hasDerivAt_id psi).ofReal_comp
  have hexp : HasDerivAt (fun psi : ℝ => Complex.exp ((psi : ℂ) * Complex.I))
      (Complex.exp ((psi : ℂ) * Complex.I) * Complex.I) psi := by
    simpa using (hid.mul_const Complex.I).cexp
  have hid2 : HasDerivAt (fun psi : ℝ => ((a * psi : ℝ) : ℂ)) (a : ℂ) psi := by
    have h : HasDerivAt (fun psi : ℝ => a * psi) a psi := by
      simpa using (hasDerivAt_id psi).const_mul a
    simpa using h.ofReal_comp
  have hexp2 : HasDerivAt (fun psi : ℝ => Complex.exp (((a * psi : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((a * psi : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)) psi := by
    simpa using (hid2.mul_const Complex.I).cexp
  have hE : HasDerivAt (fun psi : ℝ => E a psi v)
      (E a psi v * (-((v ^ a : ℝ) : ℂ) *
        (Complex.exp (((a * psi : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)))) psi := by
    have := (hexp2.const_mul (-((v ^ a : ℝ) : ℂ))).cexp
    simpa [E, mul_assoc] using this
  have hnum := hexp.mul hE
  have hden := (hexp.const_mul (v : ℂ)).const_sub (t : ℂ)
  have hdiv := hnum.div hden hDen
  simp only [Pi.mul_apply] at hdiv
  have hfun : (fun psi : ℝ => Dintegrand a t psi v)
      = (fun psi : ℝ => Complex.exp ((psi : ℂ) * Complex.I) * E a psi v)
        / (fun psi : ℝ => (t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) := by
    funext w
    simp only [Pi.div_apply, Dintegrand]
  rw [hfun]
  refine hdiv.congr_deriv ?_
  simp only [rotDeriv]
  push_cast
  field_simp
  ring

/-- The dominating function `β(v) = e^{-κ v^a}(1 + a v^a)/(t s) + v e^{-κ v^a}/(t s)²` of the
proof of the lemma `lem:rotation` ("Rotation invariance") of `wright_laplace.tex`, where `s` is
a lower bound for `sin ψ` and `κ` a lower bound for `cos(aψ)` on the subinterval considered. -/
noncomputable def rotBound (a t k s v : ℝ) : ℝ :=
  Real.exp (-(k * v ^ a)) * (1 + a * v ^ a) / (t * s)
    + v * Real.exp (-(k * v ^ a)) / (t * s) ^ 2

/-- Integrability of the dominating function `β` of the proof of the lemma `lem:rotation`
("Rotation invariance") of `wright_laplace.tex`. -/
theorem integrableOn_rotBound {a t k s : ℝ} (ha0 : 0 < a) (hk : 0 < k) :
    IntegrableOn (fun v : ℝ => rotBound a t k s v) (Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi (s := 0) ha0 hk (by norm_num)
  have ha := integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi (s := a) ha0 hk (by linarith)
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi (s := 1) ha0 hk (by norm_num)
  have hsum := ((h0.const_mul (1 / (t * s))).add (ha.const_mul (a / (t * s)))).add
    (h1.const_mul (1 / (t * s) ^ 2))
  refine MeasureTheory.IntegrableOn.congr_fun hsum (fun v hv => ?_) measurableSet_Ioi
  have hv' : (0 : ℝ) < v := hv
  simp only [Pi.add_apply, rotBound, Real.rpow_zero, Real.rpow_one, one_mul]
  field_simp

/-- The uniform domination `|∂_ψ H(ψ,v)| ≤ β(v)` of the proof of the lemma `lem:rotation`
("Rotation invariance") of `wright_laplace.tex`. -/
theorem norm_rotDeriv_le {a t psi v k s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hsin : s ≤ Real.sin psi) (hcos : k ≤ Real.cos (a * psi)) (hv : 0 < v) (ha0 : 0 < a) :
    ‖rotDeriv a t psi v‖ ≤ rotBound a t k s v := by
  have hts : 0 < t * s := by positivity
  have hden : t * s ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ :=
    le_trans (by nlinarith) (mul_sin_le_norm_sub_mul_exp t psi v)
  have hden' : 0 < ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ := lt_of_lt_of_le hts hden
  have hva : (0 : ℝ) ≤ v ^ a := Real.rpow_nonneg hv.le a
  have hEnorm : ‖E a psi v‖ ≤ Real.exp (-(k * v ^ a)) := by
    rw [norm_E, Real.exp_le_exp]
    nlinarith
  have hfac : ‖1 - ((a * v ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I)‖
      ≤ 1 + a * v ^ a := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [rotDeriv, rotBound]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    gcongr
  · rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    gcongr

/-- Continuity in `v` of `∂_v[v H(ψ,v)]` on `(0,∞)`. -/
theorem continuousOn_rotDeriv {a t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) :
    ContinuousOn (fun v : ℝ => rotDeriv a t psi v) (Ioi 0) := by
  have hne : ∀ v ∈ Ioi (0 : ℝ), (t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) ≠ 0 :=
    fun v _ => sub_mul_exp_ne_zero ht hsin v
  have hE := continuousOn_E a psi
  have hrpow : ContinuousOn (fun v : ℝ => ((a * v ^ a : ℝ) : ℂ)) (Ioi 0) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx))
  refine ContinuousOn.add (ContinuousOn.div ?_ (by fun_prop) hne) (ContinuousOn.div ?_ ?_ ?_)
  · exact (continuousOn_const.mul hE).mul (continuousOn_const.sub (hrpow.mul continuousOn_const))
  · exact (Complex.continuous_ofReal.continuousOn.mul continuousOn_const).mul hE
  · fun_prop
  · exact fun v hv => pow_ne_zero _ (hne v hv)

/-- Integrability of `∂_v[v H(ψ,v)]` on `(0,∞)`. -/
theorem integrableOn_rotDeriv {a t psi k s : ℝ} (ha0 : 0 < a) (ht : 0 < t) (hk : 0 < k)
    (hs : 0 < s) (hsin : s ≤ Real.sin psi) (hcos : k ≤ Real.cos (a * psi)) :
    IntegrableOn (fun v : ℝ => rotDeriv a t psi v) (Ioi 0) := by
  have hsin' : 0 < Real.sin psi := lt_of_lt_of_le hs hsin
  refine (integrableOn_rotBound (t := t) (s := s) ha0 hk).mono'
    ((continuousOn_rotDeriv ht hsin').aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact norm_rotDeriv_le ht hs hsin hcos hv ha0

/-- The boundary terms of the proof of the lemma `lem:rotation` ("Rotation invariance") of
`wright_laplace.tex` vanish, so `∫_0^∞ ∂_v[v H(ψ,v)] dv = 0`. -/
theorem integral_rotDeriv_eq_zero {a t psi k s : ℝ} (ha0 : 0 < a) (ht : 0 < t) (hk : 0 < k)
    (hs : 0 < s) (hsin : s ≤ Real.sin psi) (hcos : k ≤ Real.cos (a * psi)) :
    (∫ v in Ioi (0 : ℝ), rotDeriv a t psi v) = 0 := by
  have hsin' : 0 < Real.sin psi := lt_of_lt_of_le hs hsin
  have hts : 0 < t * s := by positivity
  -- the boundary term at `0`
  have hcA : ContinuousAt (fun v : ℝ => ((v ^ a : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_rpow_const 0 a (Or.inr ha0.le))
  have hEcont : ContinuousAt (fun v : ℝ => E a psi v) 0 :=
    Complex.continuous_exp.continuousAt.comp (hcA.neg.mul continuousAt_const)
  have hdenne : ((t : ℂ) - ((0 : ℝ) : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) ≠ 0 := by
    simpa using sub_mul_exp_ne_zero ht hsin' 0
  have hcont : ContinuousWithinAt (fun v : ℝ => (v : ℂ) * Dintegrand a t psi v) (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    exact Complex.continuous_ofReal.continuousAt.mul
      ((continuousAt_const.mul hEcont).div (by fun_prop) hdenne)
  -- the boundary term at `+∞`
  have htend : Filter.Tendsto (fun v : ℝ => (v : ℂ) * Dintegrand a t psi v) Filter.atTop
      (nhds 0) := by
    refine squeeze_zero_norm' (a := fun v : ℝ => v * Real.exp (-(k * v ^ a)) / (t * s)) ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with v hv
      have hDb : ‖Dintegrand a t psi v‖ ≤ Real.exp (-(k * v ^ a)) / (t * s) :=
        norm_Dintegrand_le' ht hs hsin hcos hv.le
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
      calc v * ‖Dintegrand a t psi v‖ ≤ v * (Real.exp (-(k * v ^ a)) / (t * s)) :=
            mul_le_mul_of_nonneg_left hDb hv.le
        _ = v * Real.exp (-(k * v ^ a)) / (t * s) := by ring
    · simpa using (tendsto_mul_exp_neg_mul_rpow_atTop hk ha0).div_const (t * s)
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivAt (fun v : ℝ => (v : ℂ) * Dintegrand a t psi v) (rotDeriv a t psi v) v :=
    fun v hv => hasDerivAt_mul_Dintegrand hv (sub_mul_exp_ne_zero ht hsin' v)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_rotDeriv ha0 ht hk hs hsin hcos) htend
  simpa using h

/-- Differentiation under the integral sign in the proof of the lemma `lem:rotation`
("Rotation invariance") of `wright_laplace.tex`: `D'(ψ) = 0` for `0 < ψ < min(π, π/(2a))`. -/
theorem hasDerivAt_D {a t psi : ℝ} (ha0 : 0 < a) (ht : 0 < t)
    (h0 : 0 < psi) (hlt : psi < min Real.pi (Real.pi / (2 * a))) :
    HasDerivAt (fun psi : ℝ => D a t psi) 0 psi := by
  have hpi := Real.pi_pos
  set R : ℝ := min Real.pi (Real.pi / (2 * a)) with hR
  set d : ℝ := min (psi / 2) ((R - psi) / 2) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hl : 0 < psi - d := by
    have : d ≤ psi / 2 := min_le_left _ _
    linarith
  have hrR : psi + d < R := by
    have : d ≤ (R - psi) / 2 := min_le_right _ _
    linarith
  set l : ℝ := psi - d with hlDef
  set r : ℝ := psi + d with hrDef
  have hlr : l ≤ r := by simp only [hlDef, hrDef]; linarith
  have hrpi : r < Real.pi := lt_of_lt_of_le hrR (min_le_left _ _)
  have harpi : a * r < Real.pi / 2 := by
    have h1 : r < Real.pi / (2 * a) := lt_of_lt_of_le hrR (min_le_right _ _)
    have h2 := mul_lt_mul_of_pos_left h1 ha0
    rwa [show a * (Real.pi / (2 * a)) = Real.pi / 2 by field_simp] at h2
  -- the uniform lower bound `s₀` for `sin` on `[l, r]`
  obtain ⟨w, hw, hwmin⟩ := isCompact_Icc.exists_isMinOn (s := Icc l r)
    (nonempty_Icc.2 hlr) Real.continuous_sin.continuousOn
  set s0 : ℝ := Real.sin w with hs0
  have hs0pos : 0 < s0 :=
    Real.sin_pos_of_pos_of_lt_pi (by cases hw with | intro h1 h2 => linarith)
      (by cases hw with | intro h1 h2 => linarith)
  have hs0le : ∀ x ∈ Icc l r, s0 ≤ Real.sin x := fun x hx => isMinOn_iff.1 hwmin x hx
  -- the uniform lower bound `κ` for `cos(a·)` on `[l, r]`
  set k : ℝ := Real.cos (a * r) with hk
  have hkpos : 0 < k := Real.cos_pos_of_mem_Ioo ⟨by nlinarith, harpi⟩
  have hkle : ∀ x ∈ Icc l r, k ≤ Real.cos (a * x) := by
    intro x hx
    refine Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by linarith) ?_
    exact mul_le_mul_of_nonneg_left hx.2 ha0.le
  have hball : Metric.ball psi d ⊆ Icc l r := by
    rw [Real.ball_eq_Ioo]
    exact Ioo_subset_Icc_self
  have hmem : psi ∈ Icc l r := ⟨by simp only [hlDef]; linarith, by simp only [hrDef]; linarith⟩
  have hsinpsi : 0 < Real.sin psi := lt_of_lt_of_le hs0pos (hs0le psi hmem)
  have hcospsi : 0 < Real.cos (a * psi) := lt_of_lt_of_le hkpos (hkle psi hmem)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (p : ℝ) (v : ℝ) => Dintegrand a t p v)
    (F' := fun (p : ℝ) (v : ℝ) => Complex.I * rotDeriv a t p v)
    (bound := rotBound a t k s0)
    (s := Metric.ball psi d)
    (Metric.ball_mem_nhds psi hd0)
    (by
      filter_upwards [Metric.ball_mem_nhds psi hd0] with x hx
      have hx' : 0 < Real.sin x := lt_of_lt_of_le hs0pos (hs0le x (hball hx))
      exact (continuousOn_Dintegrand ht hx').aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_Dintegrand' ha0 ht hsinpsi hcospsi)
    ((continuousOn_const.mul (continuousOn_rotDeriv ht hsinpsi)).aestronglyMeasurable
      measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv x hx
      have hv' : (0 : ℝ) < v := hv
      rw [norm_mul, Complex.norm_I, one_mul]
      exact norm_rotDeriv_le ht hs0pos (hs0le x (hball hx)) (hkle x (hball hx)) hv' ha0)
    (integrableOn_rotBound (t := t) (s := s0) ha0 hkpos)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv x hx
      have hx' : 0 < Real.sin x := lt_of_lt_of_le hs0pos (hs0le x (hball hx))
      exact hasDerivAt_Dintegrand_psi (sub_mul_exp_ne_zero ht hx' v))
  have hzero : (∫ v in Ioi (0 : ℝ), Complex.I * rotDeriv a t psi v) = 0 := by
    rw [integral_const_mul, integral_rotDeriv_eq_zero ha0 ht hkpos hs0pos (hs0le psi hmem)
      (hkle psi hmem), mul_zero]
  rw [← hzero]
  exact key.2

/-- The lemma `lem:rotation` ("Rotation invariance") of `wright_laplace.tex`: `D` is constant on
`(0, θ]`. -/
theorem D_eq_of_mem_Ioc {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    {psi₁ psi₂ : ℝ} (h1 : psi₁ ∈ Ioc 0 (theta a)) (h2 : psi₂ ∈ Ioc 0 (theta a)) :
    D a t psi₁ = D a t psi₂ := by
  set R : ℝ := min Real.pi (Real.pi / (2 * a)) with hR
  have hdiff : ∀ x ∈ Ioo 0 R, HasDerivAt (fun p : ℝ => D a t p) 0 x :=
    fun x hx => hasDerivAt_D ha0 ht hx.1 hx.2
  have hsub : Ioc 0 (theta a) ⊆ Ioo 0 R := fun x hx =>
    ⟨hx.1, lt_of_le_of_lt hx.2 (theta_lt_min ha0 ha1)⟩
  refine Convex.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (convex_Ioo 0 R) ?_ ?_ (hsub h1) (hsub h2)
  · exact fun x hx => ((hdiff x hx).differentiableAt).differentiableWithinAt
  · intro x hx
    have hfd := (hdiff x hx).hasFDerivAt.hasFDerivWithinAt (s := Ioo 0 R)
    rw [hfd.fderivWithin (uniqueDiffOn_Ioo 0 R x hx)]
    ext
    simp

/-- The lemma `lem:rotation` ("Rotation invariance") of `wright_laplace.tex`, in the form in
which it is used later: `D(ψ) = D(θ)` for every `ψ ∈ (0, θ]`. -/
theorem D_eq_D_theta {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    {psi : ℝ} (h : psi ∈ Ioc 0 (theta a)) :
    D a t psi = D a t (theta a) :=
  D_eq_of_mem_Ioc ha0 ha1 ht h ⟨theta_pos ha0 ha1, le_rfl⟩

end WrightLaplace
