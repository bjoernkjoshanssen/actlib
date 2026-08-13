import Mathlib
import Actlib.Laplace.StandingData

/-!
# The target integrand `g` and the ray integrand `E`

This file sets up the objects of `wright_laplace.tex` ("A contour-free proof of the unit-scale
positive-stable Laplace-transform identity") that are needed to state the lemma `lem:ray`
("Ray representation") and the corollary `cor:bounds` ("Bounds, continuity, integrability"):

* `WrightLaplace.wrightBessel`, the Wright generalized Bessel function
  `W_{Λ,μ}(z) = ∑_{k ≥ 0} z^k / (k! Γ(Λ k + μ))` of the abstract of the source;
* `WrightLaplace.g`, the target integrand `g(y) = (1/y) W_{-a,0}(-y^{-a})` of equation `eq:gdef`,
  together with `WrightLaplace.g_eq_tsum`, the series form
  `g(y) = ∑_k (-1)^k y^{-ak-1} / (k! Γ(-ak))` also displayed in `eq:gdef`;
* `WrightLaplace.E`, the function `E(ψ, v) = exp(-v^a e^{iaψ})` of equation `eq:E`, and the
  modulus identity `|E(ψ,v)| = e^{-v^a cos(aψ)}` recorded there;
* `WrightLaplace.rayIntegrand` and `WrightLaplace.rayIntegral`, the integrand
  `v ↦ exp(y v e^{iθ}) E(θ, v)` and the quantity
  `I(y) = e^{iθ} ∫_0^∞ exp(y v e^{iθ}) E(θ, v) dv` of the lemma `lem:ray`, together with the
  modulus computation `|exp(y v e^{iθ}) E(θ,v)| = e^{-c₁ y v} e^{-c₂ v^a}` used in its proof.

All junk-value conventions are those of Mathlib, which are exactly the conventions
`conv:junk` and `conv:powers` of the source.
-/

namespace WrightLaplace

open MeasureTheory Set Complex

/-- The **Wright generalized Bessel function**
`W_{Λ,μ}(z) = ∑_{k ≥ 0} z^k / (k! Γ(Λ k + μ))` of `wright_laplace.tex` (see the abstract, where
it is called `wright_generalized_bessel`). -/
noncomputable def wrightBessel (L m : ℝ) (z : ℝ) : ℝ :=
  ∑' k : ℕ, z ^ k / ((k.factorial : ℝ) * Real.Gamma (L * k + m))

/-- The **target integrand** `g(y) = (1/y) W_{-a,0}(-y^{-a})` of equation `eq:gdef` in
`wright_laplace.tex`. -/
noncomputable def g (a y : ℝ) : ℝ := (1 / y) * wrightBessel (-a) 0 (-(y ^ (-a)))

/-- The series form of the target integrand displayed in equation `eq:gdef` of
`wright_laplace.tex`:
`g(y) = ∑_{k=0}^{∞} (-1)^k y^{-ak-1} / (k! Γ(-ak))` for `y > 0`.
(By Convention `conv:junk` the `k = 0` term vanishes.) -/
theorem g_eq_tsum {a y : ℝ} (hy : 0 < y) : g a y
    = ∑' k : ℕ, (-1) ^ k * y ^ (-(a * k) - 1) / ((k.factorial : ℝ) * Real.Gamma (-(a * k))) := by
  rw [g, wrightBessel, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hpow : (-(y ^ (-a))) ^ k = (-1) ^ k * y ^ (-(a * k)) := by
    rw [neg_pow, ← Real.rpow_natCast (y ^ (-a)) k, ← Real.rpow_mul hy.le]
    ring_nf
  rw [hpow]
  have h1 : y ^ (-(a * k) - 1) = y ^ (-(a * k)) * (1 / y) := by
    rw [Real.rpow_sub hy, Real.rpow_one]
    ring
  rw [h1, show (-a) * (k : ℝ) + 0 = -(a * k) by ring]
  ring

/-- The function `E(ψ, v) = exp(-v^a e^{iaψ})` of equation `eq:E` in `wright_laplace.tex`. -/
noncomputable def E (a psi v : ℝ) : ℂ :=
  Complex.exp (-((v ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I))

/-- The modulus identity `|E(ψ,v)| = e^{-v^a cos(aψ)}` recorded just after equation `eq:E`
in `wright_laplace.tex`. -/
theorem norm_E (a psi v : ℝ) : ‖E a psi v‖ = Real.exp (-(v ^ a * Real.cos (a * psi))) := by
  rw [E, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.exp_re]

/-- The integrand `v ↦ exp(y v e^{iθ}) E(θ, v)` of the lemma `lem:ray` ("Ray representation")
in `wright_laplace.tex`. -/
noncomputable def rayIntegrand (a y v : ℝ) : ℂ :=
  Complex.exp ((y * v : ℝ) * Complex.exp ((theta a : ℝ) * Complex.I)) * E a (theta a) v

/-- The quantity `I(y) = e^{iθ} ∫_0^∞ exp(y v e^{iθ}) E(θ, v) dv` of the lemma `lem:ray`
("Ray representation") in `wright_laplace.tex`. -/
noncomputable def rayIntegral (a y : ℝ) : ℂ :=
  Complex.exp ((theta a : ℝ) * Complex.I) * ∫ v in Ioi (0 : ℝ), rayIntegrand a y v

/-- The modulus computation of the proof of the lemma `lem:ray` ("Ray representation") in
`wright_laplace.tex`:
`|exp(y v e^{iθ}) E(θ,v)| = e^{y v cos θ} e^{-v^a cos(aθ)} = e^{-c₁ y v} e^{-c₂ v^a}`. -/
theorem norm_rayIntegrand (a y v : ℝ) :
    ‖rayIntegrand a y v‖ = Real.exp (-(c₁ a * (y * v))) * Real.exp (-(c₂ a * v ^ a)) := by
  rw [rayIntegrand, norm_mul, norm_E, Complex.norm_exp]
  congr 2
  · simp only [c₁]
    simp [Complex.mul_re, Complex.exp_re]
    ring
  · rw [c₂]; ring

/-- The bound `|exp(y v e^{iθ}) E(θ,v)| ≤ e^{-c₂ v^a}` for `y ≥ 0`, `v ≥ 0`, used in the proof of
the corollary `cor:bounds` ("Bounds, continuity, integrability") of `wright_laplace.tex`. -/
theorem norm_rayIntegrand_le {a y v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    ‖rayIntegrand a y v‖ ≤ Real.exp (-(c₂ a * v ^ a)) := by
  rw [norm_rayIntegrand]
  have h1 : Real.exp (-(c₁ a * (y * v))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := c₁_pos ha0 ha1
    have : 0 ≤ c₁ a * (y * v) := by positivity
    linarith
  nlinarith [Real.exp_pos (-(c₂ a * v ^ a)), Real.exp_pos (-(c₁ a * (y * v)))]

/-- The bound `|exp(y v e^{iθ}) E(θ,v)| ≤ e^{-c₁ y v}`, the dominating function used for the
integrability assertion of the lemma `lem:ray` ("Ray representation") of
`wright_laplace.tex`. -/
theorem norm_rayIntegrand_le' {a y v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hv : 0 ≤ v) :
    ‖rayIntegrand a y v‖ ≤ Real.exp (-(c₁ a * (y * v))) := by
  rw [norm_rayIntegrand]
  have h1 : Real.exp (-(c₂ a * v ^ a)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h := c₂_pos ha0 ha1
    have : 0 ≤ c₂ a * v ^ a := by positivity
    linarith
  nlinarith [Real.exp_pos (-(c₂ a * v ^ a)), Real.exp_pos (-(c₁ a * (y * v)))]

/-- Continuity of the integrand `v ↦ exp(y v e^{iθ}) E(θ, v)` of the lemma `lem:ray`
("Ray representation") of `wright_laplace.tex` on `(0, ∞)`. -/
theorem continuousOn_rayIntegrand (a y : ℝ) : ContinuousOn (rayIntegrand a y) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine Complex.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    exact ContinuousOn.neg (Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (ne_of_gt hx)))

end WrightLaplace
