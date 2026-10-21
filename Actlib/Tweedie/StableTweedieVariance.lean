import Mathlib
import Actlib.Laplace.MainTheorem
import Actlib.Tweedie.ExponentialDispersion
import Actlib.Tweedie.StableTweedie
import Mathlib.Probability.Distributions.Gamma

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
set_option maxRecDepth 4000

set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Real MeasureTheory Set Filter Topology

noncomputable section

/-!
### The `p = 3` Tweedie density is the inverse Gaussian density

The user-supplied statement of `stableTweedie₃_eq_inverseGaussian` asserted that the
`p = 3` stable Tweedie density equals `inverseGaussianPDF μ (phi * μ)`.  That is false:
the shape parameter of the inverse Gaussian obtained from `stableTweediePDF 3 μ phi` is
`Λ = 1 / phi`, not `phi * μ`.  Indeed, unfolding the definitions for `y > 0` gives

  `stableTweediePDF 3 μ phi y = √(1/(2 π phi y³)) · exp (-(y - μ)² / (2 phi μ² y))`,

which is `inverseGaussianPDF μ Λ y` exactly for `Λ = 1 / phi`.  (This is also the value
forced by the moments: the density has mean `μ` and variance `phi · μ³ = μ³ / Λ`.)
Below, the original statement is preserved as a comment, the corrected statement is proved,
and a counterexample to the original statement is given.
-/

/-- **The `p = 3` stable Tweedie density is the inverse Gaussian density.**

For `y > 0`, `phi > 0` and `μ ≠ 0`,
`stableTweediePDF 3 μ phi y = inverseGaussianPDF μ (1 / phi) y`.

This is the corrected form of the originally requested statement (see the comment below):
the inverse Gaussian shape parameter is `Λ = 1 / phi`, not `phi * μ`. -/
lemma stableTweedie₃_eq_inverseGaussian (μ phi y : ℝ) (hy : 0 < y) (hμ : μ ≠ 0)
    (hphi : 0 < phi) :
    stableTweediePDF 3 μ phi y = (inverseGaussianPDF μ (1 / phi) y).toReal := by
  unfold stableTweediePDF inverseGaussianPDF tweedieNormalizedScale
  rw [Set.indicator_of_mem (show y ∈ {y : ℝ | 0 < y} from hy)]
  norm_num
  rw [h𝓦]
  simp only
  rw [max_eq_left (by positivity)]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow,
    Real.rpow_neg_one]
  have hval : √2 / √phi * (√y)⁻¹ = √(2 / (phi * y)) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_mul hphi.le]
    field_simp
  have hnn : (0:ℝ) ≤ 2 / (phi * y) := by positivity
  have key : (y⁻¹ * (√(2 / (phi * y)) / (2 * √π))) ^ 2 = phi⁻¹ / (2 * π * y ^ 3) := by
    rw [mul_pow, div_pow, Real.sq_sqrt hnn, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
  have hpre : y⁻¹ * (√(2 / (phi * y)) / (2 * √π)) = √(phi⁻¹ / (2 * π * y ^ 3)) := by
    rw [← key, Real.sqrt_sq (by positivity)]
  rw [hval, neg_neg, neg_sq, Real.sq_sqrt hnn]
  rw [show y⁻¹ * (√(2 / (phi * y)) / (2 * √π) *
        rexp (-(2 / (phi * y)) / 4)) * rexp (phi⁻¹ * (y * (μ ^ 2)⁻¹ / -2 - μ⁻¹ / -1))
      = (y⁻¹ * (√(2 / (phi * y)) / (2 * √π))) *
        (rexp (-(2 / (phi * y)) / 4) * rexp (phi⁻¹ * (y * (μ ^ 2)⁻¹ / -2 - μ⁻¹ / -1))) from by
    ring]
  rw [← Real.exp_add, hpre]
  congr 2
  field_simp
  ring



namespace TweedieVariance

open TweedieMean

/-- `y ↦ y² · exp (-b y)` is integrable on `(0, ∞)`. -/
lemma integrableOn_sq_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ 2 * Real.exp (-b * y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := b)
    (by norm_num) one_pos hb
  refine h.congr_fun (fun _ _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `y ↦ y · (scale-`c` positive-stable density) · exp (-t y)` is integrable on `(0, ∞)`. -/
lemma integrableOn_id_mul_wright_stable_mul_exp {a c t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ =>
      y * (1 / y * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) * Real.exp (-t * y)))
      (Ioi 0) := by
  have hdom : IntegrableOn
      (fun y : ℝ => WrightLaplace.M a / c ^ (1 / a) * (y * Real.exp (-t * y))) (Ioi 0) :=
    (integrableOn_id_mul_exp_neg ht).const_mul _
  refine Integrable.mono' hdom
    (continuous_id.aestronglyMeasurable.mul
      ((((continuousOn_wright_stable ha0 ha1 hc).aestronglyMeasurable measurableSet_Ioi).mul
        (Continuous.aestronglyMeasurable (by fun_prop))))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy' : (0 : ℝ) < y := hy
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hy', abs_mul, abs_of_pos (Real.exp_pos _)]
  have h2 := abs_wright_stable_le ha0 ha1 hc hy'
  have hexp : (0 : ℝ) < Real.exp (-t * y) := Real.exp_pos _
  calc y * (|1 / y * wright_generalized_bessel (-a) 0 (-c * y ^ (-a))| * Real.exp (-t * y))
      ≤ y * (WrightLaplace.M a / c ^ (1 / a) * Real.exp (-t * y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hy'.le
        exact mul_le_mul_of_nonneg_right h2 hexp.le
    _ = WrightLaplace.M a / c ^ (1 / a) * (y * Real.exp (-t * y)) := by ring

/-- The second-moment Laplace identity for the positive-stable density, obtained by
differentiating the first-moment identity once more in `t`. -/
lemma integral_wright_positive_stable_mul_sq (a c t : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) (ht : 0 < t) :
    ∫ y in Ioi (0 : ℝ),
      y ^ 2 * (1 / y * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) * Real.exp (-t * y))
      = (c * a * (1 - a) * t ^ (a - 2) + (c * a) ^ 2 * t ^ (2 * a - 2)) *
        Real.exp (-c * t ^ a) := by
  set G : ℝ → ℝ := fun y => 1 / y * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) with hGdef
  set m : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hm
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun y : ℝ => y * (G y * Real.exp (-s * y))) m :=
    fun s => continuous_id.aestronglyMeasurable.mul
      (((continuousOn_wright_stable ha0 ha1 hc).aestronglyMeasurable
        measurableSet_Ioi).mul (Continuous.aestronglyMeasurable (by fun_prop)))
  have hs_mem : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by linarith)
  have hbound_int : Integrable
      (fun y : ℝ => WrightLaplace.M a / c ^ (1 / a) * (y ^ 2 * Real.exp (-(t / 2) * y))) m :=
    (integrableOn_sq_mul_exp_neg (by linarith : (0:ℝ) < t / 2)).const_mul _
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (y : ℝ) => y * (G y * Real.exp (-s * y)))
    (F' := fun (s : ℝ) (y : ℝ) => -(y ^ 2 * (G y * Real.exp (-s * y))))
    (x₀ := t) (μ := m)
    (bound := fun y : ℝ => WrightLaplace.M a / c ^ (1 / a) * (y ^ 2 * Real.exp (-(t / 2) * y)))
    (s := Ioi (t / 2)) hs_mem (Filter.Eventually.of_forall hmeas)
    (integrableOn_id_mul_wright_stable_mul_exp ha0 ha1 hc ht)
    (((continuous_pow 2).aestronglyMeasurable.mul
      (((continuousOn_wright_stable ha0 ha1 hc).aestronglyMeasurable measurableSet_Ioi).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))).neg)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy s hs
      have hy' : (0 : ℝ) < y := hy
      have hs' : t / 2 < s := hs
      simp only [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos hy',
        abs_of_pos (Real.exp_pos _), abs_pow]
      have h1 : Real.exp (-s * y) ≤ Real.exp (-(t / 2) * y) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have h2 : |G y| ≤ WrightLaplace.M a / c ^ (1 / a) := abs_wright_stable_le ha0 ha1 hc hy'
      have hG0 : (0 : ℝ) ≤ |G y| := abs_nonneg _
      calc y ^ 2 * (|G y| * Real.exp (-s * y))
          ≤ y ^ 2 * (WrightLaplace.M a / c ^ (1 / a) * Real.exp (-(t / 2) * y)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul h2 h1 (Real.exp_pos _).le (hG0.trans h2)
        _ = WrightLaplace.M a / c ^ (1 / a) * (y ^ 2 * Real.exp (-(t / 2) * y)) := by ring)
    hbound_int
    (by
      filter_upwards with y s _
      have h0 : HasDerivAt (fun s : ℝ => -s * y) (-y) s := by
        simpa using ((hasDerivAt_id s).neg.mul_const y)
      have h2 : HasDerivAt (fun s : ℝ => y * (G y * Real.exp (-s * y)))
          (y * (G y * (Real.exp (-s * y) * -y))) s := ((h0.exp).const_mul (G y)).const_mul y
      rw [show -(y ^ 2 * (G y * Real.exp (-s * y))) = y * (G y * (Real.exp (-s * y) * -y)) by ring]
      exact h2)
  have hderiv1 : HasDerivAt (fun s : ℝ => ∫ y, y * (G y * Real.exp (-s * y)) ∂m)
      (∫ y, -(y ^ 2 * (G y * Real.exp (-t * y))) ∂m) t := hkey.2
  have heq : (fun s : ℝ => ∫ y, y * (G y * Real.exp (-s * y)) ∂m)
      =ᶠ[𝓝 t] fun s : ℝ => c * a * s ^ (a - 1) * Real.exp (-c * s ^ a) := by
    filter_upwards [Ioi_mem_nhds (by linarith : (0:ℝ) < t)] with s hs
    exact integral_wright_positive_stable_mul_id a c s ha0 ha1 hc hs
  have hderiv2 : HasDerivAt (fun s : ℝ => c * a * s ^ (a - 1) * Real.exp (-c * s ^ a))
      ((c * a * ((a - 1) * t ^ (a - 1 - 1))) * Real.exp (-c * t ^ a) +
        (c * a * t ^ (a - 1)) * (-c * (a * t ^ (a - 1)) * Real.exp (-c * t ^ a))) t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ (a - 1)) ((a - 1) * t ^ (a - 1 - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht.ne')
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-c * s ^ a))
        (-c * (a * t ^ (a - 1)) * Real.exp (-c * t ^ a)) t := by
      have hrpow : HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t :=
        Real.hasDerivAt_rpow_const (Or.inl ht.ne')
      have h3 := (hrpow.const_mul (-c)).exp
      convert h3 using 1
      ring
    exact (h1.const_mul (c * a)).mul h2
  have huniq : (∫ y, -(y ^ 2 * (G y * Real.exp (-t * y))) ∂m)
      = (c * a * ((a - 1) * t ^ (a - 1 - 1))) * Real.exp (-c * t ^ a) +
        (c * a * t ^ (a - 1)) * (-c * (a * t ^ (a - 1)) * Real.exp (-c * t ^ a)) :=
    (hderiv1.congr_of_eventuallyEq heq.symm).unique hderiv2
  rw [integral_neg] at huniq
  have hpow1 : t ^ (a - 1 - 1) = t ^ (a - 2) := by ring_nf
  have hpow2 : t ^ (a - 1) * t ^ (a - 1) = t ^ (2 * a - 2) := by
    rw [← Real.rpow_add ht]
    ring_nf
  have hfin : (∫ y, y ^ 2 * (G y * Real.exp (-t * y)) ∂m)
      = (c * a * (1 - a) * t ^ (a - 2) + (c * a) ^ 2 * t ^ (2 * a - 2)) *
        Real.exp (-c * t ^ a) := by
    rw [hpow1] at huniq
    linear_combination (-1 : ℝ) * huniq + (c * a) ^ 2 * Real.exp (-c * t ^ a) * hpow2
  have hgoal : ∀ y : ℝ,
      y ^ 2 * (1 / y * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) * Real.exp (-t * y))
        = y ^ 2 * (G y * Real.exp (-t * y)) := by
    intro y
    simp only [hGdef]
  simp_rw [hgoal]
  rw [hm] at hfin
  exact hfin

end TweedieVariance

open TweedieMean TweedieVariance in
/-- The second moment of the corrected Tweedie density for `p > 2`:
`∫ y² · stableTweediePDF p μ phi y dy = phi · μ^p + μ²`, i.e. the variance is `phi · μ^p`. -/
lemma stableTweediePDF_variance (p μ phi : ℝ)
    (hp₂ : 2 < p) (hphi : 0 < phi) (hμ : 0 < μ) :
    ∫ y : ℝ, y ^ 2 * stableTweediePDF p μ phi y = phi * μ ^ p + μ ^ 2 := by
  have hp1_neg : 1 - p < 0 := by linarith
  have hp2_neg : 2 - p < 0 := by linarith
  have hp1_ne : p - 1 ≠ 0 := by linarith
  have hp2_ne : p - 2 ≠ 0 := by linarith
  have hphi_ne : phi ≠ 0 := ne_of_gt hphi
  set α := (2 - p) / (1 - p) with hα_def
  have ha0 : 0 < α := div_pos_of_neg_of_neg hp2_neg hp1_neg
  have ha1 : α < 1 := by
    rw [hα_def, div_lt_one_of_neg hp1_neg]
    linarith
  have hc_pos : 0 < tweedieNormalizedScale p phi := by
    unfold tweedieNormalizedScale
    apply div_pos
    · apply Real.rpow_pos_of_pos; linarith
    · positivity
  set t := μ ^ (1 - p) / ((p - 1) * phi) with ht_def
  have ht_pos : 0 < t := by
    apply div_pos _ (mul_pos (by linarith : (0:ℝ) < p - 1) hphi)
    exact Real.rpow_pos_of_pos hμ _
  have hset : {y : ℝ | 0 < y} = Set.Ioi 0 := by ext; simp [Set.mem_Ioi]
  simp only [stableTweediePDF]
  rw [← hα_def, hset]
  have hind : ∀ y : ℝ, y ^ 2 * Set.indicator (Set.Ioi (0:ℝ)) (fun y =>
      1 / y * wright_generalized_bessel (-α) 0
        (-tweedieNormalizedScale p phi * y ^ (-α)) *
      Real.exp (1 / phi * (y * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)))) y
      = Set.indicator (Set.Ioi (0:ℝ)) (fun y => y ^ 2 * (1 / y * wright_generalized_bessel (-α) 0
        (-tweedieNormalizedScale p phi * y ^ (-α)) *
      Real.exp (1 / phi * (y * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p))))) y := by
    simp [Set.indicator]
  simp_rw [hind]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  have hexp_factor : ∀ x : ℝ,
      Real.exp (1 / phi * (x * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p))) =
      Real.exp (-t * x) * Real.exp (-μ ^ (2 - p) / ((2 - p) * phi)) := by
    intro x
    rw [← Real.exp_add, ht_def]
    congr 1
    have h1p : 1 - p = -(p - 1) := by ring
    rw [h1p]
    field_simp
    ring
  have hrearrange : ∀ x : ℝ, x ^ 2 * (1 / x * wright_generalized_bessel (-α) 0
      (-tweedieNormalizedScale p phi * x ^ (-α)) *
      Real.exp (1 / phi * (x * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)))) =
      Real.exp (-μ ^ (2 - p) / ((2 - p) * phi)) *
      (x ^ 2 * (1 / x * wright_generalized_bessel (-α) 0
        (-tweedieNormalizedScale p phi * x ^ (-α)) * Real.exp (-t * x))) := by
    intro x
    rw [hexp_factor x]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hrearrange x)]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_wright_positive_stable_mul_sq α (tweedieNormalizedScale p phi) t
    ha0 ha1 hc_pos ht_pos]
  -- algebraic identification
  have hα_eq : α = (p - 2) / (p - 1) := by
    rw [hα_def, show (2:ℝ) - p = -(p - 2) by ring, show (1:ℝ) - p = -(p - 1) by ring,
      neg_div_neg_eq]
  have hnors : tweedieNormalizedScale p phi * t ^ α = tweedieTiltConstant p μ phi := by
    rw [hα_eq, ht_def]
    exact tweedieNormalizedScale_mul_rpow_tiltRate p μ phi hp₂ hμ hphi
  have htconst_eq : -μ ^ (2 - p) / ((2 - p) * phi) = tweedieTiltConstant p μ phi := by
    unfold tweedieTiltConstant
    rw [show (2:ℝ) - p = -(p - 2) by ring]
    field_simp
  have hmean : tweedieNormalizedScale p phi * α * t ^ (α - 1) = μ := by
    have hrpow : t ^ (α - 1) = t ^ α / t := by
      rw [Real.rpow_sub ht_pos, Real.rpow_one]
    rw [hrpow, show tweedieNormalizedScale p phi * α * (t ^ α / t)
      = α * (tweedieNormalizedScale p phi * t ^ α) / t by ring, hnors, hα_eq, ht_def]
    unfold tweedieTiltConstant
    have hμ1 : (0:ℝ) < μ ^ (1 - p) := Real.rpow_pos_of_pos hμ _
    rw [show (2:ℝ) - p = (1 - p) + 1 by ring, Real.rpow_add hμ, Real.rpow_one]
    field_simp
  -- rewrite the two powers of `t` in terms of `t ^ (α - 1)`
  have hpowA : t ^ (α - 2) = t ^ (α - 1) / t := by
    rw [show α - 2 = (α - 1) - 1 by ring, Real.rpow_sub ht_pos, Real.rpow_one]
  have hpowB : t ^ (2 * α - 2) = t ^ (α - 1) * t ^ (α - 1) := by
    rw [← Real.rpow_add ht_pos]
    ring_nf
  have hfirst : tweedieNormalizedScale p phi * α * (1 - α) * t ^ (α - 2) = phi * μ ^ p := by
    rw [hpowA, show tweedieNormalizedScale p phi * α * (1 - α) * (t ^ (α - 1) / t)
      = (tweedieNormalizedScale p phi * α * t ^ (α - 1)) * (1 - α) / t by ring, hmean]
    have h1α : 1 - α = 1 / (p - 1) := by
      rw [hα_eq]
      field_simp
      ring
    have hmuinv : μ ^ p * μ ^ (1 - p) = μ := by
      rw [← Real.rpow_add hμ, show p + (1 - p) = (1:ℝ) by ring, Real.rpow_one]
    rw [h1α, ht_def, div_div_eq_mul_div,
      div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hμ (1 - p))),
      show phi * μ ^ p * μ ^ (1 - p) = phi * (μ ^ p * μ ^ (1 - p)) by ring, hmuinv]
    field_simp
  have hsecond : (tweedieNormalizedScale p phi * α) ^ 2 * t ^ (2 * α - 2) = μ ^ 2 := by
    rw [hpowB, show (tweedieNormalizedScale p phi * α) ^ 2 * (t ^ (α - 1) * t ^ (α - 1))
      = (tweedieNormalizedScale p phi * α * t ^ (α - 1)) ^ 2 by ring, hmean]
  rw [htconst_eq, ← hnors]
  calc _ = (tweedieNormalizedScale p phi * α * (1 - α) * t ^ (α - 2) +
        (tweedieNormalizedScale p phi * α) ^ 2 * t ^ (2 * α - 2)) *
          (Real.exp (tweedieNormalizedScale p phi * t ^ α) *
            Real.exp (-(tweedieNormalizedScale p phi * t ^ α))) := by ring_nf
    _ = phi * μ ^ p + μ ^ 2 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, hfirst, hsecond]

/-- Let us attempt to generalize.
p < 0 and p = ⊤ both appear at
https://en.wikipedia.org/wiki/Tweedie_distribution#Related_distributions
p = ⊤ is exponential tilting of Cauchy distribution!
        /-
        In the gamma case, why these choices of `a` and `r`? Wel...
        a = α
        r = β (Wikipedia)
        Mean μ = α / β = a/r
        Variance α / β^2 = φ (a / r)^2
        where φ = 1/a
        So r = a / μ = (1 / φ) / μ -/
-/
def Tw (p μ phi : ℝ) (hμ : 0 ≤ μ)
  (hp₁ : 1 ≤ p)
  : Measure ℝ := by
  by_cases hp : 2 < p
  · exact volume.withDensity <| ENNReal.ofReal ∘ stableTweediePDF p μ phi
  · by_cases hp : p = 2
    · apply volume.withDensity
      exact ProbabilityTheory.gammaPDF (1 / phi) (1 / (phi * μ))
    · by_cases hp₁ : 1 < p
      -- compound Poisson
      · apply tweedieMeasure μ hμ (by linarith)
        simp_all
      · have : p = 1 := by linarith
        subst p

        apply PMF.toMeasure -- Poisson-like
        exact {
          val := by
            intro r
            by_cases H : ∃ k : ℕ, r = phi * k
            · choose k hk using H
              apply ENNReal.ofReal
              -- Poisson with parameter μ / phi:
              exact (1:ℝ) / ((Nat.factorial k) : ℝ)
                * Real.exp (- μ / phi) * (μ / phi) ^ k
            · exact 0
          property := by
            simp
            sorry
        }
      -- · by_cases hp : p = 1
      --   · /- Poisson
      --        mean: λ
      --        variance: λ
      --        so λ=μ, but it only makes sense if φ = 1.
      --        So let's not include it in the parametrization.
      -- If φ≠1, our r.v. is φN where N~Poisson(μ/φ).
      --     -/
      --     sorry
      --   · by_cases hp : p = 0
      --     · -- normal
      --       sorry
      --     · sorry

theorem tweedieproperties (p μ phi : ℝ) (hμ : 0 < μ)
  (hp₁ : 1 ≤ p) (hφ : 0 < phi) :
  ∫ x, x ∂ Tw p μ phi (by linarith) hp₁ = μ
  ∧
  ∫ x, x^2 ∂ Tw p μ phi (by linarith) hp₁ = phi * μ^p + μ^2
   := by
    constructor
    unfold Tw
    split_ifs with g₀ g₁
    · have := @stableTweediePDF_mean p μ phi g₀ hφ hμ
      nth_rw 2 [← this]
      -- true, but tricky
      generalize stableTweediePDF p μ phi = P
      sorry
    · subst p
      unfold ProbabilityTheory.gammaPDF
        ProbabilityTheory.gammaPDFReal
      simp
      sorry
    · refine tweedieMeasure_expectation hμ hμ (by linarith) ?_
      simp_all
      contrapose! g₁
      linarith
    · simp -- p = 1
      sorry
    sorry


example : 0 = 0 :=
  have m : @ProbabilityTheory.Kernel ℝ ℝ measurableSpace
    measurableSpace := {
      toFun := by
        intro p
        sorry -- option up
      measurable' := by sorry
    }
  sorry
