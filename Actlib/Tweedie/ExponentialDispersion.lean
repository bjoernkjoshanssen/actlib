/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib
import Actlib.Tweedie.Tweedie

/-!
# Exponential dispersion model
-/
open scoped BigOperators Pointwise NNReal ENNReal
open MeasureTheory ProbabilityTheory Real Set

noncomputable section

namespace tweedie

variable (p : ℝ)

def theta_of_mu (μ : ℝ) := μ ^ (1 - p) / (1 - p)

def mu_of_theta (θ : ℝ) := (θ * (1 - p)) ^ (1 / (1 - p))

/-- If `θ = μ ^ (1 - p) / (1 - p)`, then
`μ = (θ * (1 - p)) ^ (1 / (1 - p))`. -/
lemma theta_of_mu_of_theta (hp₁ : 1 < p)
    {θ : ℝ} (hθ : θ < 0) :
  tweedie.theta_of_mu p (tweedie.mu_of_theta p θ) = θ := by
    unfold tweedie.theta_of_mu tweedie.mu_of_theta
    have h₃ : 1 - p ≠ 0 := by linarith
    field_simp
    have h₁ : 1 - p < 0 := by linarith
    have h₂ : (θ * (1 -p)) > 0 := by
        apply mul_pos_of_neg_of_neg hθ h₁
    have {x y : ℝ} (hx : 0 < x) (hy : 0 > y)
        : (x ^ (1 / y)) ^ y = x := by
        refine (eq_rpow_inv ?_ ?_ ?_).mp ?_
        · positivity
        · linarith
        · linarith
        · simp
    apply this h₂ h₁

/-- For completeness, a (not necessarily useful)
companion to `tweedieTheta_of_mu_of_theta`. -/
lemma mu_of_theta_of_mu (hp₁ : p ≠ 1) {μ : ℝ} (hθ : 0 ≤ μ) :
    tweedie.mu_of_theta p (tweedie.theta_of_mu p μ) = μ := by
  unfold tweedie.mu_of_theta tweedie.theta_of_mu
  have : 1 - p ≠ 0 := by contrapose! hp₁;linarith
  generalize 1 - p = a at *
  field_simp
  rw [one_div]
  refine rpow_rpow_inv hθ this

def kappa_of_mu (μ : ℝ) := μ ^ (2 - p) / (2 - p)

def kappa_of_theta (p θ : ℝ) : ℝ := kappa_of_mu p (mu_of_theta p θ)

lemma kappa_of_theta_of_mu (hp : p ≠ 1) {μ : ℝ} (hμ : 0 ≤ μ) :
    tweedie.kappa_of_mu p μ  = tweedie.kappa_of_theta p (tweedie.theta_of_mu p μ) := by
  congr
  unfold tweedie.theta_of_mu tweedie.mu_of_theta
  have : 1 - p ≠ 0 := sub_ne_zero_of_ne hp.symm
  field_simp
  generalize 1 - p = α at *
  rw [← rpow_mul]
  · field_simp
    exact Eq.symm (rpow_one μ)
  · exact hμ

end tweedie

lemma isItTrue (p θ φ t : ℝ) (hφ : 0 < φ) (hθ : θ < 0)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    (tweedie.kappa_of_theta p (θ + φ * t) - tweedie.kappa_of_theta p θ)  / φ =
    log (∫ x, exp (t * x) ∂ tweedieMeasure (tweedie.mu_of_theta p θ)
        (show 0 ≤ φ by linarith) (by linarith)
        (by linarith)) := by
  unfold tweedie.kappa_of_theta tweedie.kappa_of_mu tweedie.mu_of_theta

--   by_cases H : t = 0
--   · subst t
--     simp only [mul_zero, add_zero, sub_self, zero_div, zero_mul, exp_zero, integral_const,
--       smul_eq_mul, mul_one]
--     symm
--     refine log_eq_zero.mpr ?_
--     right
--     left
--     refine isProbabilityMeasure_iff_real.mp ?_
--     apply tweedieMeasure_prob
--     · unfold tweedie.mu_of_theta
--       apply rpow_pos_of_pos
--       nlinarith
--     · linarith
--     · exact hp₁
--     · exact hp₂
  sorry




structure ExponentialDispersionFamily (f : ℝ → ℝ≥0 → ℝ → ℝ) where
  κ : ℝ → ℝ -- cumulant
  baseDensity : ℝ≥0 → ℝ → ℝ -- usually not itself a PDF
  Θ : Set ℝ
  hΘ : IsOpen Θ
  hnorm : ∀ v, ∀ t ∈ Θ, ∫ x, f t v x ≤ 1

-- not = 1 for Tweedie "PDF" !
-- requiring ≤ 1 is maybe a funny condition but
-- we can prove it for both Gaussian and Tweedian
-- even when v = 0.

  eq_exp :
    ∀ θ ∈ Θ, f θ = fun φ x => baseDensity φ x * exp ((θ * x - κ θ) / φ)


def gaussianEDF :
    ExponentialDispersionFamily gaussianPDFReal where
  κ := fun θ => θ ^ 2 / 2
  baseDensity := fun v x => (1 / √(2 * π * v)) * exp (- x ^ 2 / (2 * v))
  Θ := univ
  hΘ := isOpen_univ
  hnorm := by
    intro v t _
    by_cases H : v = 0
    · subst v;simp
    rw [integral_gaussianPDFReal_eq_one t H]
  eq_exp := by
    intro θ _
    ext v x
    unfold gaussianPDFReal
    repeat rw [mul_assoc]
    congr
    · field_simp
    rw [← exp_add]
    congr
    field_simp
    ring_nf


/-!
## The mean of an EDM is `A'(θ)`

We work with a *real-valued* density `f θ v : ℝ → ℝ` (this is the natural setting for
differentiating under the integral sign, which requires a real/Banach-valued integrand
the `ℝ≥0∞`-valued Lebesgue integral does not support the parametric differentiation
API).  For a fixed dispersion parameter `v > 0` and a canonical parameter `θ`, the density is
`f θ v x = h v x * exp ((θ * x - A θ) / v)` and the mean of the corresponding distribution is
`∫ x, x * f θ v x`.  We show this equals `deriv A θ`.
-/


/-!
## Exponential dispersion families with a natural-parameter domain

The open-domain assumption lets ordinary two-sided derivatives be used at each parameter.
The local domination neighborhoods are required to lie inside the parameter domain.
-/

lemma EDF_hasDerivAt_theta {f : ℝ → ℝ≥0 → ℝ → ℝ}
    (E : ExponentialDispersionFamily f) (v : ℝ≥0)
    (hA : DifferentiableOn ℝ E.κ E.Θ) (x : ℝ) {θ : ℝ} (hθ : θ ∈ E.Θ) :
    HasDerivAt (fun t => f t v x) (f θ v x * (x - deriv E.κ θ) / (v : ℝ)) θ := by
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1
  · exact fun t => E.baseDensity v x * exp ((t * x - E.κ t) / v)
  · convert HasDerivAt.const_mul (E.baseDensity v x)
        (((hasDerivAt_mul_const x).sub
        (hA.hasDerivAt (E.hΘ.mem_nhds hθ))).div_const _).exp
        using 1
    · rfl
    · ext y
      simp only [Pi.sub_apply, mul_eq_mul_left_iff, exp_eq_exp]
      left
      rfl
    · have := E.eq_exp θ hθ
      simp_all only [mul_comm, Pi.sub_apply, mul_assoc]
      by_cases H : v.toReal = 0
      · rw [H]
        simp
      · field_simp
  · --filter_upwards [E.hΘ.mem_nhds hθ] with t ht
    -- the above line equivalent to these three:
    apply Filter.mem_of_superset <| E.hΘ.mem_nhds hθ
    intro t ht
    simp only [mem_setOf_eq]
    rw [E.eq_exp t ht]


lemma integral_score_scale
    (p : ℝ → ℝ) (m : ℝ) {v : ℝ} (hv : v ≠ 0) :
    v * (∫ x, x * (p x * (x - m) / v)) =
         ∫ x, x * (p x * (x - m)) := by
  rw [← integral_const_mul]
  field_simp

lemma integral_centered_first_moment
    {p : ℝ → ℝ} (m : ℝ)
    (hxp_int : Integrable (fun x => x * p x) volume)
    (hxxp_int : Integrable (fun x => x ^ 2 * p x) volume) :
    ∫ x, x * (p x * (x - m)) =
      (∫ x, x ^ 2 * p x) - m * (∫ x, x * p x) := by
  rw [← integral_const_mul, ← integral_sub]
  · congr
    ext
    ring
  · exact hxxp_int
  · exact hxp_int.const_mul m

lemma variance_eq_of_score_integral
    (p : ℝ → ℝ) (m d : ℝ) {v : ℝ} (hv : v ≠ 0)
    (hxp_int : Integrable (fun x => x * p x) volume)
    (hxxp_int : Integrable (fun x => x ^ 2 * p x) volume)
    (hmean : ∫ x, x * p x = m)
    (hscore : ∫ x, x * (p x * (x - m) / v) = d) :
    (∫ x, x ^ 2 * p x) - (∫ x, x * p x) ^ 2 = v * d := by
  have hs := integral_score_scale p m hv
  rw [hscore, integral_centered_first_moment m hxp_int hxxp_int, hmean] at hs
  rw [hmean, pow_two, hs]

theorem Real.le_sSup_image {g : ℝ → ℝ} {y : ℝ} {S : Set ℝ} (h : y ∈ S)
    (hb : BddAbove (g '' S)) :
    g y ≤ sSup (g '' S) := by
  rw [Real.le_sSup_iff hb ((nonempty_of_mem h).image g)]
  intro ε hε
  use g y
  constructor
  · exact mem_image_of_mem g h
  · linarith

lemma gaussianBound {θ : ℝ} {v : ℝ≥0} (hv : 0 < v.1)
    {a₁ : ℝ} (ha₁ : a₁ ∈ Icc (θ - v.1) (θ + v.1)) (a : ℝ) :
    |gaussianPDFReal a₁ v a| ≤ 1 / √(2 * π * ↑v) * rexp (-(a - θ) ^ 2 / (4 * v.1) + ↑v / 2) := by
  rw [abs_of_nonneg (by exact mul_nonneg (by positivity) (exp_nonneg _))]
  rw [gaussianPDFReal]
  ring_nf
  apply mul_le_mul_of_nonneg_left
  · apply exp_le_exp.mpr
    rw [← NNReal.val_eq_coe]
    nlinarith [sq_nonneg (a - 2 * a₁ + θ),
      mul_inv_cancel_left₀ hv.ne' θ,
      mul_inv_cancel₀ hv.ne', ha₁.1, ha₁.2]
  · positivity

open Set
/-
The supremum, over Gaussian means in a compact interval of radius equal to the
variance parameter, of the indicated weighted Gaussian density is Lebesgue integrable.
-/
theorem integrable_sSup_gaussianPDFReal_weighted
    (θ : ℝ) {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    Integrable (fun x => sSup
        ((fun μ => |gaussianPDFReal μ v x| * |x - μ| / v) ''
          Icc (θ - v) (θ + v))) volume := by
  have h₂ : Integrable (fun a => |a| * exp (-a^2 / (4 * v))) volume := by
    have := @integrable_rpow_mul_exp_neg_mul_sq
    specialize @this (1 / (4 * v)) (by positivity) 1; norm_num at this
    convert this.norm using 2; norm_num
    ring_nf
    norm_num
  have h₁ : Integrable (fun a => (|a| + v) * exp (-a^2 / (4 * v))) volume := by
    simp_all only [NNReal.coe_pos,
        add_mul, integrable_add_iff_integrable_right']
    exact Integrable.const_mul (by simpa [div_eq_inv_mul] using
        (integrable_exp_neg_mul_sq (by positivity))) _
  have h₀ : Integrable (fun a => (|a - θ| + v)
        * exp (-(a - θ)^2 / (4 * v) + v / 2)) volume := by
      convert h₁.comp_sub_right θ |>
        fun h => h.mul_const (exp (v / 2)) using 2
      norm_num [exp_add]
      ring
  -- The supremum of a continuous function over a compact interval is continuous.
  have h_cont : Continuous (fun a => sSup ((fun a₁ =>
    |gaussianPDFReal a₁ v a| * |a - a₁| / v) '' Icc (θ - v) (θ + v))) := by
    apply_rules [IsCompact.continuous_sSup]
    · exact CompactIccSpace.isCompact_Icc
    · unfold gaussianPDFReal
      fun_prop
  -- We need to show that the function is bounded above by an integrable function.
  suffices h_bound : ∀ a, sSup
    ((fun a₁ => |gaussianPDFReal a₁ v a| * |a - a₁| / v) ''
    Icc (θ - v) (θ + v))
    ≤ (1 / √(2 * π * v)) / v * (|a - θ| + v)
    * exp (-(a - θ)^2 / (4 * v) + v / 2) by
    -- The function $(|a - θ| + v) * \exp(-(a - θ)^2 / (4 * v) + v / 2)$ is integrable.
    refine h₀.const_mul (1 / √(2 * π * v) / v) |> fun h => h.mono' ?_ ?_
    · exact h_cont.measurable.aestronglyMeasurable
    · apply ae_of_all
      intro a
      rw [norm_of_nonneg (by
        apply_rules [sSup_nonneg]; rintro x ⟨y, hy, rfl⟩; positivity)]
      simpa only [mul_assoc] using h_bound a
    --   filter_upwards with a using by
    --     rw [norm_of_nonneg (by
    --         apply_rules [sSup_nonneg]; rintro x ⟨y, hy, rfl⟩; positivity)]
    --     simpa only [mul_assoc] using h_bound a
  intro a
  have h_bound (a₁) (ha₁ : a₁ ∈ Icc (θ - v) (θ + v)) :
        |gaussianPDFReal a₁ v a| * |a - a₁| / v
        ≤ (1 / √(2 * π * v)) / v * (|a - θ| + v)
        * exp (-(a - θ)^2 / (4 * v) + v / 2) := by
    have h_bound : |gaussianPDFReal a₁ v a| ≤ (1 / √(2 * π * v))
        * exp (-(a - θ)^2 / (4 * v) + v / 2) := gaussianBound hv ha₁ a
    have h_abs : |a - a₁| ≤ |a - θ| + v := by grind
    have := mul_le_mul h_bound h_abs (by positivity) (by positivity)
    convert mul_le_mul_of_nonneg_right this
        (by positivity : 0 ≤ (v : ℝ) ⁻¹) using 1
    · rfl
    · ring_nf
    · ring_nf
  exact csSup_le (Nonempty.image _ <| nonempty_Icc.mpr <| by linarith)
    <| forall_mem_image.mpr h_bound






open ENNReal
/-- July 18, 2026.
Despite not being absolutely continuous,
the Tweedie measure can be realized as a `withDensity` measure.
-/
lemma tweedieMeasure_eq_integral_tweedieBaseMeasure (μ : ℝ)
    {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2) :
    tweedieMeasure μ hφ (by linarith) hp₂ =
    (tweedieBaseMeasure p ⟨φ,hφ⟩).withDensity (fun y =>
      (exp ((1 / φ) * (tweedie.theta_of_mu p μ * y - tweedie.kappa_of_mu p μ))).toNNReal) := by
  unfold tweedieMeasure tweedieBaseMeasure
    tweediePDF' tweediePDF tweedieProbZero tweedie.theta_of_mu
    tweedie.kappa_of_mu
  rw [withDensity_add_measure]
  rw [← withDensity_mul]
  · refine Measure.ext_iff.mpr ?_
    · intro A hA
      have (a b c d : ℝ≥0∞) (h₀ : a = c) (h₁ : b = d) :
        a + b = c + d := by rw [h₀, h₁]
      apply this
      · simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Measure.coe_toOuterMeasure,
        Pi.smul_apply, Measure.dirac_apply, indicator, Pi.one_apply, smul_ite, ENNReal.smul_one,
        smul_zero, one_div]
        split_ifs with g₀
        · have (f : ℝ → ℝ≥0∞) : (Measure.dirac 0).withDensity f A
          = f 0 := by
            rw [withDensity_apply]
            · rw [← lintegral_indicator]
              · rw [lintegral_dirac]
                exact indicator_of_mem g₀ f
              · exact hA
            · exact hA
          rw [this]
          norm_num
          have (r : ℝ) (hr : 0 ≤ r) (h : r ≠ 0) : r.toNNReal = ⟨r,hr⟩ := by
            refine (toNNReal_eq_iff_eq_coe ?_).mpr rfl
            exact NNReal.coe_ne_zero.mp h
          rw [this]
          · field_simp
          · exact exp_nonneg _
          · simp
        · have (f : ℝ → ℝ≥0∞) (hf : Measurable f) : (Measure.dirac 0).withDensity f A
            = 0 := by
            refine (withDensity_apply_eq_zero hf).mpr ?_
            · simp_all
          rw [this]
          measurability
      · congr
        ext y
        simp only [indicator, mem_setOf_eq, one_div, Pi.mul_apply, ite_mul, zero_mul]
        split_ifs with g₀
        · rw [← coe_mul]
          congr
          · norm_num
            rw [max_eq_left]
            · congr
            · exact tweedie_a_nonneg hφ (by linarith) (by linarith) _ (by linarith)
          · norm_num
            exact exp_nonneg _
        · rfl
  · simp [a]
    measurability
  · measurability



/-- The Tweedie distribution is obtained by
exponentially tilting the Tweedie base (carrier) measure.
-/
lemma tweedieMeasure_eq_integral_tweedieBaseMeasure' {θ : ℝ}
    (hθ : θ < 0)
    {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p < 2) :
    tweedieMeasure (tweedie.mu_of_theta p θ) hφ (by linarith) (by linarith) =
    (tweedieBaseMeasure p ⟨φ,hφ⟩).withDensity (fun y =>
      (exp ((1 / φ) * (θ * y - tweedie.kappa_of_theta p θ))).toNNReal) := by
  unfold tweedie.kappa_of_theta
  rw [tweedie.kappa_of_theta_of_mu]
  · rw [tweedieMeasure_eq_integral_tweedieBaseMeasure]
    · congr
      ext y
      congr
      all_goals rw [tweedie.theta_of_mu_of_theta p hp₁ hθ]
    exact hp₁
  · linarith
  · apply rpow_nonneg
    nlinarith



def exponentialDispersionMeasure (baseMeasure : ℝ → Measure ℝ)
    (kappa : ℝ → ℝ) (φ : ℝ≥0) (θ : ℝ) : Measure ℝ :=
    (baseMeasure φ).withDensity (fun y =>
    (exp ((1 / φ) * (θ * y - kappa θ))).toNNReal)

def exponentialDispersionMeasure' (baseMeasure : ℝ≥0 → Measure ℝ)
    (kappa : ℝ → ℝ) (φ : ℝ≥0) (θ : ℝ) : Measure ℝ :=
    (baseMeasure φ).withDensity (fun y =>
    (exp ((1 / φ) * (θ * y - kappa θ))).toNNReal)

def exponentialDispersionMeasure₁ {Ω : Type*}
    [MeasurableSpace Ω]
    (baseMeasure : Measure Ω)
    (stat : Ω → ℝ)
    (kappa : ℝ → ℝ) (θ : ℝ) : Measure Ω :=
    (baseMeasure).withDensity (fun y =>
    (exp (θ * stat y - kappa θ)).toNNReal)


def poissonBase : Measure ℕ :=
    MeasureTheory.Measure.sum fun (n : ℕ) =>
    ENNReal.ofReal (1 / ↑n.factorial) • MeasureTheory.Measure.dirac n


def poissonEDM (Λ : ℝ≥0) := exponentialDispersionMeasure₁
    poissonBase (fun x => x) (fun θ => exp θ) (log Λ)

/-- Not a mathematical result, but this shows
that our `poissonEDM` model and our
`poissonMeasure` model do not agree at the degenerate
case `Λ=0`. -/
private theorem poisson_as_EDM₀ (n : ℕ)
 : poissonEDM 0 {n} ≠ ProbabilityTheory.poissonMeasure 0 {n} := by
    unfold poissonEDM exponentialDispersionMeasure₁
        poissonMeasure poissonBase
    repeat rw [withDensity_sum]
    simp only [one_div, NNReal.coe_zero, Real.log_zero, zero_mul, exp_zero, zero_sub,
      withDensity_const, Measure.coe_nnreal_smul, MeasurableSpace.measurableSet_top,
      Measure.sum_apply, Measure.smul_apply, Measure.dirac_apply', indicator_singleton, Pi.single,
      Function.update, Pi.one_apply, eq_rec_constant, Pi.zero_apply, dite_eq_ite, smul_eq_mul,
      mul_ite, mul_one, mul_zero, smul_ite, smul_zero, tsum_ite_eq, neg_zero, one_mul, ne_eq]
    by_cases H : n = 0
    · subst n;simp
    simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_div, ofReal_zero, smul_eq_zero,
      toNNReal_eq_zero, ofReal_eq_zero, inv_nonpos, Nat.cast_nonpos, not_or, not_le]
    constructor
    · exact exp_pos (-1)
    · exact Nat.factorial_ne_zero n



def inverseGaussianPDF (μ Λ x : ℝ) : ℝ≥0∞ :=
    (√(Λ / (2 * π * x ^ 3)) * exp (- Λ * (x - μ) ^ 2 / (2 * μ ^ 2 * x))).toNNReal

def levyMeasure (c : ℝ) := volume.withDensity
    fun x => (√(c / (2 * π * x^3))
        * exp (-c / (2 * x))).toNNReal

def tMeasure (v : ℝ) := volume.withDensity (
    fun y => ((Gamma ((v+1) / 2) / √(v * π))
    * (1 + y ^ 2 / v) ^ (- (v + 1) / 2)).toNNReal
)

def inverseGaussianEDM (μ Λ : ℝ≥0) := exponentialDispersionMeasure
    (φ := 1 / Λ) (θ := -1 / (2 * μ ^ 2))
    (kappa := fun θ => - √(-2 * θ))
    (baseMeasure := fun φ => levyMeasure (1 / φ))
/-- Source:
https://chatgpt.com/share/6a6538ef-00d0-83ea-aca5-da5ae20ce5e2
-/
def wright_generalized_bessel (Λ μ : ℝ) (z : ℝ) :=
    ∑' k : ℕ, z ^ k / (Nat.factorial k * Gamma (Λ * k + μ))

lemma notice_something_curious_wright_generalized_bessel
    (Λ : ℝ) (z : ℝ) :
    wright_generalized_bessel Λ 0 z
    =
    ∑' k : ℕ, ite (k=0) 0 (z ^ k / (Nat.factorial k * Gamma (Λ * k)))
    := by
    unfold wright_generalized_bessel
    congr
    ext k
    split_ifs
    · subst k
      simp
    · simp




/-- Tweedie PDF for `2<p<3`. -/
def tweediePDF₂₃ (p μ φ : ℝ)
    (y : ℝ) : ℝ :=
    let α := (2 - p) / (1 - p)
    Set.indicator {y : ℝ | 0 < y} (
    fun y => 1 / y * wright_generalized_bessel (-α) 0 (
        - y^(-α) / ((p - 1) * φ ^ (1 / (p - 1)))
    ) * exp (
        1 / φ * (y * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p) )
    )) y

example (p : ℝ) (hp₂ : 2 < p)
    (hp₃ : p < 3) (μ φ : ℝ)
    (hμ : 0 < μ) (hφ : 0 < φ)
    : ∫ y, tweediePDF₂₃ p μ φ y = 1 := by
    sorry


def gammaEDM := exponentialDispersionMeasure
    (kappa := fun θ => - log (-θ))
    (baseMeasure := fun φ => dite (φ <0) (fun _ => 0) fun h => volume.withDensity (fun x =>
            ofNNReal ⟨
                if x < 0 then 0 else
                (
                x^(1/φ - 1) / (Real.Gamma (1/φ) * (φ^(1/φ)))
            ), by
            split_ifs with g₀
            · simp
            apply mul_nonneg
            · apply rpow_nonneg
              convert g₀;simp
            · simp only [one_div, mul_inv_rev]
              apply mul_nonneg
              · simp only [inv_nonneg]
                apply rpow_nonneg
                convert h;simp
              · simp only [inv_nonneg]
                refine Gamma_nonneg_of_nonneg ?_
                simp only [inv_nonneg]
                convert h;simp⟩))


theorem gamma_eq_EDM.helper (φ : ℝ≥0) (hφ : 0 < φ) (μ : ℝ) (hμ : 0 < μ)
  (g₀_1 : ¬φ.1 < 0)
  ⦃x : ℝ⦄ (hx : x ∈ univ \ {0})
  (g₀ : 0 ≤ x) (g₁ : ¬x < 0) :
  ((φ.1)⁻¹ * μ⁻¹) ^ (φ.1)⁻¹ * x ^ ((1 - φ.1) / φ.1) * rexp (-(x / (μ * φ.1))) * φ.1 ^ (φ.1)⁻¹ =
    x ^ ((1 - φ.1) / φ.1) * (rexp ((φ.1)⁻¹ * (-x / μ)) / μ ^ (φ.1)⁻¹) := by
              have : μ ^ (1 / φ.1) ≠ 0 := by
                simp only [NNReal.val_eq_coe, one_div, ne_eq]
                refine (rpow_ne_zero ?_ ?_).mpr ?_
                all_goals (try simp);linarith
              field_simp
              simp only [one_div, mul_inv_rev]
              have : μ * φ.1 ≠ 0 := by
                simp
                constructor <;> linarith
              have : μ ≠ 0 := by linarith
              set α := (@HPow.hPow ℝ ℝ ℝ instHPow x ((1 - ↑φ) / ↑φ) : ℝ)
              have : x ^ ((1 - φ.1) / φ.1) ≠ 0 := by
                by_cases H : φ.toReal = 1
                · simp at H
                  subst φ;simp
                · refine (rpow_ne_zero g₀ ?_).mpr ?_
                  · simp only [NNReal.val_eq_coe, ne_eq, _root_.div_eq_zero_iff,
                    NNReal.coe_eq_zero, not_or]
                    constructor
                    · contrapose! H
                      linarith
                    · linarith
                  · contrapose! H
                    subst H
                    simp at hx
              have : α ≠ 0 := this
              field_simp
              rw [← mul_rpow]
              · have h₀ : φ.1 ≠ 0 := by simp;linarith
                field_simp
                rw [← mul_rpow]
                · field_simp
                  exact Real.one_rpow (1 / φ.1)
                · positivity
                · linarith
              · simp only [NNReal.val_eq_coe, one_div, mul_inv_rev]
                positivity
              · simp



/-- July 22, 2026 @ OSU
Pitfalls along the way: log(negative values),
scale,rate vs. scale, shape
not true at x=0 but true a.e.
-/
lemma gamma_eq_EDM (φ : ℝ≥0) (hφ : 0 < φ) (μ : ℝ) (hμ : 0 < μ) :
    volume.withDensity (gammaPDF (1 / φ) (1 / (φ * μ))) = -- scale, rate
    gammaEDM φ (-1/μ) := by
  unfold gammaEDM gammaPDF gammaPDFReal exponentialDispersionMeasure
  -- Do not "simp", instead do this:
  have : (fun θ ↦ -Real.log (-θ)) (-1 / μ)
    =  -Real.log (1 / μ) := by ring_nf
  rw [this]
  simp only [one_div, mul_inv_rev, Real.log_inv, neg_neg]
  split_ifs with g₀
  · exfalso; revert g₀; simp
  · rw [← withDensity_mul]
    · apply withDensity_congr_ae
      apply Filter.mem_of_superset (x := Set.univ \ {0})
      · refine mem_ae_iff.mpr ?_
        suffices volume {(0:ℝ)} = 0 by
          convert this
          ext;simp
        simp
      intro x hx
      simp only [Pi.mul_apply, mem_setOf_eq]
      split_ifs with g₀ g₁ g₂
      · linarith
      · have (r : ℝ) (hr : 0 ≤ r) (h : r ≠ 0) : ofNNReal r.toNNReal = some ⟨r,hr⟩ := by
            simp only [some_eq_coe, coe_inj]
            refine (toNNReal_eq_iff_eq_coe ?_).mpr rfl
            convert h
            exact eq_iff_eq_of_cmp_eq_cmp rfl
        rw [this]
        · simp only [some_eq_coe]
          rw [← coe_mul]
          have (r : ℝ) (hr : 0 ≤ r) : ENNReal.ofReal r = ofNNReal ⟨r,hr⟩ := by
            refine (toReal_eq_toReal_iff' ?_ ?_).mp (toReal_ofReal hr) <;> simp
          rw [this]
          · have (r s : NNReal) (h : r = s) : ofNNReal r = ofNNReal s := by rw [h]
            apply this
            have (r s : ℝ≥0) : r * s = ⟨r.1*s.1, by
              simp only [NNReal.val_eq_coe]
              positivity⟩ := by
              exact NNReal.eq rfl
            rw [this]
            apply Subtype.mk.congr_simp
            simp_rw [exp_mul]
            field_simp
            rw [← exp_mul]
            nth_rw 3 [sub_div]
            rw [mul_sub_left_distrib]
            rw [exp_sub]
            rw [mul_comm _ (Real.log _)]
            have : μ / μ = 1 := by field_simp
            rw [← mul_div]
            rw [this]
            simp only [one_div, mul_inv_rev, mul_one]
            rw [mul_comm _ (Real.log _)]
            rw [exp_mul (Real.log _)]
            rw [Real.exp_log]
            · apply gamma_eq_EDM.helper
              all_goals tauto
            tauto
          · positivity
        · exact exp_nonneg _
        · simp
      · simp only [ofReal_zero, zero_eq_mul, coe_eq_zero, toNNReal_eq_zero]
        left;rfl
      · linarith
    · simp only [measurable_coe_nnreal_ennreal_iff]
      refine Measurable.nnreal_mk ?_
      apply Measurable.ite <;> measurability
    · measurability


/-- July 21, 2026 @ ARC insurance workshop. -/
lemma inverseGaussian_eq_EDM (Λ : ℝ≥0)
    {μ : ℝ≥0} (hμ : 0 < μ) :
    volume.withDensity (inverseGaussianPDF μ Λ) =
    inverseGaussianEDM μ Λ := by
  unfold inverseGaussianEDM inverseGaussianPDF
    exponentialDispersionMeasure levyMeasure
  simp only [NNReal.zero_le_coe, sqrt_div, neg_mul, one_div, NNReal.coe_inv,
    div_inv_eq_mul, one_mul, sub_neg_eq_add]
  rw [← withDensity_mul]
  · congr
    ext x
    by_cases H : x = 0
    · subst x
      simp
    simp only [Pi.mul_apply]
    repeat rw [ofNNReal_toNNReal]
    repeat rw [← ofReal_mul]
    · have (r s : ℝ)
            (hr : 0 ≤ r)
            (hs : 0 ≤ s)
            (h : r = s) :
            ENNReal.ofReal r = ENNReal.ofReal s
             := (ofReal_eq_ofReal_iff hr hs).mpr h
      apply this
      · positivity
      · positivity
      · field_simp
        ring_nf
        field_simp
        have : Λ.toReal ≥ 0 := by simp
        generalize Λ.toReal = l at *
        have : μ.toReal ≠ 0 := by
            simp
            linarith
        have : μ.toReal > 0 := by
            simp
            tauto
        generalize μ.toReal = m at *
        generalize x ^ 3 * 2 * π = γ
        rw [sqrt_div]
        · field_simp
          repeat rw [mul_assoc]
          congr
          rw [← exp_add]
          congr
          field_simp
          ring_nf
          field_simp
          ring_nf
          repeat rw [sqrt_sq]
          · field_simp;ring_nf
          · linarith
        · simp
    · positivity
  · measurability
  · measurability


/-- July 19, 2026. Poisson measure as EDM. -/
theorem poisson_as_EDM (Λ : ℝ≥0)
    (hΛ : 0 < Λ) : poissonEDM Λ = ProbabilityTheory.poissonMeasure Λ := by
    unfold poissonEDM exponentialDispersionMeasure₁
        poissonMeasure poissonBase
    repeat rw [withDensity_sum]
    congr
    ext n A hA
    simp only [one_div, MeasurableSpace.measurableSet_top, withDensity_apply, Measure.restrict_smul,
      lintegral_smul_measure, smul_eq_mul, Measure.smul_apply, Measure.dirac_apply', indicator,
      Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [← lintegral_indicator hA]
    simp only [indicator, lintegral_dirac, mul_ite, mul_zero]
    split_ifs with g₀
    · rw [ofNNReal_toNNReal]
      rw [← ENNReal.ofReal_mul]
      · refine (ofReal_eq_ofReal_iff ?_ ?_).mpr ?_
        · positivity
        · positivity
        have : (n.factorial : ℝ) ≠ 0 := by
            simp only [ne_eq, Nat.cast_eq_zero]
            exact Nat.factorial_ne_zero n
        generalize n.factorial = α at *
        field_simp
        have hΛ : 0 < Λ.toReal := by simp;tauto
        rw [Real.exp_log hΛ, exp_sub, exp_neg]
        have : rexp Λ ≠ 0 := by simp
        field_simp
        rw [exp_mul, Real.exp_log hΛ]
        simp
      · simp
    · rfl


-- def poisson := exponentialDispersionMeasure'
--     (fun φ => Measure.count (α := Fin 3))

def exponentialDispersionMeasure'' (baseMeasure : ℝ≥0 → Measure ℝ)
    (kappa : ℝ → ℝ) (θ : ℝ) (φ : ℝ≥0) : Measure ℝ :=
    (baseMeasure φ).withDensity (fun y =>
    (ite (φ = 0) 0 <|exp ((1 / φ) * (θ * y - kappa θ))).toNNReal)

lemma tweedie_eq_exponentialDispersion {θ : ℝ} (hθ : θ < 0)
    {p : ℝ} (φ : NNReal) (hp₁ : 1 < p) (hp₂ : p < 2) :
    tweedieMeasure (tweedie.mu_of_theta p θ) φ.2 (by linarith) (by linarith) =
    exponentialDispersionMeasure'
        (tweedieBaseMeasure p) (tweedie.kappa_of_theta p) φ θ := by
  rw [tweedieMeasure_eq_integral_tweedieBaseMeasure' hθ]
  · rfl
  · exact hp₁
  · exact hp₂

lemma gaussian_eq_exponentialDispersion (v : ℝ≥0)
    (hv : 0 < v) : (fun μ => gaussianReal μ v) =
    exponentialDispersionMeasure' (gaussianReal 0)
    (fun θ => θ ^ 2 / 2) v := by
    ext μ
    unfold exponentialDispersionMeasure' gaussianReal
    split_ifs with g₀
    · subst v
      simp
      -- unsatisfying that we must assume `0 < v` here
      simp at hv
    · simp only [one_div]
      rw [← withDensity_mul]
      · congr
        unfold gaussianPDF gaussianPDFReal
        simp only [NNReal.zero_le_coe, sqrt_mul', Nat.ofNat_nonneg, sqrt_mul, mul_inv_rev, sub_zero]
        ext x
        field_simp
        simp only [Pi.mul_apply]
        norm_cast
        have : 0 ≤ √↑v * √π * √2 := by
            positivity
        generalize √↑v * √π * √2 = α at *
        have : (x - μ)^2 = x^2 - 2*x*μ + μ^2 := sub_sq x μ
        rw [this]
        ring_nf
        rw [mul_comm]
        have (r : ℝ) :
            ofNNReal ((exp r).toNNReal) = ENNReal.ofReal (exp r) := by
            exact ofNNReal_toNNReal (rexp r)
        rw [this]
        repeat rw [← ENNReal.ofReal_mul]
        repeat rw [mul_assoc]
        · rw [← exp_add];congr;ring_nf
        · apply mul_nonneg
          · simp only [inv_nonneg]
            tauto
          · exact exp_nonneg _
      · exact measurable_gaussianPDF 0 v
      · measurability

/-- Unsatisfying companions to `gaussian_eq_exponentialDispersion`. -/
example (μ : ℝ) : exponentialDispersionMeasure' (gaussianReal 0)
    (fun θ => θ^2 / 2) 0 μ = Measure.dirac 0 := by
    unfold exponentialDispersionMeasure'
    simp

example (μ : ℝ) : exponentialDispersionMeasure'' (gaussianReal 0)
    (fun θ => θ^2 / 2) μ 0 = 0 := by
    unfold exponentialDispersionMeasure''
    simp


lemma gaussian_eq_exponentialDispersion'' (μ : ℝ) (v : ℝ≥0)
    (hv : 0 < v) : gaussianReal μ v =
    exponentialDispersionMeasure'' (gaussianReal 0)
    (fun θ => θ ^ 2 / 2) μ v := by
    unfold exponentialDispersionMeasure'' gaussianReal
    split_ifs with g₀
    · subst v
      simp
      -- unsatisfying that we must assume `0 < v` here
      simp at hv
    · simp only [one_div]
      rw [← withDensity_mul]
      · congr
        unfold gaussianPDF gaussianPDFReal
        simp only [NNReal.zero_le_coe, sqrt_mul', Nat.ofNat_nonneg, sqrt_mul, mul_inv_rev, sub_zero]
        ext x
        field_simp
        simp only [Pi.mul_apply]
        norm_cast
        have : 0 ≤ √↑v * √π * √2 := by
            positivity
        generalize √↑v * √π * √2 = α at *
        have : (x - μ)^2 = x^2 - 2*x*μ + μ^2 := sub_sq x μ
        rw [this]
        ring_nf
        rw [mul_comm]
        have (r : ℝ) :
            ofNNReal ((exp r).toNNReal) = ENNReal.ofReal (exp r) := by
            exact ofNNReal_toNNReal (rexp r)
        rw [this]
        repeat rw [← ENNReal.ofReal_mul]
        repeat rw [mul_assoc]
        · rw [← exp_add];congr;ring_nf
        · apply mul_nonneg
          · simp only [inv_nonneg]
            tauto
          · exact exp_nonneg _
      · exact measurable_gaussianPDF 0 v
      · measurability


def tweediePDF'' (p μ φ : ℝ) := indicator ({y | 0 < y})
    fun y => a φ p y * exp ((1 / φ) * ((tweedie.theta_of_mu p μ) * y - (tweedie.kappa_of_mu p μ)))

lemma tweediePDF_eq_tweediePDF'' (μ φ p : ℝ) :
    tweediePDF p μ φ = tweediePDF'' p μ φ := rfl

/-- Rather unimportant proof,
in effect stating that P(T>0)≤ 1 for Tweedie T. -/
theorem tweediePDFbound {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2)
    (v : ℝ≥0) (t : ℝ) (ht : t ∈ Iio 0) :
    ∫ (x : ℝ), tweediePDF p (tweedie.mu_of_theta p t) v x ≤ 1 := by
    by_cases H : v = 0
    · subst v
      simp only [tweediePDF, a, one_div, neg_mul, NNReal.coe_zero, _root_.div_zero, zero_mul,
        exp_zero, mul_one]
      have := @zero_rpow
      -- write the ∑' as 0th term plus rest
      have (y : ℝ) : (fun (j : ℕ) =>
            y ^ (-(↑j * ((2 - p) / (1 - p)))) * (p - 1) ^ ((2 - p) / (1 - p) * ↑j) /
              (0 ^ (↑j * (1 - (2 - p) / (1 - p))) * (2 - p) ^ j * ↑j.factorial
                * Gamma (-(↑j * ((2 - p) / (1 - p))))))
              = (fun j => 0) := by
        ext j
        by_cases g₀ : j = 0
        · subst j; simp
        · have : ((0:ℝ) ^ (↑j * (1 - (2 - p) / (1 - p)))) = 0 :=
                by
                rw [zero_rpow]
                simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
                constructor
                · tauto
                · intro hc
                  have : 1 - p = 2 - p := by
                    have : 1 - p ≠ 0 := by linarith
                    have : 2 - p ≠ 0 := by linarith
                    field_simp at hc
                    simp at hc
                    linarith
                  linarith
          simp_rw [this]
          simp
      simp_rw [this]
      simp
    rw [tweediePDF_integral]
    · have (x : ℝ) : 1 - exp x ≤ 1 := by
        linarith [exp_nonneg x]
      apply this
    · exact hp₁
    · exact hp₂
    · apply rpow_pos_of_pos
      apply mul_pos_of_neg_of_neg ht (by linarith)
    · simp only [NNReal.coe_pos]
      exact zero_lt_iff.mpr H

/-- July 15, 2026. -/
def tweedieEDF (p : ℝ)
    (hp₁ : 1 < p) (hp₂ : p < 2) : ExponentialDispersionFamily
    (fun θ φ => tweediePDF p (tweedie.mu_of_theta p θ) φ) := {
  κ := fun θ => tweedie.kappa_of_mu p (tweedie.mu_of_theta p θ)
  baseDensity := fun φ => {y | 0 < y}.indicator (a φ p)
  Θ := Iio 0
  hΘ := isOpen_Iio
  hnorm := tweediePDFbound hp₁ hp₂
  eq_exp := by
    simp_rw [tweediePDF_eq_tweediePDF'']
    unfold tweediePDF''
    intro θ hθ
    ext φ x
    have (f g : ℝ → ℝ) (A : Set ℝ) :
        A.indicator (fun x => f x * g x) x =
        A.indicator f x * g x := indicator_mul_const A f (g x) x
    rw [this]
    field_simp
    simp_rw [mul_comm x θ]
    congr
    apply tweedie.theta_of_mu_of_theta p hp₁ hθ
}




lemma EDF_integral_deriv_eq_zero {f : ℝ → ℝ≥0 → ℝ → ℝ}
    (E : ExponentialDispersionFamily f)
    (θ : ℝ) (hθ : θ ∈ E.Θ) (v : ℝ≥0) (hA : DifferentiableOn ℝ E.κ E.Θ)
    (hnorm : ∀ t ∈ E.Θ, ∫ x, f t v x = 1)
    (hf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => f t v x) volume)
    (hf_int : Integrable (fun x => f θ v x) volume)
    (s : Set ℝ) (hs : s ∈ nhds θ) (hsΘ : s ⊆ E.Θ)
    (bound : ℝ → ℝ) (bound_int : Integrable bound volume)
    (h_bound : ∀ᵐ x, ∀ t ∈ s,
      ‖f t v x * (x - deriv E.κ t) / (v : ℝ)‖ ≤ bound x) :
    ∫ x, f θ v x * (x - deriv E.κ θ) / (v : ℝ) = 0 := by
      have := @hasDerivAt_integral_of_dominated_loc_of_deriv_le
      specialize @this ℝ _ volume ℝ _ _ _ _ _ bound (fun t x => f t v x) θ s hs
      contrapose! this
      constructor
      · filter_upwards [hs] with t ht using hf_meas t (hsΘ ht)
      constructor
      · exact hf_int
      use fun t x => f t v x * (x - deriv E.κ t) / (v : ℝ)
      constructor
      · measurability
      constructor
      · exact h_bound
      constructor
      · exact bound_int
      constructor
      · filter_upwards [h_bound] with x hx t ht using EDF_hasDerivAt_theta E v hA x
            (hsΘ ht)
      · intro h_integrable h_deriv
        exact this (by simpa using h_deriv.deriv.symm.trans (HasDerivAt.deriv
            (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const _ _) (Filter.eventuallyEq_of_mem
                (E.hΘ.mem_nhds hθ) fun t ht => hnorm t ht))))

/-- The mean of a domain-restricted exponential dispersion model is `A'(θ)`.

The parameter domain is assumed open so that the ordinary derivative agrees with the
within-domain derivative. The domination neighborhood `s` must be contained in `E.Θ`. -/
lemma EDF_mean {f : ℝ → ℝ≥0 → ℝ → ℝ} (E : ExponentialDispersionFamily f)
    (θ : ℝ) (hθ : θ ∈ E.Θ) (v : ℝ≥0) (hv : (0 : ℝ) < v)
    (hA : DifferentiableOn ℝ E.κ E.Θ)
    (hnorm : ∀ t ∈ E.Θ, ∫ x, f t v x = 1)
    (hf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => f t v x) volume)
    (hf_int : Integrable (fun x => f θ v x) volume)
    (hxf_int : Integrable (fun x => x * f θ v x) volume)
    (s : Set ℝ) (hs : s ∈ nhds θ) (hsΘ : s ⊆ E.Θ)
    (bound : ℝ → ℝ) (bound_int : Integrable bound volume)
    (h_bound : ∀ᵐ x, ∀ t ∈ s,
      ‖f t v x * (x - deriv E.κ t) / (v : ℝ)‖ ≤ bound x) :
    ∫ x, x * f θ v x = deriv E.κ θ := by
      have h_integral_deriv : ∫ x, f θ v x * (x - deriv E.κ θ) / (v : ℝ) = 0 := by
        apply EDF_integral_deriv_eq_zero E θ hθ v hA hnorm hf_meas hf_int s hs hsΘ
            bound bound_int h_bound
      simp_all only [NNReal.coe_pos, mul_sub, sub_div, norm_eq_abs]
      rw [integral_sub] at h_integral_deriv
      · simp_all [mul_comm, integral_div, integral_mul_const]
        rw [sub_eq_zero, div_eq_div_iff] at h_integral_deriv <;> aesop
      · convert hxf_int.div_const (v : ℝ) using 2 ; ring
      · exact Integrable.div_const (hf_int.mul_const _) _

lemma EDF_mean_integral_hasDerivAt {f : ℝ → ℝ≥0 → ℝ → ℝ}
    {E : ExponentialDispersionFamily f}
    {θ : ℝ} (_hθ : θ ∈ E.Θ) {v : ℝ≥0} (hA : DifferentiableOn ℝ E.κ E.Θ)
    (hxf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => x * f t v x) volume)
    (hxf_int : Integrable (fun x => x * f θ v x) volume)
    {s : Set ℝ} (hs : s ∈ nhds θ) (hsΘ : s ⊆ E.Θ)
    {bound : ℝ → ℝ} (bound_int : Integrable bound volume)
    (h_bound : ∀ᵐ x, ∀ t ∈ s,
      ‖x * (f t v x * (x - deriv E.κ t) / (v : ℝ))‖ ≤ bound x) :
    HasDerivAt (fun t => ∫ x, x * f t v x)
      (∫ x, x * (f θ v x * (x - deriv E.κ θ) / (v : ℝ))) θ := by
        have := @hasDerivAt_integral_of_dominated_loc_of_deriv_le
        contrapose! this
        use ℝ, inferInstance, volume, ℝ, inferInstance, ℝ
        use inferInstance, inferInstance, inferInstance
        use bound, fun t x => x * f t v x, θ, s, hs
        constructor
        · filter_upwards [hs] with t ht using hxf_meas t (hsΘ ht)
        constructor
        · exact hxf_int
        · use fun t x => x * (f t v x * (x - deriv E.κ t) / v)
          constructor
          · convert hxf_meas θ _hθ |> fun h => h.mul (show AEStronglyMeasurable
                (fun x => (x - deriv E.κ θ) / v) ℙ from ?_) using 1
            · rfl
            · exact funext fun x => by simp [mul_assoc, mul_div_assoc]
            · measurability
          constructor
          · exact h_bound
          use bound_int
          constructor
          · filter_upwards [h_bound] with x hx t ht
            convert HasDerivAt.const_mul x
                (EDF_hasDerivAt_theta E v hA x (hsΘ ht)) using 1
          · exact fun _ => this

lemma EDF_score_integral_eq_second_deriv {f : ℝ → ℝ≥0 → ℝ → ℝ}
    (E : ExponentialDispersionFamily f)
    {θ : ℝ} (hθ : θ ∈ E.Θ)
    (hA : DifferentiableOn ℝ E.κ E.Θ)
    {v : ℝ≥0}
    (hxf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => x * f t v x) volume)
    {s : Set ℝ} (hs_open : IsOpen s) (hθs : θ ∈ s) (hsΘ : s ⊆ E.Θ)
    (hxf_int : ∀ {t}, t ∈ s → Integrable (fun x => x * f t v x) volume)
    (hmean : ∀ t ∈ s, ∫ x, x * f t v x = deriv E.κ t)
    (bound : ℝ → ℝ) (bound_int : Integrable bound volume)
    (h_bound : ∀ᵐ x, ∀ t ∈ s,
      ‖x * (f t v x * (x - deriv E.κ t) / (v : ℝ))‖ ≤ bound x) :
    ∫ x, x * (f θ v x * (x - deriv E.κ θ) / (v : ℝ)) = deriv (deriv E.κ) θ := by
  have := EDF_mean_integral_hasDerivAt hθ hA hxf_meas (hxf_int hθs)
    (IsOpen.mem_nhds hs_open hθs) hsΘ bound_int h_bound
  generalize_proofs at *; (
  rw [← this.deriv, Filter.EventuallyEq.deriv_eq]
  filter_upwards [hs_open.mem_nhds hθs] with t ht using hmean t ht ▸ rfl)

/-- The variance of a domain-restricted exponential dispersion model is `v * A''(θ)`.

As in `EDF_mean`, openness supplies ordinary derivatives at parameters in the
domain, while `s ⊆ E.Θ` ensures all local differentiation hypotheses stay in-domain. -/
lemma EDF_variance {f : ℝ → ℝ≥0 → ℝ → ℝ}
    (E : ExponentialDispersionFamily f)
    {θ : ℝ} (hθ : θ ∈ E.Θ)
    {v : ℝ≥0} (hv : (0 : ℝ) < v)
    (hA : DifferentiableOn ℝ E.κ E.Θ)
    (hnorm : ∀ t ∈ E.Θ, ∫ x, f t v x = 1)
    (hf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => f t v x) volume)
    (hxf_meas : ∀ t ∈ E.Θ, AEStronglyMeasurable (fun x => x * f t v x) volume)
    {s : Set ℝ} (hs_open : IsOpen s) (hθs : θ ∈ s) (hsΘ : s ⊆ E.Θ)
     (hf_int : ∀ t ∈ s, Integrable (fun x => f t v x) volume)
    (hxf_int : ∀ t ∈ s, Integrable (fun x => x * f t v x) volume)
            (hxxf_int : Integrable (fun x => x ^ 2 * f θ v x) volume)
    {bound₁ : ℝ → ℝ} (bound₁_int : Integrable bound₁ volume)
    (h_bound₁ : ∀ᵐ x, ∀ t ∈ s,
      ‖f t v x * (x - deriv E.κ t) / (v : ℝ)‖ ≤ bound₁ x)
    {bound₂ : ℝ → ℝ} (bound₂_int : Integrable bound₂ volume)
    (h_bound₂ : ∀ᵐ x, ∀ t ∈ s,
      ‖x * (f t v x * (x - deriv E.κ t) / (v : ℝ))‖ ≤ bound₂ x) :
    (∫ x, x^2 * f θ v x) - (∫ x, x*f θ v x)^2 = v * deriv (deriv E.κ) θ := by
  -- Apply the lemma EDF_score_integral_eq_second_deriv to get the score integral.
  have h_score_integral : ∫ x, x * (f θ v x * (x - deriv E.κ θ) / (v : ℝ))
  = deriv (deriv E.κ) θ := by
    apply EDF_score_integral_eq_second_deriv
    any_goals assumption
    intro t ht
    apply EDF_mean E t (hsΘ ht) v hv hA hnorm hf_meas (hf_int t ht) (hxf_int t ht) s
      (hs_open.mem_nhds ht) hsΘ bound₁ bound₁_int h_bound₁
  have := variance_eq_of_score_integral (fun x => f θ v x) (deriv E.κ θ)
    (deriv (deriv E.κ) θ) hv.ne' ?_ ?_ ?_ ?_
  · exact this
  · exact hxf_int θ hθs
  · exact hxxf_int
  · apply EDF_mean E θ hθ v hv hA hnorm hf_meas (hf_int θ hθs) (hxf_int θ hθs) s
      (hs_open.mem_nhds hθs) hsΘ bound₁ bound₁_int h_bound₁
  · exact h_score_integral



lemma gaussian_EDF_variance (μ : ℝ) (v : ℝ≥0) (hv : (0 : ℝ) < v) :
    (∫ x, x^2 * gaussianPDFReal μ v x) - (∫ x, x * gaussianPDFReal μ v x)^2
      = v * deriv (deriv gaussianEDF.κ) μ := by
    sorry
    -- apply EDF_variance (s := Ioo (μ-1) (μ+1))
    -- · exact hv
    -- · unfold gaussianEDF
    --   simp
    -- · intro θ'
    --   refine integral_gaussianPDFReal_eq_one θ' ?_
    --   linarith
    -- · measurability
    -- · measurability
    -- · exact isOpen_Ioo
    -- · simp
    -- · intro θ' hθ'
    --   exact integrable_gaussianPDFReal θ' v
    -- · intro θ' hθ'
    --   -- I think we have that somewhere
    --   sorry
    -- · -- definitely true
    --   sorry
    -- · sorry
    -- · -- similar to mean case
    --   sorry
    -- · sorry
    -- · sorry
    -- · sorry
    -- · sorry


lemma gaussian_EDF_mean
    (θ : ℝ) (v : ℝ≥0) (hv : (0 : ℝ) < v) :
    ∫ x, x * ((fun μ v => gaussianPDFReal μ v)) θ v x = deriv gaussianEDF.κ θ := by
  apply EDF_mean gaussianEDF θ (by simp [gaussianEDF]) v hv
  · simp only [gaussianEDF, NNReal.zero_le_coe, sqrt_mul', Nat.ofNat_nonneg, sqrt_mul,
    one_div, mul_inv_rev]
    apply Differentiable.differentiableOn
    simp
  · simp only [gaussianEDF, NNReal.zero_le_coe, sqrt_mul',
        Nat.ofNat_nonneg, sqrt_mul, one_div, mul_inv_rev, mem_univ, forall_const]
    refine fun t => ?_
    refine integral_gaussianPDFReal_eq_one t ?_
    linarith
  · measurability
  · exact integrable_gaussianPDFReal θ v
  · have h₀ : Integrable (fun x => x) (μ := gaussianReal θ v) := by
        exact IsGaussian.integrable_fun_id
    have h₁ : gaussianReal θ v = volume.withDensity (gaussianPDF θ v) := by
        refine gaussianReal_of_var_ne_zero θ ?_
        linarith
    rw [h₁] at h₀
    unfold gaussianPDF at h₀
    clear h₁
    clear hv
    rw [integrable_withDensity_iff] at h₀
    · convert h₀
      · rfl
      refine Eq.symm (ENNReal.toReal_ofReal ?_)
      (expose_names; exact gaussianPDFReal_nonneg θ v x)
    · measurability
    · simp
  · apply _root_.Icc_mem_nhds
    · change θ - v < θ
      linarith
    · change θ < θ + v
      linarith
  rotate_right
  · exact fun a => sSup ((fun θ' => ‖gaussianPDFReal θ' v a
        * (a - deriv gaussianEDF.κ θ') / ↑v‖) ''
        Icc (θ - v) (θ + v))
  · unfold gaussianEDF
    intro;simp
  · simp only [gaussianEDF, NNReal.zero_le_coe, sqrt_mul', Nat.ofNat_nonneg, sqrt_mul,
    one_div, mul_inv_rev, deriv_div_const, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_div_cancel_left₀, norm_div, norm_mul, norm_eq_abs, NNReal.abs_eq]
    exact integrable_sSup_gaussianPDFReal_weighted θ hv
  · apply ae_of_all
    intro a θ' hθ'
    apply Real.le_sSup_image hθ'
    apply IsCompact.bddAbove_image
    · exact ConditionallyCompleteLinearOrder.isCompact_Icc _ _
    · apply Continuous.continuousOn
      unfold gaussianPDFReal gaussianEDF
      continuity













/-- The statement with no assumption on `c` is false: at `c = 0` the density vanishes. -/
theorem levyMeasure_zero : levyMeasure 0 Set.univ = 0 := by
  rw [levyMeasure, withDensity_apply _ MeasurableSet.univ]
  simp
/-- The real integral of the Lévy density is one when its scale parameter is positive. -/
lemma integral_levy_density_eq_one {c : ℝ} (hc : 0 < c) :
    ∫ x : ℝ, √(c / (2 * π * x^3)) * exp (-c / (2 * x)) = 1 := by
  calc ∫ x : ℝ, √(c / (2 * π * x^3)) * exp (-c / (2 * x))
      = ∫ x in Set.Ioi 0, √(c / (2 * π * x^3)) * exp (-c / (2 * x)) := by
        rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        simp only [mem_Ioi, not_lt] at hx
        have hx' : x ≤ 0 := hx
        by_cases hx0 : x = 0
        · simp [hx0]
        · have hx_neg : x < 0 := lt_of_le_of_ne hx' hx0
          have hx3_neg : x ^ 3 < 0 := by
            nlinarith [sq_nonneg x, mul_pos_of_neg_of_neg hx_neg hx_neg]
          have h_arg_neg : c / (2 * Real.pi * x ^ 3) < 0 := by
            have h2pi_pos : 0 < 2 * Real.pi := by positivity
            exact div_neg_of_pos_of_neg hc (by nlinarith)
          rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt h_arg_neg)]
          simp
    _ = 1 := by
      have h_eq : ∀ x : ℝ, x > 0 → √(c / (2 * π * x ^ 3)) * Real.exp (-c / (2 * x)) =
          Real.sqrt (c / (2 * π)) * x ^ (-(3/2 : ℝ)) * Real.exp (-c / (2 * x)) := by
        intro x hx
        rw [show c / (2 * π * x ^ 3) = (c / (2 * π)) * x ^ (-(3:ℝ)) by
          rw [mul_comm, ← div_div]
          rw [Real.rpow_neg (le_of_lt hx)]
          field_simp
          norm_cast]
        rw [Real.sqrt_mul (by positivity : 0 ≤ c / (2 * π)), Real.sqrt_eq_rpow,
            Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx)]
        ring_nf
      -- Use substitution u = 1/x, then integral becomes ∫ u^(-1/2) * exp(-(c/2)*u) du
      -- Apply integral_rpow_mul_exp_neg_mul_rpow with p = -1/2, b = c/2, q = 1
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_eq]
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul]
      -- Now need to evaluate ∫ x^(-3/2) * exp(-c/(2x)) dx
      -- Using substitution u = 1/x, this becomes
      -- ∫ u^(-1/2) * exp(-(c/2)*u) du = Γ(1/2) / (c/2)^(1/2)
      -- Use integral_rpow_mul_exp_neg_mul_rpow with p = -1/2, b = c/2, q = 1
      -- Do substitution u = 1/x, so x = u^(-1), dx = -u^(-2) du
      -- ∫ x^(-3/2) * exp(-c/(2x)) dx = ∫ u^(3/2) * exp(-(c/2)*u)
      -- * u^(-2) du = ∫ u^(-1/2) * exp(-(c/2)*u) du
      have h_sub : ∫ (x : ℝ) in Set.Ioi 0, x ^ (-(3/2 : ℝ)) * Real.exp (-c / (2 * x)) =
          ∫ (u : ℝ) in Set.Ioi 0, u ^ (-(1/2 : ℝ)) * Real.exp (-(c/2) * u) := by
        rw [← MeasureTheory.integral_comp_rpow_Ioi (p := -1) (hp := by norm_num)]
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
        have hx_pos : 0 < x := hx
        have hx_ne : x ≠ 0 := ne_of_gt hx_pos
        rw [Real.rpow_sub_one hx_ne, Real.rpow_neg_one]
        -- Goal: x⁻¹ / x * (x⁻¹ ^ (-(3 / 2)) * rexp (-c / (2 * x⁻¹)))
        -- = x ^ (-(1 / 2)) * rexp (-(c / 2) * x)
        have h1 : x⁻¹ / x = x ^ (-2 : ℝ) := by
          rw [div_eq_mul_inv, inv_eq_one_div, one_div, ← Real.rpow_neg_one, ← Real.rpow_add hx_pos]
          norm_num
        rw [h1]
        have h2 : x⁻¹ ^ (-(3/2 : ℝ)) = x ^ (3/2 : ℝ) := by
          rw [Real.inv_rpow (le_of_lt hx_pos)]
          rw [← Real.rpow_neg (le_of_lt hx_pos)]
          norm_num
        rw [h2]
        -- Now: x^(-2) * (x^(3/2) * exp(-c/(2*x⁻¹))) = x^(-1/2) * exp(-(c/2)*x)
        -- Need to simplify: -c/(2*x⁻¹) = -(c/2)*x and x^(-2) * x^(3/2) = x^(-1/2)
        rw [← mul_assoc, ← Real.rpow_add hx_pos]
        congr 1
        · norm_num
        · field_simp
      rw [h_sub]
      -- Need to match the exact form of integral_rpow_mul_exp_neg_mul_rpow
      -- The lemma has form: ∫ x^p * exp(-b * x^q) = b^(-(p+1)/q) * (1/q) * Γ((p+1)/q)
      -- We have: ∫ u^(-1/2) * exp(-(c/2) * u) = ∫ u^(-1/2) * exp(-(c/2) * u^1)
      have h_u_pow : ∀ u : ℝ, -(c / 2) * u = -(c / 2) * u ^ (1 : ℝ) := by
        intro u; rw [Real.rpow_one]
      rw [funext h_u_pow]
      rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (-1 : ℝ) < -(1/2)) (by linarith : 0 < c/2)]
      -- Goal: √(c / (2 * π)) * ((c / 2) ^ (-(-(1 / 2) + 1) / 1) * (1 / 1)
      -- * Gamma ((-(1 / 2) + 1) / 1)) = 1
      -- Simplify: -(-(1/2) + 1) / 1 = -1/2, (-(1/2) + 1) / 1 = 1/2
      norm_num
      -- Goal: √(c / (2 * π)) * ((c / 2) ^ (-(1/2)) * Gamma (1/2)) = 1
      rw [Real.Gamma_one_half_eq]
      -- Goal: √(c / (2 * π)) * ((c / 2) ^ (-(1/2)) * √π) = 1
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [show (c / (2 * Real.pi)) = (c / 2) / Real.pi by ring]
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [Real.rpow_neg (by positivity : 0 ≤ c / 2)]
      -- Now we have: (c/2)^(1/2) / π^(1/2) * (1 / (c/2)^(1/2)) * π^(1/2) = 1
      field_simp
/-- For a positive scale parameter, the proposed density defines a probability measure. -/
theorem levyMeasure_apply_univ {c : ℝ} (hc : 0 < c) :
    levyMeasure c Set.univ = 1 := by
  let f : ℝ → ℝ := fun x => √(c / (2 * π * x^3)) * exp (-c / (2 * x))
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (sqrt_nonneg _) (exp_pos _).le
  have hfi : Integrable f := by
    by_contra h
    have hz : ∫ x, f x = 0 := integral_undef h
    have ho : ∫ x, f x = 1 := by
      simpa [f] using integral_levy_density_eq_one hc
    linarith
  rw [levyMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change ∫⁻ x : ℝ, ((f x).toNNReal : ℝ≥0∞) = 1
  simp_rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (hf0 _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  rw [show ∫ x, f x = 1 by simpa [f] using integral_levy_density_eq_one hc]
  simp
