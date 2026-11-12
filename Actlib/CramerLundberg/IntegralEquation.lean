import Actlib.CramerLundberg.Convolution
import Actlib.CramerLundberg.Invariant
import Actlib.CramerLundberg.Kernel
import Actlib.CramerLundberg.Regularity
import Actlib.CramerLundberg.Tail

/-!
# The renewal form of the Cramér–Lundberg integral equation

Writing the claim-size convolution as a weighted primitive and the first-arrival
integral as a weighted tail gives two first-order derivative identities. Their
difference is constant, and the limit at infinity determines that constant.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace CramerLundberg

lemma renewal_equation_of_continuous
    {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c)
    (hcont : Continuous φ) (hlim : Tendsto φ atTop (𝓝 1))
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ∀ u ≥ 0, φ u = 1 - α / (β * c) + α / c *
      ∫ x in Icc 0 u, φ (u - x) * (1 - cdf (expMeasure β) x) := by
  let a : ℝ := α / c
  let F : ℝ → ℝ := expConvolution β φ
  let G : ℝ → ℝ := fun u => β * F u
  have ha : 0 < a := div_pos hα hc
  have hFc : Continuous F := continuous_expConvolution β hcont
  have hFlim : Tendsto F atTop (𝓝 (1 / β)) :=
    tendsto_expConvolution hβ hcont hlim
      (bounded_Ici_of_continuousOn_tendsto hcont.continuousOn hlim)
  have hGc : Continuous G := continuous_const.mul hFc
  have hGlim : Tendsto G atTop (𝓝 1) := by
    convert hFlim.const_mul β using 1
    field_simp
  obtain ⟨M, hM⟩ := bounded_Ici_of_continuousOn_tendsto hGc.continuousOn hGlim
  have hGi : IntegrableOn (fun v => exp (-a * v) * G v) (Ioi 0) :=
    integrableOn_exp_mul_of_bounded ha hGc.continuousOn hM
  have htail : ∀ u ≥ 0, φ u = a * expTail a G u :=
    eq_expTail_of_integralEquation hc heq
  have hdφ (u : ℝ) (hu : 0 < u) :
      HasDerivAt φ (a * φ u - a * β * F u) u := by
    have hd := (hasDerivAt_expTail hGi hGc.continuousOn hu).const_mul a
    have hd' := hd.congr_of_eventuallyEq (show φ =ᶠ[𝓝 u]
        (fun v => a * expTail a G v) from by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact htail v hv.le)
    apply hd'.congr_deriv
    rw [htail u hu.le]
    dsimp [G]
    ring
  have hdH (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun v => φ v - a * F v) 0 u := by
    apply ((hdφ u hu).sub
      ((hasDerivAt_expConvolution β hcont u).const_mul a)).congr_deriv
    dsimp [F]
    ring
  have hH : ∀ u ≥ 0, φ u - a * F u = 1 - a * (1 / β) :=
    eq_of_hasDerivAt_zero_of_tendsto
      (hcont.sub (continuous_const.mul hFc)).continuousOn hdH
      (hlim.sub (hFlim.const_mul a))
  intro u hu
  rw [integral_exponential_tail_eq β u φ hβ,
    ← expConvolution_eq_setIntegral β φ hu]
  have huH := hH u hu
  have hratio : a * (1 / β) = α / (β * c) := by
    dsimp [a]
    ring
  rw [hratio] at huH
  change φ u = 1 - α / (β * c) + a * F u
  linarith

/-- Continuity is needed only on the nonnegative half-line: values at negative
capital can be replaced by the value at zero before applying the calculus proof. -/
lemma renewal_equation_of_continuousOn
    {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c)
    (hcont : ContinuousOn φ (Ici 0)) (hlim : Tendsto φ atTop (𝓝 1))
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ∀ u ≥ 0, φ u = 1 - α / (β * c) + α / c *
      ∫ x in Icc 0 u, φ (u - x) * (1 - cdf (expMeasure β) x) := by
  let ψ : ℝ → ℝ := fun u => φ (max u 0)
  have hψ (u : ℝ) (hu : 0 ≤ u) : ψ u = φ u := by simp [ψ, max_eq_left hu]
  have hψcont : Continuous ψ :=
    hcont.comp_continuous (continuous_id.max continuous_const) (fun u => le_max_right u 0)
  have hψlim : Tendsto ψ atTop (𝓝 1) := hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact (hψ u hu).symm)
  have hψeq : ∀ u ≥ 0, ψ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), ψ (u + c * t - x) * exponentialPDFReal β x := by
    intro u hu
    rw [hψ u hu, heq u hu]
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    dsimp only
    rw [hψ _ (sub_nonneg.mpr hx)]
  intro u hu
  have h := renewal_equation_of_continuous hα hβ hc hψcont hψlim hψeq u hu
  rw [hψ u hu] at h
  convert h using 2
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  rw [hψ _ (sub_nonneg.mpr hx.2)]

/-- The original equation and its normalization at infinity already imply all
the regularity needed for the renewal identity. -/
lemma renewal_equation
    {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c)
    (hlim : Tendsto φ atTop (𝓝 1))
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ∀ u ≥ 0, φ u = 1 - α / (β * c) + α / c *
      ∫ x in Icc 0 u, φ (u - x) * (1 - cdf (expMeasure β) x) := by
  exact renewal_equation_of_continuousOn hα hβ hc
    (continuousOn_of_integralEquation hc hlim heq) hlim heq

end CramerLundberg
