import Actlib.CramerLundberg.Convolution
import Actlib.CramerLundberg.Kernel
import Actlib.CramerLundberg.Tail

/-!
# Regularity forced by the Cramér–Lundberg integral equation

The equation and its nonzero limit rule out the nonintegrable branch of Lean's
totalized integral.  This first makes the claim-size convolution continuous;
the weighted tail representation then makes the solution itself continuous.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace CramerLundberg

/-- The weighted-tail form follows by change of variables, without any
regularity assumption on the solution. -/
lemma eq_expTail_of_integralEquation
    {α β c : ℝ} {φ : ℝ → ℝ} (hc : 0 < c)
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ∀ u ≥ 0, φ u = (α / c) *
      expTail (α / c) (fun v => β * expConvolution β φ v) u := by
  intro u hu
  rw [heq u hu, ← integral_exponentialPDFReal_mul_eq_expTail α u hc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : 0 ≤ t
  · congr 1
    rw [integral_exponentialPDFReal_Iic_eq,
      ← expConvolution_eq_setIntegral β φ (show 0 ≤ u + c * t by positivity)]
  · have hz : exponentialPDFReal α t = 0 := by
      simp [exponentialPDFReal, gammaPDFReal, ht]
    simp [hz]

/-- A nonzero limit and the integral equation force local integrability of the
exponentially weighted solution on the nonnegative half-line. -/
lemma intervalIntegrable_of_integralEquation
    {α β c : ℝ} {φ : ℝ → ℝ} (hc : 0 < c)
    (hlim : Tendsto φ atTop (𝓝 1))
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ∀ R ≥ 0, IntervalIntegrable (fun y => exp (β * y) * φ y) volume 0 R := by
  have htail := eq_expTail_of_integralEquation hc heq
  have hnz : ∀ᶠ u in atTop, φ u ≠ 0 :=
    hlim.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  intro R hR
  by_contra hbad
  have hzero (s : ℝ) (hs : R ≤ s) : expConvolution β φ s = 0 := by
    have hbadS : ¬ IntervalIntegrable (fun y => exp (β * y) * φ y) volume 0 s := by
      intro hint
      apply hbad
      apply hint.mono_set
      rw [uIcc_of_le hR, uIcc_of_le (hR.trans hs)]
      exact Icc_subset_Icc le_rfl hs
    simp [expConvolution, intervalIntegral.integral_undef hbadS]
  obtain ⟨u, hnu, hu⟩ := (hnz.and (eventually_ge_atTop R)).exists
  apply hnu
  rw [htail u (hR.trans hu)]
  have hint : (∫ v in Ioi u, exp (-(α / c) * v) *
      (β * expConvolution β φ v)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hzero v (hu.trans hv.le)]
    simp
  unfold expTail
  rw [hint, mul_zero, mul_zero]

/-- Continuity is a consequence of the original integral equation and its
limit at infinity.  No positivity of the solution or measurability assumption
is required. -/
lemma continuousOn_of_integralEquation
    {α β c : ℝ} {φ : ℝ → ℝ} (hc : 0 < c)
    (hlim : Tendsto φ atTop (𝓝 1))
    (heq : ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t *
      ∫ x in Iic (u + c * t), φ (u + c * t - x) * exponentialPDFReal β x) :
    ContinuousOn φ (Ici 0) := by
  let a : ℝ := α / c
  let G : ℝ → ℝ := fun v => β * expConvolution β φ v
  have htail : ∀ u ≥ 0, φ u = a * expTail a G u :=
    eq_expTail_of_integralEquation hc heq
  have hGc : ContinuousOn G (Ici 0) :=
    continuousOn_const.mul (continuousOn_expConvolution_of_intervalIntegrable β φ
      (intervalIntegrable_of_integralEquation hc hlim heq))
  have hfc : ContinuousOn (fun v => exp (-a * v) * G v) (Ici 0) :=
    (by fun_prop : Continuous (fun v : ℝ => exp (-a * v))).continuousOn.mul hGc
  have hnz : ∀ᶠ u in atTop, φ u ≠ 0 :=
    hlim.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  obtain ⟨u, hu, hnu⟩ := ((eventually_gt_atTop (0 : ℝ)).and hnz).exists
  have hinz : (∫ v in Ioi u, exp (-a * v) * G v) ≠ 0 := by
    intro hz
    apply hnu
    have h := htail u hu.le
    dsimp only [expTail] at h
    rw [hz, mul_zero, mul_zero] at h
    exact h
  have hitail : IntegrableOn (fun v => exp (-a * v) * G v) (Ioi u) :=
    Integrable.of_integral_ne_zero hinz
  have hiprefix : IntegrableOn (fun v => exp (-a * v) * G v) (Ioc 0 u) :=
    ((hfc.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi : IntegrableOn (fun v => exp (-a * v) * G v) (Ioi 0) := by
    simpa only [Ioc_union_Ioi_eq_Ioi hu.le] using hiprefix.union hitail
  have hcont : ContinuousOn (fun u => a * expTail a G u) (Ici 0) :=
    continuousOn_const.mul (continuousOn_expTail hi)
  exact hcont.congr (fun u hu => htail u hu)

end CramerLundberg
