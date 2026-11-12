import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Exponential

/-!
# Exponentially weighted tail integrals

The first-arrival integral in the Cramér–Lundberg equation is an exponential
multiple of a tail integral.  Its derivative follows from the ordinary
fundamental theorem of calculus after splitting the tail at a fixed endpoint.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped Topology

namespace CramerLundberg

/-- The exponentially weighted tail of a function. -/
def expTail (a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  exp (a * u) * ∫ v in Ioi u, exp (-a * v) * f v

/-- The ordinary FTC, applied to a tail integral on the positive half-line. -/
lemma hasDerivAt_integral_Ioi_of_pos {f : ℝ → ℝ} {u : ℝ}
    (hf : IntegrableOn f (Ioi 0)) (hu : 0 < u) (hcont : ContinuousAt f u) :
    HasDerivAt (fun b ↦ ∫ v in Ioi b, f v) (-f u) u := by
  have hint : IntervalIntegrable f volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu.le).2
      (hf.mono_set Ioc_subset_Ioi_self)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 u) :=
    ⟨Ioi 0, Ioi_mem_nhds hu, hf.aestronglyMeasurable⟩
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  apply (hderiv.const_sub (∫ v in Ioi 0, f v)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with b hb
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hf (le_of_lt hb)
  linarith

lemma continuousOn_expTail {a : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun v ↦ exp (-a * v) * f v) (Ioi 0)) :
    ContinuousOn (expTail a f) (Ici 0) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    hf.continuousOn_Ici_primitive_Ioi

/-- Differentiating an exponentially weighted tail only requires the FTC and
the product rule. -/
lemma hasDerivAt_expTail {a u : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun v ↦ exp (-a * v) * f v) (Ioi 0))
    (hcont : ContinuousOn f (Ici 0)) (hu : 0 < u) :
    HasDerivAt (expTail a f) (a * expTail a f u - f u) u := by
  have hgcont : ContinuousAt (fun v ↦ exp (-a * v) * f v) u :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).mul
      (hcont.continuousAt (Ici_mem_nhds hu))
  have htail := hasDerivAt_integral_Ioi_of_pos hf hu hgcont
  have hexp := ((hasDerivAt_id u).const_mul a).exp
  have hcancel : exp (a * u) * exp (-a * u) = 1 := by
    rw [← Real.exp_add]
    simp
  apply (hexp.mul htail).congr_deriv
  dsimp only [expTail, id]
  rw [mul_neg, ← mul_assoc (exp (a * u)) (exp (-a * u)) (f u), hcancel, one_mul]
  ring

/-- Bounded continuous functions admit the exponentially weighted tail for
every positive exponential rate. -/
lemma integrableOn_exp_mul_of_bounded {a M : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a) (hcont : ContinuousOn f (Ici 0))
    (hbound : ∀ u ≥ 0, ‖f u‖ ≤ M) :
    IntegrableOn (fun v ↦ exp (-a * v) * f v) (Ioi 0) := by
  have hg : ContinuousOn (fun v ↦ exp (-a * v) * f v) (Ioi 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hcont.mono Ioi_subset_Ici_self)
  refine ((exp_neg_integrableOn_Ioi 0 ha).mul_const M).mono'
    (hg.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hbound v (le_of_lt hv)) (Real.exp_pos _).le

/-- Translation of a Lebesgue integral over a positive half-line. -/
lemma integral_Ioi_zero_comp_add (g : ℝ → ℝ) (u : ℝ) :
    (∫ x in Ioi 0, g (u + x)) = ∫ v in Ioi u, g v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_left_eq_self ((Ioi u).indicator g) u]
  congr 1
  ext x
  simp [Set.indicator_apply, lt_add_iff_pos_right]

/-- Positive affine change of variables for a half-line integral. -/
lemma integral_Ioi_zero_comp_affine (g : ℝ → ℝ) (u : ℝ) {c : ℝ}
    (hc : 0 < c) :
    (∫ t in Ioi 0, g (u + c * t)) = c⁻¹ * ∫ v in Ioi u, g v := by
  simpa only [mul_zero, smul_eq_mul, integral_Ioi_zero_comp_add] using
    (integral_comp_mul_left_Ioi (fun x ↦ g (u + x)) 0 hc)

/-- Rewriting the first-arrival integral as an exponential tail.  No
regularity hypothesis on `f` is needed for this change of variables. -/
lemma integral_exponentialPDFReal_mul_eq_expTail (α u : ℝ) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ) :
    (∫ t, exponentialPDFReal α t * f (u + c * t)) =
      (α / c) * expTail (α / c) f u := by
  have hpdf : (fun t ↦ exponentialPDFReal α t * f (u + c * t)) =
      (Ici 0).indicator (fun t ↦ α * exp (-α * t) * f (u + c * t)) := by
    ext t
    simp only [exponentialPDFReal, gammaPDFReal, Real.rpow_one, Real.Gamma_one,
      div_one, sub_self, Real.rpow_zero, mul_one, Set.indicator_apply, Set.mem_Ici]
    split_ifs <;> simp [neg_mul]
  rw [hpdf, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hexp (t : ℝ) :
      exp (-α * t) = exp ((α / c) * u) * exp (-(α / c) * (u + c * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    (∫ t in Ioi 0, α * exp (-α * t) * f (u + c * t)) =
        (α * exp ((α / c) * u)) *
          ∫ t in Ioi 0, exp (-(α / c) * (u + c * t)) * f (u + c * t) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [hexp]
      ring
    _ = (α * exp ((α / c) * u)) *
        (c⁻¹ * ∫ v in Ioi u, exp (-(α / c) * v) * f v) := by
      congr 1
      exact integral_Ioi_zero_comp_affine (fun v ↦ exp (-(α / c) * v) * f v) u hc
    _ = (α / c) * expTail (α / c) f u := by
      dsimp [expTail]
      ring

end CramerLundberg
