import Mathlib.Probability.Distributions.Exponential

/-!
# The exponential density and its convolution kernel

The exponential density vanishes on negative inputs, so the inner integral in the
Cramér–Lundberg equation is a compact-interval convolution.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace CramerLundberg

lemma integral_exponentialPDFReal_Iic_eq (β u : ℝ) (φ : ℝ → ℝ) :
    (∫ x in Iic u, φ (u - x) * exponentialPDFReal β x) =
      β * ∫ x in Icc 0 u, φ (u - x) * exp (-β * x) := by
  have hfun : (fun x => φ (u - x) * exponentialPDFReal β x) =
      (Ici 0).indicator (fun x => β * (φ (u - x) * exp (-β * x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDFReal, gammaPDFReal, hx, mul_comm, mul_left_comm]
    · simp [exponentialPDFReal, gammaPDFReal, hx]
  rw [hfun, setIntegral_indicator measurableSet_Ici, Iic_inter_Ici, integral_const_mul]

lemma integral_exponential_tail_eq (β u : ℝ) (φ : ℝ → ℝ) (hβ : 0 < β) :
    (∫ x in Icc 0 u, φ (u - x) * (1 - cdf (expMeasure β) x)) =
      ∫ x in Icc 0 u, φ (u - x) * exp (-β * x) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [cdf_expMeasure_eq hβ, hx.1, neg_mul]

end CramerLundberg
