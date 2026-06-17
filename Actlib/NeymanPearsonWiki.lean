import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open MeasureTheory

/--
In this file we use the `ρ x θ` convention from Wikipedia.
However, it may be preferable to use `ρ θ x`.
 -/

noncomputable section

/-- The Neyman-Pearson region. -/
def RNP (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) : Set ℝ :=
    { x | ρ x θ₁ - η * ρ x θ₀ ≥ 0}

theorem NP.intRNP₀ {θ₀ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ} (hρ : ∀ (x θ : ℝ), 0 ≤ ρ x θ)
  (hI : Integrable (fun a ↦ ρ a θ₀) volume)
  (hAE : AEStronglyMeasurable (fun a ↦ R.indicator 1 a * ρ a θ₀) volume) :
 Integrable (fun a ↦ R.indicator 1 a * ρ a θ₀) volume
:= by
      apply integrable_of_le_of_le
      exact hAE
      show 0 ≤ᶠ[ae volume] _
      simp [EventuallyLE, Filter.Eventually, ae]
      suffices volume (∅: Set ℝ) = 0 by
        convert this
        ext x
        simp
        apply mul_nonneg
        simp [Set.indicator]
        split_ifs with g₀
        · simp
        · simp
        tauto
      simp
      show _ ≤ᶠ[ae volume] fun a => ρ a θ₀
      simp [EventuallyLE, Filter.Eventually, ae]
      suffices volume (∅: Set ℝ) = 0 by
        convert this
        ext x
        simp [Set.indicator]
        split_ifs with g₀
        · simp
        · tauto

      simp
      refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
      · exact aestronglyMeasurable_zero
      · exact EventuallyLE.refl (ae volume) 0
      · simp
      exact hI

theorem NP.intRNP₁ {θ₁ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ} (hρ : ∀ (x θ : ℝ), 0 ≤ ρ x θ)
  (hI : Integrable (fun a ↦ ρ a θ₁) volume)
  (hAE : AEStronglyMeasurable (fun a ↦ R.indicator 1 a * ρ a θ₁) volume) :
  Integrable (fun a ↦ R.indicator 1 a * ρ a θ₁) volume := by
      apply integrable_of_le_of_le
      exact hAE
      show 0 ≤ᶠ[ae volume] _
      simp [EventuallyLE, Filter.Eventually, ae]
      suffices volume (∅: Set ℝ) = 0 by
        convert this
        ext x
        simp
        apply mul_nonneg
        simp [Set.indicator]
        split_ifs with g₀
        · simp
        · simp
        exact hρ _ _
      simp
      show _ ≤ᶠ[ae volume] fun a => ρ a θ₁
      simp [EventuallyLE, Filter.Eventually, ae]
      suffices volume (∅: Set ℝ) = 0 by
        convert this
        ext x
        simp [Set.indicator]
        split_ifs with g₀
        · simp
        · exact hρ _ _

      simp
      refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
      · exact aestronglyMeasurable_zero
      · exact EventuallyLE.refl (ae volume) 0
      · simp
      exact hI

lemma wiki_arith {η α : ℝ} (hηp : 0 ≤ η)
   {I₁ J₁ I₀ : ℝ} (hα' : I₀ ≤ α)
   (hi : 0 ≤ J₁ - η * α - I₁ + η * I₀) : I₁ ≤ J₁ := by
      suffices 0 ≤ J₁ - I₁ by linarith
      have : 0 ≤ J₁ - I₁ - η * (α - I₀) := by linarith
      apply le_trans this
      have : η * (α - I₀) ≥ 0 := by
        apply mul_nonneg hηp
        linarith
      linarith

lemma wiki (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) (R : Set ℝ) (x : ℝ) :
  ((RNP θ₀ θ₁ η ρ).indicator 1 x - R.indicator 1 x) * (ρ x θ₁ - η * ρ x θ₀) ≥ 0 := by
    simp only [indicator, RNP, ge_iff_le, sub_nonneg, mem_setOf_eq, Pi.one_apply]
    split_ifs with g₀ g₁
    · simp
    · simp only [sub_zero, one_mul, sub_nonneg]
      exact g₀
    · linarith
    · simp

open Classical in
lemma int_help (θ₁ : ℝ) {ρ : ℝ → ℝ → ℝ}
  {R : Set ℝ}
  (hR : MeasurableSet R) :
  ∫ (x : ℝ) in R, ρ x θ₁ = ∫ (x : ℝ), if x ∈ R then ρ x θ₁ else 0 := by
        repeat rw [← integral_indicator]
        simp [Set.indicator]
        exact hR

lemma int_help' (θ₀ η : ℝ) {ρ : ℝ → ℝ → ℝ} {R : Set ℝ} :
  ∫ (a : ℝ), R.indicator 1 a * η * ρ a θ₀
  = η * ∫ (a : ℝ), R.indicator 1 a * ρ a θ₀ := by
    rw [← integral_const_mul]
    congr
    ext a
    ring_nf

/--
May 2, 2026, Palolo pool.
The Neyman-Pearson lemma.
-/
lemma NP (θ₀ θ₁ η α : ℝ) (hηp : 0 ≤ η)
    {ρ : ℝ → ℝ → ℝ} (hρ : ∀ x θ, 0 ≤ ρ x θ)
    (hmm : ∀ θ, Measurable fun x ↦ ρ x θ)
    (hI : ∀ θ, Integrable (fun a ↦ ρ a θ) volume)
    (hα : ∫ x in (RNP θ₀ θ₁ η ρ), ρ x θ₀ = α)
    {R : Set ℝ} (hR : MeasurableSet R)
    (hα' : ∫ x in R, ρ x θ₀ ≤ α) :
    ∫ x in R, ρ x θ₁ ≤ ∫ x in (RNP θ₀ θ₁ η ρ), ρ x θ₁ := by
  have lem (f g : ℝ → ℝ) : (fun a => f a * η * g a)
    =       (fun a => η * f a * g a) := by ext;ring_nf
  have h₁ : AEStronglyMeasurable
        (fun a ↦ R.indicator (fun _ => (1 : ℝ)) a) volume :=
    AEStronglyMeasurable.indicator aestronglyMeasurable_const hR
  have hm : MeasurableSet (RNP θ₀ θ₁ η ρ) := by
    simp only [RNP, ge_iff_le, sub_nonneg, measurableSet_setOf]
    refine ((hmm _).const_mul _).le' (hmm _)
  have h₀ : AEStronglyMeasurable (fun a : ℝ ↦ (RNP θ₀ θ₁ η ρ).indicator (fun _ => (1:ℝ)) a) volume := by
    simp only [RNP, ge_iff_le, sub_nonneg]
    refine aestronglyMeasurable_const.indicator <| measurableSet_le (measurable_const.mul (hmm _)) (hmm _)
  have hi : ∫ x, (Set.indicator (RNP θ₀ θ₁ η ρ) 1 x - Set.indicator R 1 x)
    * (ρ x θ₁ - η * ρ x θ₀) ≥ 0 := integral_nonneg (wiki _ _ _ _ _)
  ring_nf at hi
  have hAE (θ : ℝ) := h₀.mul (hI θ).aestronglyMeasurable
  have hAER (θ : ℝ) := h₁.mul (hI θ).aestronglyMeasurable
  have hI'' : Integrable (fun a ↦ R.indicator 1 a * ρ a θ₀) volume :=
    NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₀' : Integrable (fun a ↦ R.indicator 1 a * ρ a θ₁) volume :=
    NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₁ : Integrable (fun x ↦ (RNP θ₀ θ₁ η ρ).indicator 1 x * ρ x θ₀) volume :=
    NP.intRNP₀ hρ (hI _) <| hAE _
  have hI₁' : Integrable (fun a ↦ (RNP θ₀ θ₁ η ρ).indicator 1 a * ρ a θ₁) volume := by
    apply NP.intRNP₀ hρ (hI _) <| h₀.mul (hI _).aestronglyMeasurable
  rw [integral_add] at hi
  · repeat rw [integral_sub] at hi
    · repeat rw [int_help'] at hi
      rw [← integral_indicator] at hα
      simp [Set.indicator] at hα hi
      rw [hα] at hi
      repeat rw [← int_help] at hi
      apply wiki_arith hηp hα' hi
      all_goals
        try exact hR
        try exact hm
    · apply NP.intRNP₁ hρ (hI _) <| hAE _
    · rw [lem]
      simp_rw [mul_assoc]
      apply MeasureTheory.Integrable.const_mul'
      apply NP.intRNP₀ hρ (hI _) <| hAE _
    · refine (integrable_add_iff_integrable_left' ?_).mpr ?_
      · simp
        rw [lem]
        simp_rw [mul_assoc]
        apply MeasureTheory.Integrable.const_mul'
        exact NP.intRNP₁ hρ (hI _) <| hAE _
      · exact hI₁'
    · exact hI₀'
  · repeat apply Integrable.sub
    · exact NP.intRNP₁ hρ (hI _) <| hAE _
    · rw [lem]
      simp_rw [mul_assoc]
      apply MeasureTheory.Integrable.const_mul'
        <| NP.intRNP₁ hρ (hI _) <| hAE _
    · exact NP.intRNP₁ hρ (hI _) <| hAER _
  · rw [lem]
    simp_rw [mul_assoc]
    apply MeasureTheory.Integrable.const_mul' hI''

def μ : ℝ → Measure ℝ := sorry
def ρ (θ : ℝ) := (μ θ).rnDeriv volume

def RNPnn (θ₀ θ₁ : ℝ) (η : ℝ≥0∞) (ρ : ℝ≥0∞ → ℝ → ℝ≥0∞) : Set ℝ≥0∞ :=
    { x | ρ x θ₁ - η * ρ x θ₀ ≥ 0}

lemma NPnn (θ₀ θ₁ η α : ℝ) (hηp : 0 ≤ η)
    {ρ : ℝ → ℝ → ℝ≥0∞} (hρ : ∀ x θ, 0 ≤ ρ x θ)
    (hmm : ∀ θ, Measurable fun x ↦ ρ x θ)
    (hI : ∀ θ, Integrable (fun a ↦ ρ a θ) volume)
    : 0 = 0 := by sorry
--     (hα : ∫ x in (RNPnn θ₀ θ₁ η ρ), ρ x θ₀ = α)
--     {R : Set ℝ} (hR : MeasurableSet R)
--     (hα' : ∫ x in R, ρ x θ₀ ≤ α) :
--     ∫ x in R, ρ x θ₁ ≤ ∫ x in (RNP θ₀ θ₁ η ρ), ρ x θ₁ := by
--   have lem (f g : ℝ → ℝ) : (fun a => f a * η * g a)
--     =       (fun a => η * f a * g a) := by ext;ring_nf
--   have h₁ : AEStronglyMeasurable
--         (fun a ↦ R.indicator (fun _ => (1 : ℝ)) a) volume :=
--     AEStronglyMeasurable.indicator aestronglyMeasurable_const hR
--   have hm : MeasurableSet (RNP θ₀ θ₁ η ρ) := by
--     simp only [RNP, ge_iff_le, sub_nonneg, measurableSet_setOf]
--     refine ((hmm _).const_mul _).le' (hmm _)
--   have h₀ : AEStronglyMeasurable (fun a : ℝ ↦ (RNP θ₀ θ₁ η ρ).indicator (fun _ => (1:ℝ)) a) volume := by
--     simp only [RNP, ge_iff_le, sub_nonneg]
--     refine aestronglyMeasurable_const.indicator <| measurableSet_le (measurable_const.mul (hmm _)) (hmm _)
--   have hi : ∫ x, (Set.indicator (RNP θ₀ θ₁ η ρ) 1 x - Set.indicator R 1 x)
--     * (ρ x θ₁ - η * ρ x θ₀) ≥ 0 := integral_nonneg (wiki _ _ _ _ _)
--   ring_nf at hi
--   have hAE (θ : ℝ) := h₀.mul (hI θ).aestronglyMeasurable
--   have hAER (θ : ℝ) := h₁.mul (hI θ).aestronglyMeasurable
--   have hI'' : Integrable (fun a ↦ R.indicator 1 a * ρ a θ₀) volume :=
--     NP.intRNP₀ hρ (hI _) <| hAER _
--   have hI₀' : Integrable (fun a ↦ R.indicator 1 a * ρ a θ₁) volume :=
--     NP.intRNP₀ hρ (hI _) <| hAER _
--   have hI₁ : Integrable (fun x ↦ (RNP θ₀ θ₁ η ρ).indicator 1 x * ρ x θ₀) volume :=
--     NP.intRNP₀ hρ (hI _) <| hAE _
--   have hI₁' : Integrable (fun a ↦ (RNP θ₀ θ₁ η ρ).indicator 1 a * ρ a θ₁) volume := by
--     apply NP.intRNP₀ hρ (hI _) <| h₀.mul (hI _).aestronglyMeasurable
--   rw [integral_add] at hi
--   · repeat rw [integral_sub] at hi
--     · repeat rw [int_help'] at hi
--       rw [← integral_indicator] at hα
--       simp [Set.indicator] at hα hi
--       rw [hα] at hi
--       repeat rw [← int_help] at hi
--       apply wiki_arith hηp hα' hi
--       all_goals
--         try exact hR
--         try exact hm
--     · apply NP.intRNP₁ hρ (hI _) <| hAE _
--     · rw [lem]
--       simp_rw [mul_assoc]
--       apply MeasureTheory.Integrable.const_mul'
--       apply NP.intRNP₀ hρ (hI _) <| hAE _
--     · refine (integrable_add_iff_integrable_left' ?_).mpr ?_
--       · simp
--         rw [lem]
--         simp_rw [mul_assoc]
--         apply MeasureTheory.Integrable.const_mul'
--         exact NP.intRNP₁ hρ (hI _) <| hAE _
--       · exact hI₁'
--     · exact hI₀'
--   · repeat apply Integrable.sub
--     · exact NP.intRNP₁ hρ (hI _) <| hAE _
--     · rw [lem]
--       simp_rw [mul_assoc]
--       apply MeasureTheory.Integrable.const_mul'
--         <| NP.intRNP₁ hρ (hI _) <| hAE _
--     · exact NP.intRNP₁ hρ (hI _) <| hAER _
--   · rw [lem]
--     simp_rw [mul_assoc]
--     apply MeasureTheory.Integrable.const_mul' hI''
