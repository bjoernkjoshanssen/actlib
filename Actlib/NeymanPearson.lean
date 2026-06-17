import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open MeasureTheory

/-! In this file we use the `ρ θ x` convention
and `ℝ≥0∞`.

 -/

noncomputable section

def μ : ℝ → Measure ℝ := sorry
def ρ (θ : ℝ) := (μ θ).rnDeriv volume

def RNPnn (θ₀ θ₁ : ℝ) (η : ℝ≥0∞) (ρ : ℝ → ℝ → ℝ≥0∞) : Set ℝ :=
    { x | ρ θ₁ x - η * ρ θ₀ x ≥ 0}


/-- The Neyman-Pearson region. -/
def RNP (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) : Set ℝ :=
    { x | ρ θ₁ x - η * ρ θ₀ x ≥ 0}

theorem NP.intRNP₀ {θ₀ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ≥0∞}
    (hρ : 0 ≤ ρ)
  (hI : Integrable (ρ θ₀) volume)
  (hAE : AEStronglyMeasurable (R.indicator (fun _ => 1) * ρ θ₀) volume) :
 Integrable (fun a => R.indicator 1 a * ρ θ₀ a) volume
:= by
      sorry

theorem NP.intRNP₁ {θ₁ : ℝ} {R : Set ℝ} {ρ : ℝ → ℝ → ℝ≥0∞}
    (hρ : 0 ≤ ρ)
  (hI : Integrable (ρ θ₁) volume)
  (hAE : AEStronglyMeasurable (R.indicator 1 * ρ θ₁) volume) :
  Integrable (R.indicator 1 * ρ θ₁) volume := by
      apply NP.intRNP₀ hρ hI hAE

/-- A basic arithmetic lemma that is used in
Wikipedia's proof of Neyman--Pearson. -/
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

/-- The basic inequality that gets Wikipedia's proof of N--P
off the ground. -/
lemma wiki (θ₀ θ₁ η : ℝ) (ρ : ℝ → ℝ → ℝ) (R : Set ℝ) (x : ℝ) :
  ((RNP θ₀ θ₁ η ρ).indicator 1 x - R.indicator 1 x) * (ρ θ₁ x - η * ρ θ₀ x) ≥ 0 := by
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
  ∫ (x : ℝ) in R, ρ θ₁ x = ∫ (x : ℝ), if x ∈ R then ρ θ₁ x else 0 := by
        repeat rw [← integral_indicator]
        simp [Set.indicator]
        exact hR

lemma int_help' (θ₀ η : ℝ) {ρ : ℝ → ℝ → ℝ} {R : Set ℝ} :
  ∫ (a : ℝ), R.indicator 1 a * η * ρ θ₀ a
  = η * ∫ (a : ℝ), R.indicator 1 a * ρ θ₀ a := by
    rw [← integral_const_mul]
    congr
    ext a
    ring_nf


/--
May 2, 2026, Palolo pool.
The Neyman-Pearson lemma.
-/
lemma NP (θ₀ θ₁ : ℝ) (η α : ℝ≥0∞) (hηp : 0 ≤ η)
    {ρ : ℝ → ℝ → ℝ≥0∞} (hρ : 0 ≤ ρ)
    (hmm : ∀ θ, Measurable (ρ θ))
    (hmm' :  AEMeasurable (ρ θ₀) volume)
    (hmm'' : AEMeasurable ((RNPnn θ₀ θ₁ η ρ).indicator fun _ => (1:ℝ≥0∞)) volume)
    (hI : ∀ θ, Integrable (ρ θ) volume)
    (hα : ∫⁻ x in (RNPnn θ₀ θ₁ η ρ), ρ θ₀ x = α)
    {R : Set ℝ} (hR : MeasurableSet R)
    (hmR : AEMeasurable (R.indicator fun x ↦ (1:ℝ≥0∞)) volume)
    (hα' : ∫⁻ x in R, ρ θ₀ x ≤ α) :
    ∫⁻ x in R, ρ θ₁ x ≤ ∫⁻ x in (RNPnn θ₀ θ₁ η ρ), ρ θ₁ x := by
  have lem (f g : ℝ → ℝ≥0∞) : (fun a => f a * η * g a)
    =       (fun a => η * f a * g a) := by ext;ring_nf
  have h₁ : AEStronglyMeasurable
        (fun a ↦ R.indicator (fun _ => (1 : ℝ)) a) volume :=
    AEStronglyMeasurable.indicator aestronglyMeasurable_const hR
  have hm : MeasurableSet (RNPnn θ₀ θ₁ η ρ) := by
    simp only [RNPnn, ge_iff_le, zero_le, setOf_true, MeasurableSet.univ]
  have h₀ : AEStronglyMeasurable (fun a : ℝ ↦ (RNPnn θ₀ θ₁ η ρ).indicator (fun _ => (1:ℝ)) a) volume := by
    simp only [RNPnn, ge_iff_le, zero_le, setOf_true, mem_univ, indicator_of_mem]
    exact aestronglyMeasurable_const
  have hi : ∫⁻ x, (Set.indicator (RNPnn θ₀ θ₁ η ρ) 1 x - Set.indicator R 1 x)
    * (ρ θ₁ x - η * ρ θ₀ x) ≥ 0 := by
    exact
      zero_le
        (∫⁻ (x : ℝ), ((RNPnn θ₀ θ₁ η ρ).indicator 1 x - R.indicator 1 x) * (ρ θ₁ x - η * ρ θ₀ x))

  ring_nf at hi
  have hAE (θ : ℝ)
   : AEStronglyMeasurable
    ((RNPnn θ₀ θ₁ η ρ).indicator (fun _ => (1:ℝ≥0∞)) * ρ θ₀) volume
     := by
     have := h₀
     have := (hI θ).aestronglyMeasurable
    --  apply AEStronglyMeasurable.mul
     refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
     refine AEMeasurable.mul' ?_ ?_
     apply hmm''
     apply hmm'

  have hAER (θ : ℝ)
   : AEStronglyMeasurable
    (R.indicator (fun _ => (1:ℝ≥0∞)) * ρ θ₀) volume
     := by
     have := h₀
     have := (hI θ).aestronglyMeasurable
    --  apply AEStronglyMeasurable.mul
     refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
     refine AEMeasurable.mul' ?_ ?_
     apply hmR
     apply hmm'


  have hI'' : Integrable (fun a ↦ R.indicator 1 a * ρ θ₀ a) volume :=
    sorry --NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₀' : Integrable (fun a ↦ R.indicator 1 a * ρ θ₁ a) volume :=
    sorry --NP.intRNP₀ hρ (hI _) <| hAER _
  have hI₁ : Integrable (fun x ↦ (RNPnn θ₀ θ₁ η ρ).indicator 1 x * ρ θ₀ x) volume :=
    sorry --NP.intRNP₀ hρ (hI _) <| hAE _
  have hI₁' : Integrable (fun a ↦ (RNPnn θ₀ θ₁ η ρ).indicator 1 a * ρ θ₁ a) volume := by
    sorry --apply NP.intRNP₀ hρ (hI _) <| h₀.mul (hI _).aestronglyMeasurable

  have ringNF : (fun x =>
    ((RNPnn θ₀ θ₁ η ρ).indicator 1 x - R.indicator 1 x) * (ρ θ₁ x - η * ρ θ₀ x))
    =
    (fun x =>
      (RNPnn θ₀ θ₁ η ρ).indicator 1 x * ρ θ₁ x -
      (RNPnn θ₀ θ₁ η ρ).indicator 1 x * η * ρ θ₀ x
      - R.indicator 1 x * ρ θ₁ x +
      R.indicator 1 x * η * ρ θ₀ x)
    := by
    ext x
    ring_nf
    repeat rw [ENNReal.sub_mul]
    · sorry
    -- generalize (RNPnn θ₀ θ₁ η ρ).indicator (fun _ => (1:ℝ≥0∞)) x = A
    -- generalize R.indicator (fun _ => (1:ℝ≥0∞)) x = B
    -- generalize ρ θ₁ x = C₁
    -- generalize ρ θ₀ x = C₀
    -- have (a b c : ℝ≥0∞) : (a-b)*c=a*c-b*c := by
    --     refine ENNReal.sub_mul ?_
    --     intro h₀ h₁
    --     sorry
    -- NOT CLEAR THAT THIS ARGUMENT CAN WORK OVER ENNREAL
    sorry

  sorry
