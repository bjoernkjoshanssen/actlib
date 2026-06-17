import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open MeasureTheory

noncomputable section

def power (θ : ℝ) (RR : Set ℝ) := ∫ y : ℝ in RR, exponentialPDFReal θ y

def powerUniform (θ : ℝ) (RR : Set ℝ) := (volume (RR ∩ Set.Icc 0 θ)).toReal / θ


def RR (θ₀ θ₁ k : ℝ) := {y | exponentialPDFReal θ₀ y ≤ k * exponentialPDFReal θ₁ y}

def RRuniform (θ₀ θ₁ k : ℝ) := {y | (Set.indicator (Set.Icc 0 θ₀) 1 y) / θ₀
                                    ≤ k * (Set.indicator (Set.Icc 0 θ₁) 1 y) / θ₁}


lemma G {k : ℝ} (hk : k ≥ 1 / 2) :  (fun y ↦ (if 0 ≤ y then rexp (-y) else 0) ≤
    if 0 ≤ y then k * (2 * rexp (-(2 * y))) else 0) = fun x ↦ x ≤ log (2 * k)
      := by
      ext y
      have he : rexp (-(2*y)) = rexp (-y) * rexp (-y) := by
            rw [← exp_add]
            congr
            ring_nf
      split_ifs with g₀
      · constructor
        · intro h
          rw [he] at h
          field_simp at h
          have : rexp y * 1 ≤ rexp y * (rexp (-y) * k * 2) :=
            mul_le_mul_of_nonneg (le_refl _) h (exp_nonneg _) (by linarith)
          simp only [mul_one] at this
          repeat rw [← mul_assoc] at this
          rw [← exp_add] at this
          simp only [add_neg_cancel, exp_zero, one_mul] at this
          rw [mul_comm]
          refine (le_log_iff_exp_le ?_).mpr this
          linarith
        · intro h
          rw [he]
          apply le_of_mul_le_mul_right (a := rexp y)
          · rw [exp_neg y]
            field_simp
            rw [mul_comm]
            refine (le_log_iff_exp_le ?_).mp h
            simp
            linarith
          · exact exp_pos y
      · simp only [Std.le_refl, true_iff]
        linarith [log_nonneg (show 1 ≤ 2*k by linarith)]


lemma GG {a k : ℝ} (hk : k ≥ 1 / 2) (ha : a ≥ 0)
  (hr : ∫ (y : ℝ) in Ioc 0 a, exponentialPDFReal 1 y = 1 - rexp (-log 2 + -log k))
  : a = log (k * 2) := by
          simp only [exponentialPDFReal, gammaPDFReal, rpow_one, Gamma_one, ne_eq, one_ne_zero,
            not_false_eq_true, div_self, sub_self, rpow_zero, mul_one, one_mul] at hr
          have : (∫ (y : ℝ) in Ioc 0 a, if 0 ≤ y then rexp (-y) else 0)
                = ∫ (y : ℝ) in Ioc 0 a, rexp (-y) := by
            repeat rw [← integral_indicator]
            · congr
              ext x
              simp [Set.indicator]
              split_ifs
              all_goals try rfl
              linarith
            · simp
            · simp
          rw [this] at hr;clear this
          have h₀ (u v : ℝ) (huv : u ≤ v) : (∫ (y : ℝ) in Ioc u v, rexp (-y))
            = -rexp (-v) - (-rexp (-u)):= by
            have :  ∫ (y : ℝ) in Ioc u v, rexp (-y)
              =  ∫ (y : ℝ) in Ioc u v, - (deriv (rexp ∘ Neg.neg) (y))
              := by
              congr
              ext y
              rw [deriv_comp]
              · simp
              · simp
              · refine Differentiable.differentiableAt differentiable_neg
            rw [this]
            rw [integral_neg (deriv (rexp ∘ Neg.neg))]
            apply neg_injective
            simp only [neg_neg, sub_neg_eq_add, neg_add_rev]
            suffices ∫ (a : ℝ) in u..v, deriv (rexp ∘ Neg.neg) a = -rexp (-u) + rexp (-v) by
              rw [← this]
              generalize deriv (rexp ∘ Neg.neg) = F
              rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
              rw [if_pos huv, uIoc, smul_eq_mul, one_mul, min_eq_left huv, max_eq_right huv]
            rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real]
            · change (rexp ∘ Neg.neg) (v) - rexp (-u) = -rexp (-u) + rexp (-v)
              simp
              ring_nf
            · tauto
            · refine Continuous.comp_continuousOn continuous_exp continuousOn_neg
            · intro x hx
              exact (Differentiable.comp differentiable_exp
                differentiable_neg).differentiableAt.hasDerivAt.hasDerivWithinAt
            have : deriv (rexp ∘ Neg.neg) = Neg.neg ∘ (rexp ∘ Neg.neg) := by
              ext y
              rw [deriv_comp]
              · simp
              · simp
              · exact differentiable_neg.differentiableAt
            rw [this]
            refine Continuous.integrableOn_Icc ?_
            apply continuous_neg.comp <| continuous_exp.comp continuous_neg
          have : ∫ (y : ℝ) in Ioc 0 a, rexp (-y) =  1 - rexp (-a) := by
            rw [h₀]
            · simp
              linarith
            · tauto
          rw [this] at hr;clear this
          suffices -a = -log 2 + -log k by
            rw [log_mul]
            · linarith
            · linarith
            · simp
          apply exp_eq_exp.mp
          linarith


/--
May 1, 2026
As our first Neyman-Pearson example,
we show that when testing an exponential distribution with parameter
either 1 or 2, using the likelihood ratio test is at least as good as using
an interval of the form `Set.Ioc` as rejection region (actually it amounts to the same!).

TODO: generalize from 1, 2 to any θ₀, θ₁
-/
lemma neyman_pearson_trivial (θ₀ θ₁ k : ℝ) (hk : k ≥ 1 / 2) (α : ℝ)
    (hθ₀ : θ₀ = 1) (hθ₁ : θ₁ = 2)
    (hα : α = 1 - rexp (-log 2 + -log k))
    (region : ℝ → ℝ → Set ℝ)
    (hr : power θ₀ (region θ₀ θ₁) = α)
    (ha : ∃ a ≥ 0, region 1 2 = Set.Ioc 0 a) :
    power θ₀ (RR θ₀ θ₁ k) = α
    ∧ power θ₁ (region θ₀ θ₁) ≤ power θ₁ (RR θ₀ θ₁ k) := by
    have hh : {y | (if 0 ≤ y then rexp (-y) else 0) ≤
                    if 0 ≤ y then k * (2 * rexp (-(2 * y))) else 0} =
      Set.Iic (log (k * (2))) := by
      ext y
      simp only [mem_setOf_eq, mem_Iic]
      rw [congrFun (G hk) y]
      rw [mul_comm]
    have NPLemma₁ :
        power θ₀ (RR θ₀ θ₁ k) = α := by
      unfold RR power exponentialPDFReal gammaPDFReal
      subst hθ₀ hθ₁
      simp only [rpow_one, Gamma_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, sub_self,
        rpow_zero, mul_one, one_mul, div_one, mul_ite, mul_zero]
      rw [hα]
      have h₀ := @cdf_expMeasure_eq 1 (by simp) (log (2 * k))
      have h₁ : 0 ≤ log (2 * k) := by apply log_nonneg;linarith
      rw [if_pos h₁] at h₀
      simp only [one_mul] at h₀
      have : -log 2 + -log k = -log (2*k) := by
        rw [log_mul]
        · ring_nf
        · simp
        linarith
      rw [this]
      rw [← h₀]
      have := @cdf_expMeasure_eq_integral 1 (by simp)
      rw [this]
      congr
      · rw [G]
        simp
        linarith
      · simp [exponentialPDFReal, gammaPDFReal]
    have NPLemma₂ : power θ₁ (region θ₀ θ₁) ≤ power θ₁ (RR θ₀ θ₁ k) := by
        subst θ₀ θ₁
        simp only [RR, exponentialPDFReal, gammaPDFReal, rpow_one, Gamma_one, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, sub_self, rpow_zero, mul_one, one_mul, div_one, mul_ite,
          mul_zero]
        rw [hh]
        obtain ⟨a,ha⟩ := ha
        rw [ha.2] at hr ⊢
        unfold power at hr
        rw [hα] at hr
        field_simp at hr
        rw [GG hk ha.1 hr]
        simp only [power, exponentialPDFReal, gammaPDFReal, rpow_one, Gamma_one, div_one, sub_self,
          rpow_zero, mul_one]
        rw [Eq.symm integral_Icc_eq_integral_Ioc]
        apply le_of_eq
        repeat rw [← integral_indicator]
        · congr
          ext x
          simp [Set.Icc, Set.Iic, Set.indicator]
          split_ifs with g₀ g₁
          all_goals
            try rfl
            try tauto
        · simp
        · simp
    tauto
