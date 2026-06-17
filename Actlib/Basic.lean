/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping

/-!

# Cramér-Lundberg distribution

Main results:
* `first_loss_is_ruinous' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :`
    `(Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}`
    `= some ⟨r / (r + s), by field_simp;linarith⟩`
    For two independent random variables `X~exponential(r)` and `Y~exponential(s)`,
    where `r` and `s` are the rates of occurrence (so `E(X)=1/r` and `E(Y)/1/s`)
    the probability that `X≤Y` is `r/(r+s)`.
    We interpret `X` as the loss incurred and `Y` as the capital accrued when the loss
    occurs. `Y` is proportional to time.

* Definition of `integralEquation`:
  `  ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t * ∫ x in Set.Iic (u + c * t),`
    `φ (u + c * t - x) * exponentialPDFReal β x`
  (If α=0 it corresponds to fixing t=∞ and φ=1)
  We interpret this:
  `φ u` = probability of eventual nonruin given starting capital `u`.
  `α` = rate associated with waiting for a loss (units `1/time`)
  `c` = insurance income rate, so that at time `t` we have `u+ct` dollars.
        (units `dollars/time`)
  `β` = rate associated with the size of a loss
        (units `1/dollars`)
  The equation says: the probability of nonruin given starting capital `u`
  is the probability that at some time `t` the first loss occurs, in an amount `x`,
  and `0 ≤ u + ct - x` so that we don't experience ruin at time `t`; and
  then we experience nonruin starting with capital `u+ct-x`.


* A solution to `integralEquation` is
  `φ = fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u)`.

  `lemma ruin_theory_classical_model_solution_Aristotle {α β c : ℝ} {φ : ℝ → ℝ}`
  `(hα : 0 < α) (hc : 0 < c) (hβ : 0 < β)`
    `(h : φ = fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u)) :`
    `integralEquation α β c φ := by`

 * In progress: environment change
 `def integralEquation₂ (α₀ α₁ Λ₀ Λ₁ c₀ c₁ β₀ β₁ : ℝ)`
    `(φ₀ φ₁ : ℝ → ℝ) :=`
    `(∀ u ≥ 0, φ₀ u = ∫ t, exponentialPDFReal α₀ t`
        `* exponentialPDFReal Λ₀ t`
        `* ((1/α₀) * φ₁ (u + c₀ * t) +`
        `(1/Λ₀) * (∫ x in Set.Iic (u + c₀ * t),`
    `φ₀ (u + c₀ * t - x) * exponentialPDFReal β₀ x))) ∧`
    `(∀ u ≥ 0, φ₁ u = ∫ t, exponentialPDFReal α₁ t`
        `* exponentialPDFReal Λ₁ t`
        `* ((1/α₁) * φ₀ (u + c₁ * t) +`
        `(1/Λ₁) * (∫ x in Set.Iic (u + c₁ * t),`
    `φ₁ (u + c₁ * t - x) * exponentialPDFReal β₁ x)))`

-/
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open ProbabilityTheory MeasureTheory


/-- (Aristotle): exponentialPDFReal simplification for nonneg argument -/
lemma exponentialPDFReal_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDFReal r x = r * exp (-(r * x)) := by
  simp [exponentialPDFReal, gammaPDFReal, hx, Gamma_one]

/-- (Aristotle): exponentialPDFReal is zero for negative argument -/
lemma exponentialPDFReal_of_neg {r x : ℝ} (hx : x < 0) :
    exponentialPDFReal r x = 0 := by
  simp [exponentialPDFReal, gammaPDFReal, not_le.mpr hx]


/-- A trivial glue lemma. -/
lemma integral_ite (f : ℝ → ℝ) :
    (∫ (a : ℝ), if 0 ≤ a then f a else 0)
    = ∫ (a : ℝ) in Ici 0, f a := by
    rw [← integral_indicator]
    · rfl
    · exact measurableSet_Ici

/-- A trivial glue lemma. -/
lemma integral_exponentialPDFReal_eq (z) :
    ∫ a, exponentialPDFReal z a =
    ∫ a in Set.Ici 0, z * Real.exp (-(z * a)) := by
  unfold exponentialPDFReal gammaPDFReal
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]
  apply integral_ite

/-- A trivial identity. -/
lemma Real.neg_mul_add (s r x : ℝ) :
    -(s * x) + -(r * x) = -((s+r) * x) := by linarith

-- We need five "obvious" lemmas about measurability and integrability.
lemma ae {r s : ℝ} (x : ℝ) :
    AEStronglyMeasurable (fun y ↦ if x ≤ y then
    exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite ?_ ?_ ?_
  · apply measurableSet_Ici
  · refine Measurable.mul measurable_const <| measurable_exponentialPDFReal s
  simp

lemma integral_exponentialPDFReal_eq_one (z : ℝ) (hz : 0 < z) :
    ∫ (y : ℝ), exponentialPDFReal z y = 1 := by
  have := @lintegral_exponentialPDF_eq_one z hz
  have h₁ : (1 : ℝ) = (1 : ENNReal).toReal := rfl
  rw [h₁]
  rw [← this]
  refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
  · rw [Filter.EventuallyLE, Filter.Eventually]
    exact Filter.univ_mem' <| exponentialPDFReal_nonneg hz
  unfold exponentialPDFReal
    gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite measurableSet_Ici ?_ measurable_const
  · exact Measurable.mul measurable_const <|Measurable.exp
      <| Measurable.neg <| measurable_const_mul z

/-- r = frequency-of-loss occurrence rate
s = amount-of-loss-stopping rate
c = 1 here
-/
lemma prob_first_loss_is_ruinous {r s : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ (loss : ℝ) in Set.Ici 0,
    (∫ (time : ℝ) in Set.Iic loss,
      exponentialPDFReal s loss *
      exponentialPDFReal r time) = r / (r + s) := by
  simp_rw [integral_const_mul]
  have h₁ := @cdf_expMeasure_eq_integral r hr
  simp_rw [← h₁]
  simp_rw [@cdf_expMeasure_eq r hr]
  unfold exponentialPDFReal gammaPDFReal
  suffices (∫ (y : ℝ) in Set.Ici 0,
    if 0 ≤ y then s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y))) else 0) =
    r / (r + s) by
    rw [← this]
    congr
    ext y
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, mul_ite,
      ite_mul, zero_mul, mul_zero, ite_eq_left_iff, not_le, right_eq_ite_iff, zero_eq_mul,
      mul_eq_zero, Real.exp_ne_zero, or_false]
    intro h₀ h₁
    linarith
  suffices (∫ (y : ℝ) in Set.Ici 0,
    s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y)))) = r / (r + s) by
    rw [← this]
    apply integral_congr_ae
    refine Set.EqOn.aeEq_restrict ?_ ?_
    · intro x hx
      simp only [ite_eq_left_iff, not_le, zero_eq_mul, mul_eq_zero, Real.exp_ne_zero, or_false]
      intro hx₀
      simp at hx
      linarith
    · simp
  simp_rw [mul_sub]
  simp only [mul_one]
  rw [integral_sub]
  · have : ∫ (a : ℝ) in Set.Ici 0, s * Real.exp (-(s * a)) = 1 := by
      rw [← integral_exponentialPDFReal_eq]
      exact EReal.coe_eq_one.mp (congrArg Real.toEReal
        (integral_exponentialPDFReal_eq_one s hs))
    rw [this]
    simp_rw [mul_assoc, ← exp_add, Real.neg_mul_add]
    rw [integral_const_mul]
    have :          ∫ (x : ℝ) in Set.Ici 0, Real.exp (-((s + r) * x))
      = (1/(s+r)) * ∫ (x : ℝ) in Set.Ici 0, (s+r) * Real.exp (-((s + r) * x)) := by
        rw [integral_const_mul]
        field_simp
    rw [this]
    rw [← integral_exponentialPDFReal_eq,
      integral_exponentialPDFReal_eq_one]
    · field_simp
      linarith
    · linarith
  · refine integrable_of_integral_eq_one ?_
    rw [← integral_exponentialPDFReal_eq]
    rw [integral_exponentialPDFReal_eq_one]
    exact hs
  · simp_rw [mul_assoc, ← exp_add]
    simp_rw [Real.neg_mul_add]
    have : (fun y ↦ s * Real.exp (-((s + r) * y)))
         = (fun _ => s / (s + r)) * (fun y ↦ (s + r) * Real.exp (-((s + r) * y))) := by
      ext y
      simp
      field_simp
    rw [this]
    refine Integrable.const_mul' ?_ _
    refine integrable_of_integral_eq_one ?_
    rw [← integral_exponentialPDFReal_eq]
    rw [integral_exponentialPDFReal_eq_one]
    linarith

lemma exp_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x y : ℝ) :
    0 ≤ if x ≤ y then exponentialPDFReal r x * exponentialPDFReal s y else 0 := by
  split_ifs with g₀
  · apply mul_nonneg
    · exact exponentialPDFReal_nonneg hr _
    · exact exponentialPDFReal_nonneg hs _
  · simp

lemma measExp₁ (r : ℝ) :
    Measurable fun (a : ℝ × ℝ) ↦ exponentialPDFReal r a.1 := by
  refine Measurable.ite ?_ ?_ ?_
  · simp only [measurableSet_setOf]
    refine Measurable.le' measurable_const measurable_fst
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul measurable_const <| Measurable.pow_const measurable_fst _
    · refine Measurable.exp <| Measurable.neg
        <| Measurable.mul measurable_const measurable_fst
  simp

lemma measExp₂ (r : ℝ) :
    Measurable fun (a : ℝ × ℝ) ↦ exponentialPDFReal r a.2 := by
  refine Measurable.ite ?_ ?_ ?_
  · simp only [measurableSet_setOf]
    refine Measurable.le' measurable_const measurable_snd
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul measurable_const <| Measurable.pow_const measurable_snd _
    · refine Measurable.exp <| Measurable.neg <| Measurable.mul measurable_const measurable_snd
  simp

lemma ae' {r s : ℝ} :
    AEMeasurable (fun a ↦ {x | x.1 ≤ x.2}.indicator
    (fun a ↦ exponentialPDF r a.1 * exponentialPDF s a.2) a)
    (volume.prod volume) := by
  refine (aemeasurable_indicator_iff ?_).mpr ?_
  · simp only [measurableSet_setOf]
    exact measurable_le
  · refine Measurable.aemeasurable ?_
    refine measurable_coe_nnreal_ennreal_iff.mpr ?_
    refine Measurable.mul ?_ ?_
    all_goals
        refine Measurable.real_toNNReal ?_
    · apply measExp₁
    · apply measExp₂

lemma exponentialPDFReal_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (exponentialPDFReal r) volume := by
      apply MeasureTheory.Integrable.mono' _ _ _;
      · apply fun x => if x ≥ 0 then r * Real.exp ( -r * x ) else 0;
      · -- The integral of the exponential function is convergent.
        have h_exp : ∫ x in Set.Ici 0, Real.exp (-r * x) = 1 / r := by
          rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ] ;
          have := integral_exp_neg_mul_rpow zero_lt_one hr
          norm_num [ Real.rpow_neg_one ] at * ; aesop;
        apply MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) |>.2 _;
        exact MeasureTheory.Integrable.const_mul
          (( by contrapose! h_exp; rw [ MeasureTheory.integral_undef h_exp ]
                norm_num; positivity ) ) _;
      · exact Measurable.aestronglyMeasurable (Measurable.ite ( measurableSet_Ici )
          (by measurability) (by measurability ) );
      · simp only [exponentialPDFReal, Real.norm_eq_abs, ge_iff_le, neg_mul];
        filter_upwards [ ] with x
        split_ifs
        · simp_all only [gammaPDFReal, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
            Real.rpow_zero, mul_one, abs_mul, Real.abs_exp];
          rw [ abs_of_pos hr ]
        · simp_all [ gammaPDFReal ];

lemma integ {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun (a : ℝ × ℝ) ↦ if a.1 ≤ a.2 then
      exponentialPDFReal r a.1 * exponentialPDFReal s a.2 else 0) (volume.prod volume) := by
        apply MeasureTheory.Integrable.indicator _ _;
        · exact MeasureTheory.Integrable.mul_prod ( exponentialPDFReal_integrable hr )
            ( exponentialPDFReal_integrable hs );
        · exact measurableSet_le measurable_fst measurable_snd

lemma integ₀ {r s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable (fun (y : ℝ) ↦ if x ≤ y then
    exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
  have := @MeasureTheory.Integrable.indicator ℝ ℝ Real.measurableSpace
    {y | x ≤ y} volume _ _
  apply this
  · generalize exponentialPDFReal r x = α
    apply Integrable.const_mul
    exact exponentialPDFReal_integrable hs
  · apply measurableSet_le
    · simp only [measurable_const]
    · exact measurable_id'

open MeasureTheory ProbabilityTheory MeasureTheory.Measure


-- ARISTOTLE START
theorem integrable_exponential_joint (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun x ↦ ∫ (y : ℝ), if x ≤ y then
    exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
  -- The inner integral can be computed explicitly.
  have h_inner : ∀ x, ∫ y, (if x ≤ y then
  (exponentialPDFReal r x) * (exponentialPDFReal s y) else 0)
    = (exponentialPDFReal r x) * (if 0 ≤ x then Real.exp (-s * x) else 1) := by
    intro x
    by_cases hx : 0 ≤ x;
    · -- For $x \geq 0$, we can simplify the integral.
      have h_simp : ∫ y in Set.Ici x, exponentialPDFReal s y = Real.exp (-s * x) := by
        have h_inner : ∫ y in Set.Ici x, s * Real.exp (-s * y) = Real.exp (-s * x) := by
          have := integral_exp_neg_mul_rpow zero_lt_one hs;
          rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ]
          rw [ MeasureTheory.integral_const_mul ]
          rw [ show ( ∫ y in Set.Ioi x, Real.exp ( -s * y ) )
            = ( ∫ y in Set.Ioi 0, Real.exp ( -s * ( y + x ) ) ) by
              rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ),
              ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ] ;
              rw [ ← MeasureTheory.integral_add_right_eq_self _ x ] ; congr; ext y;
              rw [ Set.indicator_apply, Set.indicator_apply ] ; aesop ] ;
              simp_all only [Real.rpow_one, neg_mul, div_one, Real.rpow_neg_one, ne_eq,
                one_ne_zero, not_false_eq_true, div_self, mul_add, Real.exp_add];
          rw [ MeasureTheory.integral_mul_const, this ] ; norm_num [ hs.ne' ];
        convert h_inner using 1;
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun y hy => ?_
        simp [exponentialPDFReal];
        simp [ gammaPDFReal];
        grind;
      simp_all only [measurableSet_Ici, ← integral_indicator, Set.indicator_apply,
        Set.mem_Ici, neg_mul, ↓reduceIte];
      rw [ ← h_simp, ← MeasureTheory.integral_const_mul ] ; congr ; ext ; split_ifs <;> ring;
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ]
        <;> norm_num [ hx, exponentialPDFReal ];
      · change ∫ y in Set.Ici x, gammaPDFReal 1 r x * gammaPDFReal 1 s y = gammaPDFReal 1 r x;
        · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi ];
          norm_num [ gammaPDFReal ];
          grind;
      · norm_num;
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
  simp_all only [exponentialPDFReal, mul_comm, mul_neg, Real.exp_neg, mul_ite, one_mul];
  have h_integrable : MeasureTheory.Integrable (fun x => (if 0 ≤ x then Real.exp (-r * x) else 0) *
    (if 0 ≤ x then Real.exp (-s * x) else 1)) MeasureTheory.volume := by
    have h_integrable : MeasureTheory.IntegrableOn
      (fun x => Real.exp (-(r + s) * x)) (Set.Ici 0) := by
      have := ( exp_neg_integrableOn_Ioi 0 ( by linarith : 0 < r + s ) );
      rwa [ MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici ] at *;
    rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) ] at *;
    convert h_integrable using 1
    · rfl
    ext x ; split_ifs <;> simp_all [ ← Real.exp_add ] ; ring;
  convert h_integrable.const_mul ( r : ℝ ) using 2
  norm_num [ Real.exp_neg, Real.exp_ne_zero, hr.ne', hs.ne', gammaPDFReal ] ; ring_nf

lemma div_add_nonneg {r s : ℝ} (hs : 0 < s) (hr : 0 < r) : 0 ≤ r / (r + s) := by
    field_simp;linarith

lemma first_loss_is_ruinous' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}
    = some ⟨r / (r + s), div_add_nonneg hs hr⟩ := by
  have : (volume.withDensity (exponentialPDF r)).prod
    (volume.withDensity (exponentialPDF s))
    = (Measure.prod (expMeasure r) (expMeasure s)) := by
      exact Measure.ext_iff.mpr fun s_1 ↦ congrFun rfl
  rw [← this]
  have h₀ := @prod_withDensity ℝ _ volume ℝ _ volume
    instSFiniteOfSigmaFinite (exponentialPDF r) (exponentialPDF s)
    (Measurable.ennreal_ofReal <| measurable_exponentialPDFReal r)
    (Measurable.ennreal_ofReal <| measurable_exponentialPDFReal s)
  rw [h₀]
  simp_rw [← prob_first_loss_is_ruinous hs hr]
  rw [withDensity_apply]
  · have h₀ := @lintegral_indicator
      (ℝ × ℝ) Prod.instMeasurableSpace
      volume {x | x.1 ≤ x.2}
      measurableSet_le'
      (fun a => exponentialPDF r a.1 * exponentialPDF s a.2)
    rw [← Measure.volume_eq_prod]
    rw [← h₀]
    have h₂ := @lintegral_prod (α := ℝ) (β := ℝ) (μ := volume) (ν := volume)
      (f := fun a => {x | x.1 ≤ x.2}.indicator
        (fun a ↦ exponentialPDF r a.1 * exponentialPDF s a.2) a)
    have h₃ : (@Measure.prod ℝ ℝ _ _ volume volume : Measure (ℝ × ℝ))
         = (@volume (ℝ × ℝ) Measure.prod.measureSpace : Measure (ℝ × ℝ)) := by
        exact Eq.symm (Measure.volume_eq_prod ℝ ℝ)
    rw [← h₃]
    rw [h₂]
    · unfold Set.indicator
      simp only [Set.mem_setOf_eq, ENNReal.some_eq_coe]
      -- looks good, integrate over all x,y with x ≤ y
      unfold exponentialPDF
      have H₀ (x y : ℝ) :
          (if x ≤ y then ENNReal.ofReal (exponentialPDFReal r x)
                       * ENNReal.ofReal (exponentialPDFReal s y) else 0) =
          ENNReal.ofReal ( if x ≤ y then (exponentialPDFReal r x)
                                       * (exponentialPDFReal s y) else 0) := by
        split_ifs with g₀
        · refine Eq.symm (ENNReal.ofReal_mul ?_)
          exact exponentialPDFReal_nonneg hr x
        · exact Eq.symm ENNReal.ofReal_zero
      simp_rw [H₀]
      have (x : ℝ) :
        ∫⁻ (y : ℝ), ENNReal.ofReal (if x ≤ y then exponentialPDFReal r x
        * exponentialPDFReal s y else 0)
       = ENNReal.ofReal (∫ (y : ℝ), if x ≤ y then exponentialPDFReal r x
       * exponentialPDFReal s y else 0 ∂volume) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · apply integ₀ hs
          · simp only [Filter.EventuallyLE, Filter.Eventually, Pi.zero_apply]
            have : {x_1 | 0 ≤ if x ≤ x_1 then
              exponentialPDFReal r x * exponentialPDFReal s x_1 else 0}
              = Set.univ := by
              ext y
              simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              apply exp_nonneg hr hs
            rw [this]
            exact Filter.univ_mem
      simp_rw [this]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · have (x : ℝ) (hx : 0 ≤ x) :
            (⟨x,hx⟩ : {x : ℝ // 0 ≤ x}) = NNReal.mk x hx := rfl
        rw [this]
        rw [← ENNReal.ofReal_eq_coe_nnreal]
        apply congrArg -- yes!
        have hswap: (∫ (x : ℝ) (y : ℝ), if x ≤ y then
                exponentialPDFReal r x * exponentialPDFReal s y else 0)
                =  (∫ (y : ℝ) (x : ℝ), if x ≤ y then
                exponentialPDFReal r x * exponentialPDFReal s y else 0) := by
          apply integral_integral_swap
          -- certainly true...
          unfold Function.uncurry
          apply integ hr hs
        rw [← integral_indicator]
        · unfold Set.indicator
          simp only [Set.mem_Ici]
          rw [hswap]
          congr
          ext x
          split_ifs with g₀
          · rw [← integral_indicator]
            · unfold Set.Iic Set.indicator
              congr
              ext z
              rw [mul_comm]
              simp
            · simp
          · simp at g₀
            have : exponentialPDFReal s x = 0 := by
              unfold exponentialPDFReal gammaPDFReal
              split_ifs with g₁
              · linarith
              · rfl
            rw [this]
            simp
        · simp
      · apply integrable_exponential_joint _ _ hr hs
      · simp only [Filter.EventuallyLE, Filter.Eventually, Pi.zero_apply]
        refine Filter.univ_mem' ?_
        intro a
        simp only [Set.mem_setOf_eq]
        have : 0 = ∫ (y : ℝ), (0:ℝ) := by simp
        nth_rw 1 [this]
        apply integral_mono
        · apply integrable_zero
        · apply integ₀ hs
        · intro x
          apply exp_nonneg hr hs
    · exact instSFiniteOfSigmaFinite
    · apply ae'
  · exact measurableSet_le'

/-- Probably the assumption of σ-finiteness is not needed,
but that's fine. -/
lemma sigmaFiniteMeasure_pi_prod (μ ν : Measure ℝ)
  [SigmaFinite μ] [SigmaFinite ν] :
    Measure.pi ![μ, ν] {v | v 0 ≤ v 1} =
    Measure.prod μ ν {v | v.fst ≤ v.snd} := by
  have h := (@MeasureTheory.measurePreserving_finTwoArrow_vec
    ℝ Real.measurableSpace μ ν _ _).map_eq
  have h₁ : Measure.map (finTwoArrowEquiv ℝ)
    (Measure.pi ![μ, ν]) = Measure.prod μ ν := by
    rw [← h]
    simp
  rw [← h₁]
  symm
  rw [Measure.map_apply]
  · simp
  · refine Measurable.prodMk ?_ ?_
    all_goals exact measurable_pi_apply _
  · simp only [measurableSet_setOf];exact measurable_le

lemma expMeasure_pi_prod (r s : ℝ) :
    Measure.pi ![expMeasure r, expMeasure s] {v | v 0 ≤ v 1} =
    Measure.prod (expMeasure r) (expMeasure s) {v | v.fst ≤ v.snd} := by
  apply @sigmaFiniteMeasure_pi_prod (expMeasure r) (expMeasure s)
    (SigmaFinite.withDensity_of_ne_top' <| by simp [gammaPDF])
    (SigmaFinite.withDensity_of_ne_top' <| by simp [gammaPDF])

lemma first_loss_is_ruinous'' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (Measure.pi ![expMeasure r, expMeasure s]) {x | x 0 ≤ x 1}
    = some ⟨r / (r + s), div_add_nonneg hs hr⟩ := by
    rw [expMeasure_pi_prod]
    exact first_loss_is_ruinous' r s hs hr


-- In the degenerate case `s=0`, the measure becomes 0.
lemma first_loss_is_ruinous_zero (r : ℝ) :
    Measure.prod (expMeasure r) (expMeasure 0) {x | x.1 ≤ x.2} = 0 := by
  unfold expMeasure gammaMeasure gammaPDF gammaPDFReal
  simp

-- In the degenerate case `r=0`, the measure becomes 0.
lemma first_loss_is_ruinous_zero' (s : ℝ) :
    (Measure.prod (expMeasure 0) (expMeasure s)) {x | x.1 ≤ x.2} = 0 := by
  unfold expMeasure gammaMeasure gammaPDF gammaPDFReal
  simp


def integralEquation (α β c : ℝ) (φ : ℝ → ℝ) :=
  ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t * ∫ x in Set.Iic (u + c * t),
    φ (u + c * t - x) * exponentialPDFReal β x

-- lemma integralEquation_variant (α β c : ℝ) (φ : ℝ → ℝ)
--   (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c)
--   (h : Tendsto φ atTop (nhds 1)) -- added by Aristotle
--   (h_net_profit : α < β * c) -- added by Aristotle
--   (hφ : integralEquation α β c φ) :
--   ∀ u ≥ 0, φ u = 1 - α / (β * c) + α / c *
--     ∫ x : ℝ in Set.Icc 0 u, φ (u - x) * (1 - cdf (expMeasure β) x) := by
--   /- "The proof requires Fubini's theorem,
--   differentiation under the integral sign, and
--   Volterra equation theory,
--   which are extremely challenging to formalize." -/
--   sorry

lemma exists_solution (α β c : ℝ) :
    integralEquation α β c 0 := by simp [integralEquation]

/-- If the loss rate `α = 0` then the nonruin probability is `0`.
This is an odd consequence of the definition of `exponentialPDFReal`.
-/
lemma exists_solution' (β c : ℝ) (φ : ℝ → ℝ) :
    integralEquation 0 β c φ → ∀ u ≥ 0, φ u = 0 := by
  unfold integralEquation exponentialPDFReal gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, zero_mul,
    neg_zero, Real.exp_zero, ite_self, mul_ite, mul_zero, integral_zero]
  tauto

lemma exists_solution'' (α c : ℝ) (φ : ℝ → ℝ) :
    integralEquation α 0 c φ → ∀ u ≥ 0, φ u = 0 := by
  unfold integralEquation exponentialPDFReal gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, zero_mul,
    neg_zero, Real.exp_zero, ite_self, mul_zero, integral_zero]
  tauto

/-- u = starting capital, φ u = nonruin probability,
c = income rate, α = loss rate, β = loss-amount-stop-rate
The equation for `φ` is from the end of
https://en.wikipedia.org/wiki/Ruin_theory#Classical_model
`hc` says that the income rate makes the game exactly evenly fair
as in Applied Math Seminar April 8, 2026.
-/
lemma too_fair (α β c : ℝ) (φ : ℝ → ℝ) (hα : α ≠ 0)
    (hβ : β ≠ 0)
    (h : φ = fun u => 1 - ((α * β) / c) * Real.exp (-(1 / β - α / c) * u))
    (hc : c = α * β) :
    integralEquation α β c φ := by
  subst c
  rw [h]
  have : α * β / (α * β) = 1 := by
    field_simp
  rw [this]
  have : (1 / β - α / (α * β)) = 0 := by
    field_simp
    linarith
  rw [this]
  simp [integralEquation]
open Real


lemma ite_sub' (x y z : ℝ) :
    (if (0 ≤ x) then (y - z) else 0) =
    (if (0 ≤ x) then y else 0) -
    (if (0 ≤ x) then z else 0) := by
    split_ifs  <;> simp

theorem indicator_exp_integrable (u c t β : ℝ) :
    Integrable ((Set.Icc 0 (u + c * t)).indicator fun x ↦ β * rexp (-(β * x))) volume := by
  rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
  exact Continuous.integrableOn_Icc (by continuity)



/-- This verifies a claim from Wikipedia at the end of
https://en.wikipedia.org/wiki/Ruin_theory#Classical_model
β = claim size limitation rate (1 / $); 1/β=E(claim size) = $ = μ
λ = α = claim arrival rate (1/time); 1/α=E(claim time)=time
u = initial capital
φ(u)=nonruin probability

Units checK;
λ = 1 / hour        = α
c = $ / hour
λ / c = 1 / $       = α / c
μ = $               = 1 / β
λ μ / c = 1         = α / (β * c)
1/μ - λ/c = 1/$ - 1/$

Viability of the business requires
`c > λ μ ` i.e., `β * c > α`
-/
lemma ruin_theory_classical_model_solution {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c) (hβ : 0 < β)
    (h : φ = fun u => 1 - (α / (β * c)) * Real.exp (-(β - α / c) * u)) :
    integralEquation α β c φ := by
  intro u hu
  rw [h]
  unfold exponentialPDFReal gammaPDFReal
  simp only [neg_sub, rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one, mul_ite, mul_zero,
    ite_mul, zero_mul]
  simp_rw [sub_mul (a := (1:ℝ))]
  simp only [one_mul]
  have (t x : ℝ):
        α / (β * c) * rexp ((α / c - β) * (u + c * t - x)) * (β * rexp (-(β * x)))
        =
        α / (c) * (rexp ((α / c - β) * (u + c * t - x)) * (rexp (-(β * x))))
        := by field_simp
  simp_rw [this]
  simp_rw [← exp_add]
  have (t x : ℝ) :
    (α / c - β) * (u + c * t - x) + -(β * x) =
    ((α / c - β) * (u + c * t)) + (-(α / c) * x)
    := by ring_nf
  simp_rw [this]
  simp_rw [exp_add]
  simp_rw [ite_sub']
  have (t : ℝ) := @integral_indicator ℝ ℝ measurableSpace
    _ _ (fun x => (if 0 ≤ x then β * rexp (-(β * x)) else 0) -
            if 0 ≤ x then α / c * (rexp ((α / c - β) * (u + c * t)) * rexp (-(α / c) * x)) else 0)
    (Set.Iic (u + c * t))
    volume (by simp)
  simp_rw [← this]
  simp only [neg_mul]
  simp_rw [← Pi.sub_def]
  simp_rw [Set.indicator_sub']
  simp only [Pi.sub_apply]
  simp_rw [Set.indicator_apply]
  have (t : ℝ) := @integral_sub ℝ ℝ _ _ measurableSpace
    volume
    (fun x => (if x ∈ Set.Iic (u + c * t) then if 0 ≤ x then β * rexp (-(β * x)) else 0 else 0))
    (fun x => if x ∈ Set.Iic (u + c * t) then
              if 0 ≤ x then α / c * (rexp ((α / c - β) * (u + c * t)) * rexp (-(α / c * x))) else 0
            else 0) (by
        simp only [mem_Iic]
        have := @MeasureTheory.Integrable.indicator ℝ ℝ Real.measurableSpace
        have : ((fun x ↦ if x ≤ u + c * t then if 0 ≤ x then
            β * rexp (-(β * x)) else 0 else 0))
            = Set.indicator (Set.Icc 0 (u + c * t))
            (fun x => β * rexp (-(β * x))) := by
            ext x
            simp [Set.indicator]
            split_ifs
            all_goals
              try rfl
              try tauto
        simp_rw [this]
        apply indicator_exp_integrable) (by
        have (f : ℝ → ℝ) : (fun x ↦
            if x ∈ Set.Iic (u + c * t) then if 0 ≤ x then f x else 0 else 0)
            = Set.indicator (Set.Icc 0 (u + c * t))
            (fun x => f x)
            := by
            ext x
            simp [Set.indicator]
            split_ifs
            all_goals
              try tauto
              try rfl
        simp_rw [this]
        rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
        exact Continuous.integrableOn_Icc ( by continuity ))
  simp_rw [this]
  clear this
  simp only [mem_Iic]
  have (t : ℝ) : ∫ (a : ℝ), if a ≤ u + c * t then
    if 0 ≤ a then β * rexp (-(β * a)) else 0 else 0 ∂volume
    = ∫ (a : ℝ) in Set.Iic (u+c*t), exponentialPDFReal β a ∂volume :=
    by
    unfold exponentialPDFReal gammaPDFReal
    rw [← integral_indicator]
    · congr
      ext a
      simp [Set.indicator]
    · simp
  simp_rw [this]
  clear this
  simp_rw [mul_left_comm (a := α / c)]
  clear this
  have (t a : ℝ):
     (if a ≤ u + c * t then if 0 ≤ a then
      rexp ((α / c - β) * (u + c * t)) * (α / c * rexp (-(α / c * a))) else 0
            else 0)
        =
     rexp ((α / c - β) * (u + c * t)) *
      (if a ≤ u + c * t then if 0 ≤ a then (α / c * rexp (-(α / c * a))) else 0
            else 0) := by
    split_ifs <;> simp
  simp_rw [this]
  clear this
  simp_rw [integral_const_mul]
  have (t : ℝ):
    ∫ (a : ℝ),
              if a ≤ u + c * t then if 0 ≤ a then α / c * rexp (-(α / c * a)) else 0 else 0 ∂volume
              =
              ∫ (a : ℝ) in Set.Iic (u+c*t), exponentialPDFReal (α / c) a ∂volume
              := by
              rw [← integral_indicator]
              · congr
                ext a
                split_ifs with g₀ g₁
                · simp only [indicator, mem_Iic]
                  rw [if_pos (by tauto)]
                  unfold exponentialPDFReal gammaPDFReal
                  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one,
                    left_eq_ite_iff, not_le, mul_eq_zero, div_eq_zero_iff, exp_ne_zero, or_false]
                  intro g₂
                  linarith
                · simp only [indicator, mem_Iic, right_eq_ite_iff]
                  intro
                  unfold exponentialPDFReal gammaPDFReal
                  simp
                  tauto
                simp [Set.indicator]
                tauto
              simp
  simp_rw [this]
  clear this
  have (t : ℝ) : ∫ (a : ℝ) in Set.Iic (u + c * t), exponentialPDFReal (α/c) a
    = cdf (expMeasure (α/c)) (u+c*t) := by
        rw [cdf_expMeasure_eq_integral]
        apply div_pos <;> tauto
  simp_rw [this]
  clear this
  have (t : ℝ) :
    ∫ (a : ℝ) in Set.Iic (u + c * t), exponentialPDFReal β a
    =
    cdf (expMeasure β) (u+c*t)
    := Eq.symm (cdf_expMeasure_eq_integral hβ (u + c * t))
  simp_rw [this]
  clear this
  have (t : ℝ) :
    (cdf (expMeasure β)) (u + c * t)
    =
    ((if 0 ≤ u + c * t then 1 - rexp (-(β * (u + c * t))) else 0))
    := by
    rw [cdf_expMeasure_eq]
    tauto
--   simp_rw [cdf_expMeasure_eq]
  simp_rw [this]
  clear this
  have (t : ℝ) :
    (cdf (expMeasure (α / c))) (u + c * t)
    =
    ((if 0 ≤ u + c * t then 1 - rexp (-((α/c) * (u + c * t))) else 0))
    := by
    rw [cdf_expMeasure_eq]
    apply div_pos <;> tauto
  simp_rw [this]
  clear this
  simp only [mul_ite, mul_zero]
  have :
  ∫ (t : ℝ),
    (if 0 ≤ t then
    α * rexp (-(α * t)) *
      ((if 0 ≤ u + c * t then 1 - rexp (-(β * (u + c * t))) else 0) -
        if 0 ≤ u + c * t then rexp ((α / c - β) * (u + c * t))
        * (1 - rexp (-(α / c * (u + c * t)))) else 0)
    else 0)
    =
    ∫ (t : ℝ),
    if 0 ≤ t then
      α * rexp (-(α * t)) *
        ((1 - rexp (-(β * (u + c * t)))) -
          rexp ((α / c - β) * (u + c * t)) * (1 - rexp (-(α / c * (u + c * t)))))
    else 0
    := by
    congr
    ext t
    split_ifs with g₀ g₁
    · ring_nf
    · exfalso
      apply g₁
      apply add_nonneg
      · linarith
      apply mul_nonneg
      · linarith
      · tauto
    rfl
  simp_rw [this]
  clear this
  field_simp
  have (t : ℝ):
        (1 - rexp (-(β * (u + c * t)))
        - rexp ((α - β * c) * (u + c * t) / c) * (1 - rexp (-(α * (u + c * t) / c)))) =
        1 - rexp (-(β * (u + c * t)))
          - rexp ((α - β * c) * (u + c * t) / c) * 1
          + rexp ((α - β * c) * (u + c * t) / c) * rexp (-(α * (u + c * t) / c)) := by
      ring_nf
  simp_rw [this]
  clear this
  simp_rw [← exp_add]
  have (t : ℝ) :
    ((α - β * c) * (u + c * t) / c + -(α * (u + c * t) / c))
    =
    ( - β ) * (u + c * t)
    := by field_simp;ring_nf
  simp_rw [this]
  simp only [mul_one, neg_mul]
  have (t : ℝ) :
    1 - rexp (-(β * (u + c * t)))
      - rexp ((α - β * c) * (u + c * t) / c) + rexp (-(β * (u + c * t)))
    =
    1
      - rexp ((α - β * c) * (u + c * t) / c)
    := by linarith
  simp_rw [this]
  simp_rw [mul_sub]
  simp only [mul_one]
  simp_rw [mul_assoc]
  simp_rw [← exp_add]
  have (t : ℝ) :
    -(α * t) + (α - β * c) * (u + c * t) / c
    =
     (α) * (u) / c
     -
     (β) * (u + c * t)
    := by field_simp;ring_nf
  simp_rw [this]
  have : ∫ (t : ℝ), (if 0 ≤ t then
    α * rexp (-(α * t)) - α * rexp (α * u / c - β * (u + c * t)) else 0)
    = (∫ (t : ℝ), if 0 ≤ t then α * rexp (-(α * t)) else 0)
    - ∫ (t : ℝ), if 0 ≤ t then α * rexp (α * u / c - β * (u + c * t)) else 0
    := by
    rw [← integral_sub]
    · congr
      ext t
      split_ifs <;> simp
    · have (t : ℝ) : -(α * t) = -α * t := by exact neg_mul_eq_neg_mul α t
      simp_rw [this]
      have : Integrable (exponentialPDFReal α) := by
        exact exponentialPDFReal_integrable hα
      unfold exponentialPDFReal gammaPDFReal at this
      simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one] at this
      convert this using 1
      ext t
      simp
    · have :
            ((fun t ↦ if 0 ≤ t then α * rexp (α * u / c - β * (u + c * t)) else 0))
            =
            (fun t ↦ if 0 ≤ t then α * rexp (α * u / c - β * u + -(β * c) * t) else 0)
        := by
            ext t
            split_ifs with g₀
            · field_simp
              apply congrArg
              field_simp
              ring_nf
            · rfl
      simp_rw [this]
      clear this
      simp_rw [exp_add]
      have :
          (fun t ↦ if 0 ≤ t then α * (rexp (α * u / c - β * u) * rexp (-(β * c) * t)) else 0)
        = (fun t ↦ α * (rexp (α * u / c - β * u) * (β * c)⁻¹) * if 0 ≤ t then ( ((β * c) *
            rexp (-(β * c) * t))) else 0)
        := by
        ext t
        split_ifs with g₀
        · field_simp
        · simp
      simp_rw [this]
      clear this
      rw [integrable_const_mul_iff]
      · suffices Integrable (exponentialPDFReal (β * c)) by
          unfold exponentialPDFReal gammaPDFReal at this
          simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one, neg_mul] at this ⊢
          exact this
        refine exponentialPDFReal_integrable ?_
        apply mul_pos <;> tauto
      simp
      constructor
      · linarith
      · constructor <;> linarith
  simp_rw [this]
  clear this
  have : (∫ (t : ℝ), if 0 ≤ t then α * rexp (-(α * t)) else 0)
    = ∫ (t : ℝ), exponentialPDFReal α t := by
    congr
    ext t
    unfold exponentialPDFReal gammaPDFReal
    simp
  simp_rw [this]
  clear this
  have : (∫ (t : ℝ), exponentialPDFReal α t)
    = 1 := integral_exponentialPDFReal_eq_one α hα
  simp_rw [this]
  repeat rw [mul_sub]
  simp
  ring_nf
  have (t : ℝ) :
    (α * u * c⁻¹ - β * c * t - β * u)
    =
    (α * u * c⁻¹ - β * u + -(β * c) * t) := by
    ring_nf
  simp_rw [this]
  simp_rw [exp_add]
  have :
    (∫ (t : ℝ), if 0 ≤ t then α * (rexp (α * u * c⁻¹ - β * u) * rexp (-(β * c) * t)) else 0)
    =
    rexp (α * u * c⁻¹ - β * u) * (∫ (t : ℝ), if 0 ≤ t then α * (rexp (-(β * c) * t)) else 0)
    := by
    rw [← integral_const_mul]
    congr
    ext t
    split_ifs with g₀
    · ring_nf
    · simp
  rw [this]
  nth_rw 2 [mul_comm (a := β * c)]
  nth_rw 4 [mul_assoc]
  field_simp
  have :
   (c * β * ∫ (t : ℝ), if 0 ≤ t then α * rexp (-(c * β * t)) else 0)
   =
   (  ∫ (t : ℝ), c * β * if 0 ≤ t then α * rexp (-(c * β * t)) else 0)
   := by rw [← integral_const_mul]
  rw [this]
  clear this
  have : (∫ (t : ℝ), c * β * if 0 ≤ t then α * rexp (-(c * β * t)) else 0)
    = (∫ (t : ℝ), α *  if 0 ≤ t then c * β * rexp (-(c * β * t)) else 0)
    := by
    congr
    ext t
    split_ifs with g₀
    · field_simp
    · simp
  simp_rw [this]
  clear this
  rw [integral_const_mul]
  field_simp
  suffices ∫ a : ℝ, exponentialPDFReal (c * β) a = 1 by
    rw [← this]
    congr
    ext a
    unfold exponentialPDFReal gammaPDFReal
    simp
    split_ifs with g₀
    · field_simp
    · rfl
  refine integral_exponentialPDFReal_eq_one (c * β) ?_
  apply mul_pos <;> tauto

-- Aristotle work:


/-
The inner integral: ∫_{Iic s} φ(s-x) * exponentialPDFReal β x dx = 1 - exp(-γ s)
    where φ(y) = 1 - (α/(β*c)) * exp(-γ*y) and γ = β - α/c.
-/
lemma inner_integral_eq {α β c s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) (hs : 0 ≤ s) :
    ∫ x in Iic s,
      (1 - α / (β * c) * exp (-(β - α / c) * (s - x))) * (exponentialPDFReal β x) =
    1 - exp (-(β - α / c) * s) := by
  -- Split the integral into two parts: from negative infinity to 0 and from 0 to s.
  have h_split : ∫ x in Iic s, (1 - α / (β * c) * Real.exp (-(β - α / c) * (s - x)))
    * exponentialPDFReal β x = (∫ x in Set.Icc 0 s, (1 - α / (β * c)
      * Real.exp (-(β - α / c) * (s - x))) * β * Real.exp (-β * x)) := by
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ]
    <;> norm_num [ Set.indicator ];
    congr with x ; split_ifs <;> simp_all [ mul_assoc, mul_comm, mul_left_comm,
      exponentialPDFReal_of_nonneg, exponentialPDFReal_of_neg];
  convert h_split using 1;
  rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs ] ; ring_nf;
  rw [ intervalIntegral.integral_add ] <;> norm_num [ mul_assoc, mul_comm β, hβ.ne', ← Real.exp_add]
  · ring_nf
    simp_rw [fun x => add_sub_assoc -- added by Bjørn
      (-(s * β)) (s * α * c⁻¹) (α * c⁻¹ * x)]
    rw [ intervalIntegral.integral_comp_mul_left
      ( fun x => Real.exp ( -x ) ),
      @intervalIntegral.integral_comp_sub_mul
      (f := fun x => Real.exp ( - ( s * β ) + x ) ) ℝ Real.normedAddCommGroup
        _ _ _ _ _ _  ]
      <;> norm_num [ hβ.ne', hc.ne' ]
    · ring_nf;
      -- Combine like terms and simplify the expression.
      field_simp
      ring;
    · positivity;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
The outer integral: ∫ exponentialPDFReal α t * f(u + c*t) dt for the specific f.
-/
lemma outer_integral_eq {α β c u : ℝ} (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    ∫ t, exponentialPDFReal α t *
      (1 - exp (-(β - α / c) * (u + c * t))) =
    1 - α / (β * c) * exp (-(β - α / c) * u) := by
  -- Split the integral into two parts: one over $(-\infty, 0)$ and one over $[0, \infty)$.
  have h_split : ∫ t, exponentialPDFReal α t * (1 - Real.exp (-(β - α / c) * (u + c * t))) =
    (∫ t in Set.Ici 0, exponentialPDFReal α t * (1 - Real.exp (-(β - α / c) * (u + c * t)))) := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero];
    simp +contextual [exponentialPDFReal_of_neg];
  -- Evaluate the part of the integral over $[0, \infty)$.
  have h_eval : ∫ t in Set.Ici 0, exponentialPDFReal α t *
    (1 - Real.exp (-(β - α / c) * (u + c * t))) = (∫ t in Set.Ici 0, α * Real.exp (-α * t))
      - (∫ t in Set.Ici 0, α * Real.exp (-(α + c * (β - α / c)) * t)
      * Real.exp (-(β - α / c) * u)) := by
    rw [← MeasureTheory.integral_sub]
    · refine MeasureTheory.setIntegral_congr_fun
        measurableSet_Ici fun t ht => ?_
      rw [exponentialPDFReal_of_nonneg ht.out] ; ring_nf;
      · simpa only [mul_assoc, ← Real.exp_add] using by ring_nf;
    · have := (exp_neg_integrableOn_Ioi 0 hα);
      simpa only [MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici] using this.const_mul α
    · -- The integral of the exponential function is convergent.
      have h_exp_conv : ∫ t in Set.Ici 0, Real.exp (-(α + c * (β - α / c)) * t)
        = 1 / (α + c * (β - α / c)) := by
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
        have := integral_exp_neg_mul_rpow zero_lt_one
          (show 0 < α + c * (β - α / c) by nlinarith [mul_div_cancel₀ α hc.ne'])
        norm_num [Real.rpow_neg_one] at this ⊢ ; aesop;
      exact MeasureTheory.Integrable.mul_const (MeasureTheory.Integrable.const_mul
        ((by
        contrapose! h_exp_conv
        rw [MeasureTheory.integral_undef h_exp_conv]
        norm_num; nlinarith [mul_div_cancel₀ α hc.ne'])) _) _
  -- Evaluate the remaining integrals.
  have h_integrals : (∫ t in Set.Ici 0, α * Real.exp (-α * t)) = 1 ∧
    (∫ t in Set.Ici 0, α * Real.exp (-(α + c * (β - α / c)) * t)) = α / (α + c * (β - α / c)) := by
    constructor <;> rw [MeasureTheory.integral_const_mul]
        <;> rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
        <;> have := integral_exp_neg_mul_rpow zero_lt_one
        (show 0 < α by positivity) <;> have :=
        integral_exp_neg_mul_rpow zero_lt_one (show 0 < α + c * (β - α / c) by
        nlinarith [mul_div_cancel₀ α hc.ne']) <;> norm_num [Real.rpow_neg_one] at *;
    · rw [‹∫ x in Ioi 0, Real.exp (- (α * x)) = α⁻¹›, mul_inv_cancel₀ hα.ne'];
    · grind;
  simp_all [MeasureTheory.integral_mul_const];
  grind

lemma ruin_theory_classical_model_solution_Aristotle {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c) (hβ : 0 < β)
    (h : φ = fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u)) :
    integralEquation α β c φ := by
  intro u hu
  convert (outer_integral_eq hα hβ hc) using 1
  · rw [h, outer_integral_eq hα hβ hc]
  · convert (outer_integral_eq hα hβ hc) using 1
    congr! 2
    by_cases h : u + c * ‹ℝ› ≥ 0
      <;> simp_all only [neg_sub, ge_iff_le, exponentialPDFReal, mul_eq_mul_left_iff]
    · convert Or.inl (inner_integral_eq hα hβ hc h) using 1
      unfold exponentialPDFReal gammaPDFReal; ring_nf
    · simp_all only [not_le, gammaPDFReal, rpow_one, Gamma_one, div_one, sub_self,
      rpow_zero, mul_one, mul_ite, mul_zero, ite_eq_right_iff, mul_eq_zero, exp_ne_zero, or_false]
      exact Or.inr fun _ => by nlinarith


/-- clearly φ solves integralEquation α' β c' as long as
    α'/c' = α/c
    because it only depends on -/
 lemma one_phi_solves_many_integralEquations
 {α α' β c c' : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (hα' : 0 < α') (hc' : 0 < c')
    (hβ : 0 < β)
    (h : φ = fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u))
    (h' : α' / c' = α / c)
    :
    integralEquation α' β c' φ := by
  apply ruin_theory_classical_model_solution_Aristotle hα' hc' hβ
  rw [h]
  have (a b : ℝ) (h : 1 - a = 1 - b) : a = b := by
    rw [sub_right_inj] at h
    exact h
  ext u
  apply this
  field_simp
  ring_nf
  field_simp
  have : c * α' = c' * α := by field_simp at h';rw [← h'];ring_nf
  rw [this]
  field_simp
  apply congrArg
  field_simp
  repeat rw [mul_assoc]
  apply congrArg₂
  · rfl
  ring_nf
  apply congrArg₂
  · field_simp
  rw [this]
  ring_nf

/-- This lemma points out that the
solutino to the `integralEquation` does in fact
tend to 1 at `∞`, as suggested by `Aristotle`. -/
lemma ruin_theory_tendsto {α β c : ℝ}
    (hc : 0 < c) (h' : α < β * c) :
    Tendsto (fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u)) atTop (nhds 1) := by
  simp only [neg_sub]
  rw [← tendsto_sub_const_iff (b := 1)]
  simp only [sub_sub_cancel_left, sub_self]
  have h₀ : α / c - β < 0 := by field_simp;linarith
  generalize α / (β * c) = A at *
  generalize α / c - β = B at *
  suffices Tendsto (fun u ↦ -(A * rexp (B * u))) atTop (nhds (-0)) by
    convert this
    simp
  suffices Tendsto (fun u ↦ (A * rexp (B * u))) atTop (nhds 0) by
    exact Tendsto.neg this
  have := @Tendsto.mul ℝ _ _ _ ℝ (fun _ => A)
    (fun u => rexp (B * u)) atTop A 0 tendsto_const_nhds
    (by
    refine tendsto_exp_comp_nhds_zero.mpr ?_;refine tendsto_atTop_atBot_of_antitone ?_ ?_
    · intro x y hxy
      exact (mul_le_mul_left_of_neg h₀).mpr hxy
    · intro r
      use r / B
      have : B ≠ 0 := by linarith
      apply le_of_eq
      field_simp)
  convert this
  simp

-- Here we do not need 0 < α.
lemma ruin_theory_tendsto_converse {α β c : ℝ}
    (hc : 0 < c) (hβ : 0 < β)
    (h' : Tendsto (fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u))
      atTop (nhds 1)) : α < β * c := by
  rw [← tendsto_sub_const_iff (b := 1)] at h'
  by_contra H
  simp only [not_lt, neg_sub, sub_sub_cancel_left, sub_self] at H h'
  have h₀ : α / c - β ≥ 0 := by field_simp;linarith
  generalize α / c - β = A at *
  have h₁ : α / (β * c) ≥ 1 := by field_simp;linarith
  generalize α / (β * c) = B at *
  by_cases hA : A = 0
  · subst A;simp at h';linarith
  · have h₃ : A > 0 := lt_of_le_of_ne h₀ fun a ↦ hA (Eq.symm a)
    have h₄ : Tendsto (fun x ↦ B * rexp (A * x)) atTop atTop := by
      intro S hS
      unfold atTop at hS
      have ⟨a,ha⟩ : ∃ a, Ici a ⊆ S := mem_atTop_sets.mp hS
      simp only [mem_map, mem_atTop_sets, mem_preimage]
      by_cases H : a ≤ 0
      · use 0
        intro x hx
        apply ha
        apply le_trans
        · change a ≤ 0
          linarith
        · apply mul_nonneg
          · linarith
          · exact Real.exp_nonneg (A * x)
      use Real.log (a / B) / A -- a = B * rexp (A * x)
      intro x hx
      apply ha
      suffices a / B ≤ rexp (A * x) by
        field_simp at this ⊢
        exact this
      field_simp at hx
      have : rexp (log (a / B)) ≤ rexp (A * x) := by
        exact exp_le_exp.mpr hx
      convert this using 1
      refine Eq.symm (exp_log ?_)
      apply div_pos <;> linarith
    have h₂ := Tendsto.neg h'
    simp only [neg_neg, neg_zero] at h₂
    generalize ((fun x ↦ B * rexp (A * x))) = F at *
    have : nhds (0 : ℝ) = atTop := by
      exfalso
      have : Filter.map F atTop ≤ min (nhds 0) atTop := le_inf h₂ h₄
      simp only [nhds_inf_atTop, le_bot_iff, Filter.map_eq_bot_iff] at this
      exact NeBot.ne' this
    have g₀ : Set.Icc (-1:ℝ) 1 ∈ nhds 0 := by
      apply Icc_mem_nhds <;> simp
    have g₁ : Set.Icc (-1:ℝ) 1 ∉ atTop := by
      simp only [mem_atTop_sets, mem_Icc, not_exists, not_forall,
        not_and, not_le]
      intro y
      use max (y+1) 2
      constructor <;> simp
    rw [this] at g₀
    exact g₁ g₀

lemma ruin_theory_tendsto_iff {α β c : ℝ}
    (hc : 0 < c) (hβ : 0 < β) :
    Tendsto (fun u => 1 - (α / (β * c)) * exp (-(β - α / c) * u))
      atTop (nhds 1) ↔ α < β * c := by
  constructor
  · exact ruin_theory_tendsto_converse hc hβ
  · exact ruin_theory_tendsto hc

/-- From B. Norkin,
A system of integro-differential equations for the ruin probabilities of a risk process
in a Markovian environment, 2002
-/
def integralEquation₂ (α₀ α₁ Λ₀ Λ₁ c₀ c₁ β₀ β₁ : ℝ)
    (φ₀ φ₁ : ℝ → ℝ) :=
    --(If α=0 it should corresponds to fixing t=∞ and φ=1)
    (
    ∀ u ≥ 0, φ₀ u = ∫ t, exponentialPDFReal α₀ t
        * exponentialPDFReal Λ₀ t
        * ((1/α₀) * φ₁ (u + c₀ * t) +
        (1/Λ₀) * (∫ x in Set.Iic (u + c₀ * t),
    φ₀ (u + c₀ * t - x) * exponentialPDFReal β₀ x)
    ))
    ∧
    (
    ∀ u ≥ 0, φ₁ u = ∫ t, exponentialPDFReal α₁ t
        * exponentialPDFReal Λ₁ t
        * ((1/α₁) * φ₀ (u + c₁ * t) +
        (1/Λ₁) * (∫ x in Set.Iic (u + c₁ * t),
    φ₁ (u + c₁ * t - x) * exponentialPDFReal β₁ x)
    ))

-- lemma coupled_equations_trivial_case {α β c : ℝ}
--     (φ : ℝ → ℝ)
--     (hφ : φ = (fun u => 1 - (1 / (1 * 2)) * exp (-(1 - 1 / 2) * u)))
--     (h₀ : integralEquation α β c φ)
--     :
--     integralEquation₂ α α 1 1 c c β β
--         φ φ
--     := by
--     constructor
--     · intro u hu
--       unfold integralEquation at h₀
--       rw [h₀]
--       · simp [exponentialPDFReal, gammaPDFReal]
--         congr
--         ext t
--         split_ifs with g₀
--         · ring_nf
--           sorry
--         · sorry
--       · exact hu
--     · sorry
