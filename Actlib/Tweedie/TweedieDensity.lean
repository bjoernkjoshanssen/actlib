/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
/-! # Tweedie distribution density (μ=1, φ=1, p=3/2)

We define the Tweedie density and prove it is integrable with respect to Lebesgue measure.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Real MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

@[expose] public section
noncomputable section


/-- The Tweedie density series term for index j and point y. -/
def tweedieTerm (j : ℕ) (y : ℝ) : ℝ :=
  if j = 0 then 0 else y ^ j * 4 ^ j / (↑j.factorial * Gamma ↑j)

/-- Nonnegativity of individual series terms. -/
lemma tweedieTerm_nonneg {y : ℝ} (hy : 0 ≤ y) (j : ℕ) : 0 ≤ tweedieTerm j y := by
  unfold tweedieTerm
  split_ifs with h
  · simp
  · apply div_nonneg
    · apply mul_nonneg
      · exact pow_nonneg hy j
      · positivity
    · apply mul_nonneg
      · simp
      · exact Gamma_nonneg_of_nonneg (by positivity)

/-- The real-valued Tweedie density function. -/
def tweedieReal (y : ℝ) : ℝ :=
  if y ≤ 0 then 0
  else (∑' j, tweedieTerm j y) * rexp (-2 * (y + 1)) / y

/-- tweedieReal is zero for nonpositive arguments. -/
lemma tweedieReal_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : tweedieReal y = 0 := by
  simp [tweedieReal, hy]

/-- tweedieReal is nonneg. -/
lemma tweedieReal_nonneg (y : ℝ) : 0 ≤ tweedieReal y := by
  unfold tweedieReal
  split_ifs with h
  · exact le_refl 0
  · push Not at h
    refine div_nonneg ?_ (le_of_lt h)
    apply mul_nonneg
    · exact tsum_nonneg (tweedieTerm_nonneg (le_of_lt h))
    · exact exp_nonneg _

/-- Key bound: 4^(k+1) ≤ 44 * k! for all k : ℕ. -/
lemma four_pow_le_factorial_mul (k : ℕ) : (4 : ℝ) ^ (k + 1) ≤ 44 * k.factorial := by
  induction k with
  | zero => simp;linarith
  | succ n ih =>
    have : (n+1).factorial = (n+1) * n.factorial := rfl
    rw [this]
    nth_rw 2 [mul_comm]
    norm_num
    rw [← mul_assoc]
    have : (4:ℝ) ^ (n + 1 + 1) = 4 * 4 ^ (n+1) := pow_succ' 4 (n + 1)
    rw [this]
    rcases n with (_ | _ | _ | _ | _ | _ | k)
    all_goals norm_num
    ring_nf at *
    calc (4:ℝ)^k * 65536 = 4 ^ k * 4 * 16384 := by rw [mul_assoc];norm_num
         _ ≤ 4 * ↑(6 + k)! * 44 := by linarith
         _ ≤ ↑(6 + k)! * 308  := by linarith
         _ ≤ _ := by
            generalize (6 + k)! = A
            have hA : (A:ℝ) ≥ 0 := by simp
            have hk : (k:ℝ) ≥ 0 := by simp
            have : (A:ℝ) * k * 44 ≥ 0 := by
              apply mul_nonneg (mul_nonneg hA hk)
              norm_num
            linarith
  -- induction' k with k ih <;> norm_num [pow_succ', Nat.factorial_succ] at *
  -- rcases k with (_ | _ | _ | _ | _ | _ | k) <;>
  --   norm_num [Nat.factorial_succ, pow_succ] at *
  -- nlinarith [pow_pos (by norm_num : 0 < (4 : ℝ)) k]

/-
For j ≥ 1: tweedieTerm j y ≤ 44 * y^j / j!.
    Uses Γ(j) = (j-1)! ≥ 1 and 4^j/(j-1)! ≤ 44.
-/
lemma tweedieTerm_le {y : ℝ} (hy : 0 ≤ y) {j : ℕ} (hj : 0 < j) :
    tweedieTerm j y ≤ 44 * y ^ j / j.factorial := by
  unfold tweedieTerm;
  -- Since $j \geq 1$, we can simplify the expression to $y^j * 4^j / (j! * (j-1)!)$.
  suffices h_simp : y ^ j * 4 ^ j / (Nat.factorial j * (Nat.factorial (j - 1) : ℝ)) ≤
    44 * y ^ j / Nat.factorial j by
    cases j <;> simp_all +decide [ Nat.factorial, Real.Gamma_nat_eq_factorial ];
  rw [ div_le_div_iff₀ ] <;> try positivity;
  have := four_pow_le_factorial_mul ( j - 1 );
  rw [ Nat.sub_add_cancel hj ] at this ; nlinarith [ show 0 ≤ y ^ j * j.factorial by positivity ]

/-- Summability of the series for the Tweedie density. -/
lemma tweedieTerm_summable {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun j => tweedieTerm j y) := by
  have h_abs_summable : Summable (fun j : ℕ => y ^ j * 4 ^ j / (j.factorial * Real.Gamma j)) := by
    have h_abs_summable : Summable (fun j : ℕ => y ^ j * 4 ^ j / (j.factorial)) := by
      simpa only [← mul_pow] using Real.summable_pow_div_factorial _
    refine .of_nonneg_of_le (fun j => ?_) (fun j => ?_) h_abs_summable
    · positivity
    · rcases j with (_ | j) <;> norm_num [Nat.factorial_ne_zero, Real.Gamma_nat_eq_factorial]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (le_mul_of_one_le_right (by positivity) (mod_cast Nat.factorial_pos _))
  generalize_proofs at *
  convert h_abs_summable using 1; unfold tweedieTerm; aesop

/-
Bound on the sum: ∑ tweedieTerm j y ≤ 44 * (exp(y) - 1) for y ≥ 0.
-/
lemma tsum_tweedieTerm_le {y : ℝ} (hy : 0 ≤ y) :
    ∑' j, tweedieTerm j y ≤ 44 * (rexp y - 1) := by
  rw [ ← Summable.sum_add_tsum_nat_add 1 ];
  · -- Apply the bound to the series starting from j=1.
    have h_sum_bound : ∑' j : ℕ, tweedieTerm (j + 1) y ≤ ∑' j : ℕ,
      44 * y ^ (j + 1) / (j + 1).factorial := by
      apply Summable.tsum_le_tsum
      · exact fun i => tweedieTerm_le hy ( Nat.succ_pos i );
      · exact tweedieTerm_summable hy |> Summable.comp_injective <| Nat.succ_injective;
      · simp_rw [mul_div_assoc]
        apply Summable.mul_left (a := 44)
        have := @Summable.comp_injective ℝ ℕ ℕ _ _ _
          (fun i ↦ y ^ i / ↑(i)!) _ Nat.succ (by apply Real.summable_pow_div_factorial _)
          Nat.succ_injective
        exact this
    convert h_sum_bound using 1;
    · norm_num [ tweedieTerm ];
    · norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
      rw [ Summable.tsum_eq_zero_add ( show Summable _ from Real.summable_pow_div_factorial _ ) ]
      norm_num [ mul_div_assoc, tsum_mul_left ];
  · exact tweedieTerm_summable hy

/-
(exp(y) - 1) / y ≤ exp(y) for y > 0.
-/
lemma exp_sub_one_div_le_exp {y : ℝ} (hy : 0 < y) :
    (rexp y - 1) / y ≤ rexp y := by
  rw [ div_le_iff₀ hy ] ; nlinarith [ Real.exp_pos y,
    Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ),
    Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ]

/-
Main bound: tweedieReal y ≤ 44 * exp(-y-2) for y > 0.
-/
lemma tweedieReal_le_bound_pos {y : ℝ} (hy : 0 < y) :
    tweedieReal y ≤ 44 * rexp (-y - 2) := by
  -- By tsum_tweedieTerm_le, the sum ≤ 44 * (exp(y) - 1).
  have h_sum : ∑' j, tweedieTerm j y ≤ 44 * (Real.exp y - 1) := by
    exact tsum_tweedieTerm_le hy.le;
  -- By exp_sub_one_div_le_exp, (exp(y) - 1) / y ≤ exp(y).
  have h_exp_sub_one_div_y : (Real.exp y - 1) / y ≤ Real.exp y := by
    grind +suggestions;
  -- Combine the inequalities to conclude the proof.
  have h_combined : (∑' j, tweedieTerm j y) * Real.exp (-2 * (y + 1)) / y
                          ≤ 44 * Real.exp y * Real.exp (-2 * (y + 1)) := by
    rw [ div_le_iff₀ (by positivity) ] at *;
    nlinarith [ Real.exp_pos ( -2 * ( y + 1 ) ) ];
  convert h_combined using 1;
  · exact if_neg hy.not_ge;
  · rw [ mul_assoc, ← Real.exp_add ] ; ring_nf

/-
Main bound: tweedieReal y ≤ 44 * exp(-|y|) for all y.
-/
lemma tweedieReal_le_bound (y : ℝ) :
    tweedieReal y ≤ 44 * rexp (-|y|) := by
  by_cases hy : y ≤ 0;
  · exact le_trans ( tweedieReal_eq_zero_of_nonpos hy |> le_of_eq ) ( by positivity );
  · rw [ abs_of_pos ( not_le.mp hy ) ]
    exact le_trans ( tweedieReal_le_bound_pos (not_le.mp hy))
      ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by linarith ) ) ( by norm_num ) ) ;

/-
The bounding function `44 * exp(-|y|)` is integrable.
-/
lemma bound_integrable : Integrable (fun y : ℝ => 44 * rexp (-|y|)) volume := by
  have h_integrable : ∫ y : ℝ, Real.exp (-|y|) = 2 := by
    -- We can split the integral into two parts: one over $(-\infty, 0)$ and one over $(0, \infty)$.
    have h_split : ∫ (y : ℝ), Real.exp (-|y|)
                = (∫ (y : ℝ) in Set.Iic 0, Real.exp (-|y|))
                + (∫ (y : ℝ) in Set.Ioi 0, Real.exp (-|y|)) := by
      rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
      · exact MeasureTheory.integrable_of_integral_eq_one
          (by rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun x hx => by
            rw [ abs_of_nonpos hx.out ] ] ; simpa using integral_exp_Iic_zero );
      · exact MeasureTheory.integrable_of_integral_eq_one ( by
          rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by
            rw [ abs_of_pos hx.out ] ] ; simpa using integral_exp_neg_Ioi_zero );
    rw [ h_split, MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun x hx => by
      rw [ abs_of_nonpos hx.out ],
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx.out]]
    norm_num [ integral_exp_Iic, integral_exp_neg_Ioi ];
  exact MeasureTheory.Integrable.const_mul ( by exact ( by
    contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num ) ) _

/-
tweedieReal is AEStronglyMeasurable.
-/
lemma tweedieReal_aestronglyMeasurable :
    AEStronglyMeasurable tweedieReal volume := by
  apply Measurable.aestronglyMeasurable
  apply measurable_of_tendsto_metrizable _ _
  · use fun n => fun y => if y ≤ 0 then 0 else
      (∑ j ∈ Finset.range ( n + 1 ), tweedieTerm j y ) * Real.exp ( -2 * ( y + 1 ) ) / y;
  · intro i;
    apply Measurable.ite ( measurableSet_Iic ) measurable_const _;
    apply Measurable.mul _ _;
    · exact Measurable.mul ( Finset.measurable_sum _ fun j _ => by
        unfold tweedieTerm
        split_ifs <;> [
            exact measurable_const;
            exact Measurable.div_const
              ( measurable_id'.pow_const _ |> Measurable.mul <| measurable_const ) _ ] )
              ( Real.continuous_exp.measurable.comp
              <| measurable_const.mul <| measurable_id'.add_const _ );
    · exact measurable_id.inv;
  · apply tendsto_pi_nhds.mpr _;
    intro x; by_cases hx : x ≤ 0 <;> simp only [hx, ↓reduceIte, tweedieReal,
      tendsto_const_nhds_iff];
    exact Filter.Tendsto.div_const ( Filter.Tendsto.mul ( Summable.hasSum
      ( tweedieTerm_summable ( le_of_not_ge hx ) ) |> HasSum.tendsto_sum_nat |>
        Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ ) tendsto_const_nhds ) _

/-- The Tweedie density is integrable with respect to Lebesgue measure. -/
theorem tweedieReal_integrable : Integrable tweedieReal volume := by
  apply Integrable.mono' bound_integrable tweedieReal_aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (tweedieReal_nonneg y)]
  exact tweedieReal_le_bound y

-- Now the user's original ENNReal version

lemma tweedie_nonneg
    {y : ℝ} (h : 0 ≤ y) :
     0 ≤ (∑' (j : ℕ), if j = 0 then 0 else y ^ j * 4 ^ j / (↑j.factorial * Gamma ↑j))
     * rexp (-2 * (y + 1)) / y := by
        refine div_nonneg ?_ h
        apply mul_nonneg
        · refine tsum_nonneg ?_
          intro i
          split_ifs with g₀
          · simp
          · apply div_nonneg
            · apply mul_nonneg
              · apply pow_nonneg h
              · simp
            · apply mul_nonneg
              · simp
              · refine Gamma_nonneg_of_nonneg ?_
                simp
        · exact exp_nonneg _

/-- The Tweedie density as an ENNReal-valued function. -/
noncomputable def tweedieDensity (y : ℝ) : ℝ≥0∞ :=
  dite (y < 0) (fun _ => 0)
    fun h => ENNReal.ofNNReal ⟨(∑' (j : ℕ),
        if j = 0 then 0 else y ^ j * 4 ^ j / (↑j.factorial * Gamma ↑j)) * rexp (-2 * (y + 1)) / y,
        tweedie_nonneg (by rw [not_lt] at h; exact h)⟩

/-
The ENNReal Tweedie density has finite integral (equivalent to integrability).
-/
theorem tweedieDensity_lintegral_lt_top : ∫⁻ y, tweedieDensity y ∂volume < ⊤ := by
  convert lt_of_le_of_lt
    ( MeasureTheory.lintegral_mono fun y => ?_ )
    ( MeasureTheory.Integrable.lintegral_lt_top ( tweedieReal_integrable ) ) using 1;
  unfold tweedieDensity tweedieReal;
  split_ifs
  · simp
  · simp
  · simp_all
    norm_num [ show y = 0 by linarith ]
    rfl
  · convert le_rfl
    · simp;rfl
    · simp_all only [not_le, tweedieTerm, neg_mul]
      exact ENNReal.ofReal_eq_coe_nnreal
        (div_nonneg ( mul_nonneg ( tsum_nonneg fun _ => by positivity )
        (Real.exp_nonneg _)) (by positivity))

end
