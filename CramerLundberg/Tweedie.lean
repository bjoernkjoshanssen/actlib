import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

/-!

# Tweedie distribution

Main results:
* `... (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :`
    `(Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}`
    `= some ⟨r / (r + s), by field_simp;linarith⟩`
    For two independent random variables `X~exponential(r)` and `Y~exponential(s)`,
    where `r` and `s` are the rates of occurrence (so `E(X)=1/r` and `E(Y)/1/s`)
    the probability that `X≤Y` is `r/(r+s)`.
    We interpret `X` as the loss incurred and `Y` as the capital accrued when the loss
    occurs. `Y` is proportional to time.

-/

noncomputable section
-- Tweedie distribution!

/-- The sum should exclude `j=0` but it's okay because
Real.Gamma 0 = 0 and 1 / 0 = 0 in Lean.
-/
def a (y φ p : ℝ) :=
  let α := (2 - p) / (1 - p)
  (1/y) * ∑' j : ℕ, (y ^ (- j * α) * (p - 1) ^(α * j)) /
  (φ ^ (j * (1 - α)) * (2 - p) ^ j * Nat.factorial j * Real.Gamma (- j * α))

/-- PDF for Tweedie distribution when `1 < p < 2` according to
https://stats.stackexchange.com/questions/552562/understanding-the-tweedie-distribution
Should maybe restrict to `y ≥ 0`?
-/
def tweediePDF (y μ φ p : ℝ) :=
  a y φ p * Real.exp (1 / φ * (y * μ ^ ( 1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)))


def tweediePDF' (y μ φ p : ℝ) :=
  ite (y < 0) 0
  tweediePDF y μ φ p



/-- Like a gamma distribution, Tweedie starts at the origin.
-/
lemma tweediePDF_zero (μ φ p : ℝ) : tweediePDF 0 μ φ p = 0 := by
  unfold tweediePDF
  simp
  ring_nf
  unfold a
  simp

/-- We can set mean μ = 0, dispersion φ = 1, and p = 3 / 2 -/
lemma tweediePDF_one {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p =
    ∑' j : ℕ, ite (j=0) 0 ((4:ℝ) ^ j / (j.factorial * (j-1).factorial)) := by
  -- x = 19.519
  -- x = ∑ 4 ^ j / (j! * (j-1)!)
  unfold tweediePDF
  subst μ φ p
  simp
  ring_nf
  unfold a
  simp
  ring_nf
  field_simp
  -- 2 I_1(4 √y) / √y, I_1 = modified Bessel of 1st kind
  subst y
  simp
  congr
  ext j
  congr
  have : (4 : ℝ) = 2 * 2 := by ring_nf
  rw [this]
  split_ifs with g₀
  subst j
  simp
  obtain ⟨k,hk⟩ : ∃ k, j = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero g₀
  subst j
  simp
  rw [Gamma_nat_eq_factorial]
  ring_nf
  field_simp
  rw [this]
  rw [mul_pow]
  rw [pow_mul]
  exact pow_two (2 ^ k)

lemma tweedie_one_summable :
  Summable fun i : ℕ ↦ if i = 0 then 0 else (4:ℝ) ^ i / (↑i.factorial * ↑(i - 1).factorial) := by
    apply Summable.of_nonneg_of_le
      (f := fun i ↦ 4 ^ i / (↑i.factorial * ↑(i - 1).factorial))
    · intro j
      positivity
    · intro j
      split_ifs with g₀
      · positivity
      · simp
    · apply Summable.of_nonneg_of_le
        (f := fun i ↦ 4 ^ i / (↑i.factorial))
      · intro j
        positivity
      · intro j
        ring_nf
        field_simp
        simp
        refine Nat.one_le_iff_ne_zero.mpr ?_
        exact Nat.factorial_ne_zero (j - 1)
      · exact summable_pow_div_factorial 4


lemma tweediePDF_one' {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p > 0 := by
  rw [tweediePDF_one]
  all_goals try tauto
  apply Summable.tsum_pos (i := 1)
  · simp
  · apply tweedie_one_summable
  · intro j
    split_ifs with g₀
    · simp
    · apply div_nonneg
      · simp
      · apply mul_nonneg <;> simp



lemma tweediePDF_one'' {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p ≥ 4 := by
  have := Summable.le_tsum (tweedie_one_summable) 1 (by
    intro j hj
    split_ifs with g₀
    · simp
    · positivity)
  simp at this
  rw [tweediePDF_one]
  all_goals tauto

lemma tweediePDF_one''' {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p ≥ 8 := by
  have := Summable.le_tsum (tweedie_one_summable) 2 (by
    intro j hj
    split_ifs with g₀
    · simp
    · positivity)
  simp at this
  rw [tweediePDF_one]
  linarith
  all_goals tauto

/-- A very specific estimate for the Tweedie distribution. -/
lemma tweediePDF_nineteen {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p ≥ 19 + 1/9 := by
  have := Summable.sum_le_tsum {1,2,3,4,5} (by intros; positivity) tweedie_one_summable
  simp at this
  rw [tweediePDF_one]
  all_goals try tauto
  linarith

lemma tweediePDF_upper_bound {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF y μ φ p ≤ rexp 4 := by
  rw [tweediePDF_one]
  all_goals try tauto
  apply le_trans (b :=  (∑' (j : ℕ), (4:ℝ) ^ j / (↑j.factorial)))
  · refine tsum_le_of_sum_range_le ?_ ?_
    · intro n
      split_ifs with g₀
      · simp
      · positivity
    · intro n
      apply le_trans
      · change _ ≤ (∑ i ∈ Finset.range n, (4:ℝ) ^ i / (↑i.factorial))
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with g₀
        · positivity
        · refine (div_le_div_iff₀ ?_ ?_).mpr ?_
          · apply mul_pos
            · simp
              exact Nat.factorial_pos i
            · simp
              exact Nat.factorial_pos _
          · simp
            exact Nat.factorial_pos i
          · have : 0 < (4:ℝ)^i := by simp
            have : 0 < (i.factorial : ℝ) := by simp;exact Nat.factorial_pos i
            have : 1 ≤ ((i-1).factorial : ℝ) := by
              simp;refine Nat.one_le_iff_ne_zero.mpr ?_
              exact Nat.factorial_ne_zero (i - 1)
            generalize (4:ℝ)^i = A at *
            generalize (i.factorial : ℝ) = B at *
            generalize ((i-1).factorial : ℝ) = C at *
            rw [← mul_assoc]
            have : 0 < A * B := by apply mul_pos;tauto;tauto
            generalize A * B = D at *
            apply le_trans
            change D ≤ D * 1
            simp
            apply (mul_le_mul_iff_of_pos_left this).mpr
            linarith
      apply Summable.sum_le_tsum
      · simp
        intros
        apply div_nonneg
        simp
        simp
      · apply summable_pow_div_factorial
  · apply le_of_eq
    suffices HasSum
       (fun (j : ℕ) => (4:ℝ) ^ j / ↑j.factorial) (rexp 4) by
        exact HasSum.tsum_eq this
    have h (x : ℝ) : HasSum (fun n : ℕ => x ^ n / n.factorial) (exp x) := by
      rw [exp_eq_exp_ℝ]
      have := @NormedSpace.exp_series_hasSum_exp' ℝ ℝ _ _ _ _ _ _ x
      convert this using 1
      ext n
      simp
      rw [mul_comm]
      exact div_eq_mul_inv _ _
    specialize h 4
    exact h


/-- June 2, 2026. Nonnegativity of the Tweedie PDF. -/
lemma tweediePDF_nonneg (y μ φ p : ℝ) (hφ : 0 ≤ φ)
  (hp₁ : 1 < p) (hp₂ : p ≤ 2)
  (hy : 0 ≤ y) : tweediePDF y μ φ p ≥ 0 := by
    unfold tweediePDF
    apply mul_nonneg
    · unfold a
      apply mul_nonneg
      · positivity
      · refine tsum_nonneg ?_
        intro j
        apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · apply rpow_nonneg
            linarith
        · simp only [neg_mul, mul_inv_rev]
          apply mul_nonneg
          · rw [inv_nonneg]
            refine Gamma_nonneg_of_nonneg ?_
            rw [mul_div, ← neg_div, ← neg_mul, mul_comm, ← mul_div]
            apply mul_nonneg
            · linarith
            suffices 0 ≤ j / (p - 1) by
              convert this using 1
              have : 1 - p ≠ 0 := by linarith
              have : p - 1 ≠ 0 := by linarith
              field_simp
              ring_nf
            apply mul_nonneg
            · simp
            · simp;linarith
          · apply mul_nonneg
            · simp
            · apply mul_nonneg
              · rw [inv_nonneg];apply pow_nonneg;linarith
              · rw [inv_nonneg];apply rpow_nonneg;linarith
    · exact Real.exp_nonneg _

-- lemma tweediePDF_integral {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
--   (hy : y = 1) : 0 < ∫ y in Set.Ici 0, tweediePDF y μ φ p := by
--   unfold tweediePDF a
--   simp

--   sorry
