import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import CramerLundberg.TweedieDensity
import Mathlib.MeasureTheory.Measure.WithDensity

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
def tweediePDF (μ φ p y : ℝ) :=
  a y φ p * Real.exp (1 / φ * (y * μ ^ ( 1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)))

open NNReal

/-- June 2, 2026. Nonnegativity of the Tweedie PDF. -/
lemma tweediePDF_nonneg {y μ φ p : ℝ} (hφ : 0 ≤ φ)
  (hp₁ : 1 < p) (hp₂ : p ≤ 2)
  (hy : 0 ≤ y) : tweediePDF μ φ p y ≥ 0 := by
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


def tweediePDF' (μ : ℝ) {φ p : ℝ}
    (hp₁ : 1 < p) (hp₂ : p ≤ 2)
    (hφ : 0 ≤ φ) (y : ℝ) : ℝ≥0∞:=
  dite (y < 0) (fun _ => 0)
  (by
    intro hy
    let nn : NNReal := (⟨tweediePDF μ φ p y, by
        apply tweediePDF_nonneg hφ hp₁ hp₂
        linarith⟩ : NNReal)
    exact (nn : ENNReal))


-- R error: `μ` must be positive
-- Also, `tweediePDF'` is still not a PDF since it's integral is < 1


/-- Probability of zero according to Tweedie distribution. -/
def tweedie_prob_zero (μ φ p : ℝ) : ℝ≥0 :=
    ⟨rexp (-μ ^ ( 2 - p) / (φ * (2 - p))), exp_nonneg _⟩

lemma tweedie_prob_zero_le_one (μ φ p : ℝ) (hμ : 0 ≤ μ)
    (hφ : 0 ≤ φ)
    (hp₂ : p ≤ 2) :
    tweedie_prob_zero μ φ p ≤ 1 := by
  unfold tweedie_prob_zero
  refine exp_le_one_iff.mpr ?_
  ring_nf
  simp only [Left.neg_nonpos_iff]
  apply mul_nonneg
  · apply rpow_nonneg hμ
  · simp only [inv_nonneg, le_neg_add_iff_add_le, add_zero]
    nth_rw 1 [mul_comm]
    apply mul_le_mul_of_nonneg_left hp₂ hφ

/--
June 2, 2026.
Tweedie distribution (should be a probability measure
if we have set it up right). -/
def tweedieMeasure (μ : ℝ) {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2) : Measure ℝ :=
    (tweedie_prob_zero μ φ p) • (Measure.dirac 0)
    + (volume.withDensity (tweediePDF' μ hp₁ hp₂ hφ))

/-- This is forced to be a probability measure.
However, I believe that `tweedieMeasure = tweedieMeasure'`.
-/
def tweedieMeasure' (μ : ℝ) {φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2) : Measure ℝ :=
    (tweedie_prob_zero μ φ p) • (Measure.dirac 0)
    + (1 - tweedie_prob_zero μ φ p) •
        (1 / ∫⁻ y, tweediePDF' μ hp₁ hp₂ hφ y) • (volume.withDensity (tweediePDF' μ hp₁ hp₂ hφ))



lemma tweedieMeasure_zero {μ φ p : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2) :
    tweedieMeasure μ hφ hp₁ hp₂ {0} = tweedie_prob_zero μ φ p := by
  unfold tweedieMeasure
  simp

lemma tweedieMeasure_nonzero {μ φ p x : ℝ} (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2) (hx : x ≠ 0) :
    tweedieMeasure μ hφ hp₁ hp₂ {x} = 0 := by
  unfold tweedieMeasure
  simp [Pi.single, Function.update]
  tauto




/-- Like a gamma distribution, Tweedie starts at the origin.
-/
lemma tweediePDF_zero (μ φ p : ℝ) : tweediePDF μ φ p 0 = 0 := by
  unfold tweediePDF
  simp
  ring_nf
  unfold a
  simp

lemma tweediePDF_one₁ {y μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1) (hp : p = 3 / 2)
  : tweediePDF μ φ p y =
    (∑' (j : ℕ), y^j * 4 ^ j / (↑j.factorial * Gamma ↑j)) * rexp (-2 * (y + 1)) / y
     -- so now we can prove this is ≤ 1
     := by
  subst μ φ p
  unfold tweediePDF a
  simp
  ring_nf
  field_simp
  simp_rw [← Gamma_nat_eq_factorial]
  congr
  ext j
  simp
  ring_nf
  field_simp
  by_cases H : Gamma j = 0
  · rw [H];simp
  generalize Gamma j = G at *
  field_simp
  have : (4 : ℝ) = 2 * 2 := by norm_num
  rw [this]
  field_simp
  rw [pow_mul]
  generalize y ^ j = A
  rw [← pow_mul]
  rw [pow_mul']

lemma tweediePDF_one₁₁ {μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1)
    (hp : p = 3 / 2) (y : ℝ) : tweediePDF μ φ p y =
    (∑' (j : ℕ), ite (j=0) 0 (y^j * 4 ^ j / (↑j.factorial * Gamma ↑j)))
    * rexp (-2 * (y + 1)) / y := by
  rw [tweediePDF_one₁]
  all_goals try tauto
  congr
  ext j
  split_ifs with g₀
  · subst j
    simp
  · rfl

lemma tweediePDF'_one₁₁_nonneg
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

/-- June 3, 2026. This gives an explicit form of a PDF,
which Aristotle can probably show is Integrable. -/
lemma tweediePDF'_one₁₁ {μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1) (hp : p = 3 / 2) (y : ℝ) :
    tweediePDF' μ (show 1 < p by linarith) (show p ≤ 2 by linarith) (show 0 ≤ φ by linarith) y =
    dite (y < 0) (fun _ => 0)
    fun h => ENNReal.ofNNReal ⟨(∑' (j : ℕ),
        if j = 0 then 0 else y ^ j * 4 ^ j / (↑j.factorial * Gamma ↑j)) * rexp (-2 * (y + 1)) / y,
        tweediePDF'_one₁₁_nonneg (by rw [not_lt] at h; exact h)⟩ := by
  unfold tweediePDF'
  simp only [neg_mul]
  split_ifs with g₀
  · rfl
  · subst μ φ p
    simp_rw [tweediePDF_one₁₁]
    simp



-- lemma tweediePDF_one₁₁integral {y μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1) (hp : p = 3 / 2)
--   : Integrable (tweediePDF μ φ p) := by
--   change Integrable (fun y => tweediePDF μ φ p y)
--   have := @tweediePDF_one₁₁ μ φ p hμ hφ hp
--   simp_rw [this]
--   clear hμ hp hφ this p φ μ y
--   zorry


/-- We can set mean μ = 0, dispersion φ = 1, and p = 3 / 2 -/
lemma tweediePDF_one_one {y μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF μ φ p y =
     (∑' (j : ℕ), 4 ^ j / (↑j.factorial * Gamma ↑j)) * rexp (-4)
     -- so now we can prove this is ≤ 1
     := by
  subst μ φ p y
  unfold tweediePDF a
  simp
  ring_nf
  field_simp
  simp_rw [← Gamma_nat_eq_factorial]
  congr
  ext j
  simp
  ring_nf
  field_simp
  by_cases H : Gamma j = 0
  · rw [H];simp
  generalize Gamma j = G at *
  field_simp
  have : (4 : ℝ) = 2 * 2 := by norm_num
  rw [this]
  field_simp
  rw [mul_comm]
  exact pow_mul 2 2 j


/-- We can set mean μ = 0, dispersion φ = 1, and p = 3 / 2 -/
lemma tweediePDF_one {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF μ φ p y =
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
  simp only [Real.rpow_natCast, one_pow, one_div, rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow,
    inv_inv, one_mul]
  congr
  ext j
  have : (4 : ℝ) = 2 * 2 := by ring_nf
  rw [this]
  split_ifs with g₀
  · subst j
    simp
  obtain ⟨k,hk⟩ : ∃ k, j = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero g₀
  subst j
  simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
  rw [Gamma_nat_eq_factorial]
  ring_nf
  field_simp
  rw [this, mul_pow, pow_mul]
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
        simp only [Nat.one_le_cast]
        refine Nat.one_le_iff_ne_zero.mpr ?_
        exact Nat.factorial_ne_zero (j - 1)
      · exact summable_pow_div_factorial 4


lemma tweediePDF_one' {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF μ φ p y > 0 := by
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


-- lemma tweediePDF_upper_bound' {y μ φ p : ℝ} (hμ : μ = 1) (hφ : φ = 1) (hp : p = 3 / 2)
--   (hy : y = 1) : tweediePDF μ φ p y ≤ 1 := by
--   rw [tweediePDF_one_one]
--   all_goals try tauto
--   suffices (∑' (j : ℕ), 4 ^ j / (↑j.factorial * Gamma ↑j)) ≤ rexp 4 by
--     have (a b : ℝ) (h : a ≤ rexp b) : a * rexp (-b) ≤ 1 := by
--       zorry
--     apply this
--     apply le_trans (b :=  ∑' (j : ℕ), (4:ℝ) ^ j / (↑j.factorial))
--     · refine Summable.tsum_mono ?_ ?_ ?_
--       · zorry
--       · zorry
--       · zorry
--     · apply le_of_eq
--       -- see below
--       zorry
--   zorry



lemma tweediePDF_upper_bound {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF μ φ p y ≤ rexp 4 := by
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
            · simp only [Nat.cast_pos]
              exact Nat.factorial_pos i
            · simp only [Nat.cast_pos]
              exact Nat.factorial_pos _
          · simp only [Nat.cast_pos]
            exact Nat.factorial_pos i
          · have : 0 < (4:ℝ)^i := by simp
            have : 0 < (i.factorial : ℝ) := by
                simp only [Nat.cast_pos];exact Nat.factorial_pos i
            have : 1 ≤ ((i-1).factorial : ℝ) := by
              simp only [Nat.one_le_cast]
              refine Nat.one_le_iff_ne_zero.mpr ?_
              exact Nat.factorial_ne_zero (i - 1)
            generalize (4:ℝ)^i = A at *
            generalize (i.factorial : ℝ) = B at *
            generalize ((i-1).factorial : ℝ) = C at *
            rw [← mul_assoc]
            have : 0 < A * B := by
                apply mul_pos <;> tauto
            generalize A * B = D at *
            apply le_trans
            · change D ≤ D * 1
              simp
            apply (mul_le_mul_iff_of_pos_left this).mpr
            linarith
      apply Summable.sum_le_tsum
      · simp only [Finset.mem_range, not_lt]
        intros
        apply div_nonneg <;> simp
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
      simp only
      ext n
      simp
      rw [mul_comm]
      exact div_eq_mul_inv _ _
    specialize h 4
    exact h



-- lemma tweediePDF_integral {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
--   (hy : y = 1) : 0 < ∫ y in Set.Ici 0, tweediePDF y μ φ p := by
--   unfold tweediePDF a
--   simp

--   zorry

/-- A very specific estimate for the Tweedie distribution. -/
lemma tweediePDF_nineteen {y μ φ p : ℝ} (hμ : μ = 0) (hφ : φ = 1) (hp : p = 3 / 2)
  (hy : y = 1) : tweediePDF μ φ p y ≥ 19 + 1/9 := by
  have := Summable.sum_le_tsum {1,2,3,4,5} (by intros; positivity) tweedie_one_summable
  simp at this
  rw [tweediePDF_one]
  all_goals try tauto
  linarith


theorem friday.extracted_1 {y : ℝ} (h : ¬y < 0) :
    0 ≤ (y⁻¹ * ∑' (j : ℕ), y ^ j * (1 / 2) ^ (-(j:ℝ)) * (↑j.factorial)⁻¹
    * (Gamma ↑j)⁻¹ * (1 / 2)⁻¹ ^ j) * rexp 0 := by
    simp only [one_div, rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow, inv_inv, exp_zero,
      mul_one]
    apply mul_nonneg
    · rw [inv_nonneg]
      linarith
    apply tsum_nonneg
    intro i
    repeat apply mul_nonneg
    apply pow_nonneg
    linarith
    simp
    simp
    simp
    apply Gamma_nonneg_of_nonneg
    simp
    simp

theorem friday :
    Function.support (fun y ↦
      if h : y < 0 then 0 else ENNReal.ofNNReal
      ⟨(y⁻¹ * ∑' (j : ℕ), y ^ ↑j * (1 / 2) ^ (-(j:ℝ)) * (↑j.factorial)⁻¹ *
      (Gamma ↑j)⁻¹ * (1 / 2)⁻¹ ^ j) * rexp 0, friday.extracted_1 h⟩) =
    Ioi 0 := by
        ext x
        simp only [one_div, rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow,
          inv_inv, exp_zero, mul_one, Function.mem_support, ne_eq, dite_eq_left_iff, not_lt,
          ENNReal.coe_eq_zero, not_forall, mem_Ioi]
        constructor
        · intro ⟨h,hh⟩
          contrapose! hh
          have : x = 0 := le_antisymm hh h
          subst x
          simp;rfl
        · intro h
          use (by linarith)
          intro hc
          have {a : ℝ} {ha : 0 ≤ a} (h : (⟨a, ha⟩ : NNReal) = 0) :
            a = 0 := (Nonneg.mk_eq_zero ha).mp h
          specialize this hc
          simp only [mul_eq_zero, inv_eq_zero] at this
          cases this with
          | inl h => linarith
          | inr h =>
            revert h
            simp only [imp_false]
            apply ne_of_gt
            apply lt_of_lt_of_le
            · change 0 <
                x ^ 1 * 2 ^ 1 * ((Nat.factorial 1) : ℝ)⁻¹ * (Gamma 1)⁻¹ * 2 ^ 1
              simp
              tauto
            have (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (h : Summable f):
                f 1 ≤ ∑' i, f i := by
                    refine Summable.le_tsum ?_ 1 fun j a ↦ hf j
                    tauto
            specialize this (f := fun j =>  x ^ j * 2 ^ j * (↑j.factorial)⁻¹ * (Gamma ↑j)⁻¹ * 2 ^ j)
                (by
                    intro i
                    simp only [Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right]
                    repeat apply mul_nonneg
                    · apply pow_nonneg
                      linarith
                    · simp
                    · simp
                    simp only [inv_nonneg]
                    refine Gamma_nonneg_of_nonneg ?_
                    simp)
            convert this
            simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, mul_one, Gamma_one,
              ge_iff_le, Classical.imp_iff_left_iff]
            left
            apply Summable.of_nonneg_of_le
              (f := fun i ↦ (4 * x) ^ i / (↑i.factorial))
            · intro b
              repeat apply mul_nonneg
              · apply pow_nonneg
                linarith
              · simp
              · simp
              · apply inv_nonneg.mpr;apply Gamma_nonneg_of_nonneg;simp
              · simp
            · intro b
              ring_nf
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
              rw [pow_mul' 2 b 2]
              suffices x ^ b * (↑b.factorial)⁻¹ * (Gamma ↑b)⁻¹
                     ≤ x ^ b * (↑b.factorial)⁻¹ by
                have h : 0 ≤ ((2:ℝ) ^ 2) ^ b := by
                    apply pow_nonneg
                    simp
                apply mul_le_mul_of_nonneg_right this h
              have hxb : x ^ b * (b.factorial : ℝ)⁻¹ > 0 := by
                apply mul_pos (pow_pos h _)
                apply inv_pos.mpr
                simp
                exact Nat.factorial_pos b
              by_cases hb : b = 0
              · subst b
                simp
              have : (Gamma b)⁻¹ ≤ 1 := by
                refine (inv_le_one₀ ?_).mpr ?_
                refine Gamma_pos_of_pos ?_
                simp
                omega
                suffices 1 ≤ ((b-1).factorial : ℝ) by
                    convert this
                    rfl
                    rw [← Gamma_nat_eq_factorial]
                    congr
                    cases b with
                    | zero => simp at hb
                    | succ n => simp
                simp
                exact Nat.one_le_iff_ne_zero.mpr <| Nat.factorial_ne_zero _
              rw [mul_le_iff_le_one_right]
              · exact this
              · exact hxb
            apply summable_pow_div_factorial



theorem tweedieMeasure'_isProbabilityMeasure.nonzero₁ {μ φ p : ℝ}
    (hμ : 0 ≤ μ) (hφ : 0 ≤ φ) (hp₁ : 1 < p) (hp₂ : p ≤ 2)
    (hμ' : μ = 1) (hφ' : φ = 1) (hp' : p = 3 / 2) :
    ∫⁻ (y : ℝ), tweediePDF' μ hp₁ hp₂ hφ y ≠ 0 := by
        apply ne_of_gt
        unfold tweediePDF' tweediePDF a
        subst μ φ p
        simp
        ring_nf
        refine (lintegral_pos_iff_support ?_).mpr ?_
        · show Measurable fun y ↦
            dite (y ∈ Set.Iio 0) (fun _ => (0 : ENNReal)) _
          have := @Measurable.dite ℝ ENNReal (Set.Iio 0) (Real.measurableSpace)
            (ENNReal.measurableSpace) (by intro x;simp;exact x.decidableLT 0;)
            (fun _ => 0) (by simp)
            (fun hy => ENNReal.ofNNReal ⟨(hy.1⁻¹ *
                ∑' (j : ℕ), hy ^ j * 2 ^ j * (↑j.factorial)⁻¹
                * (Gamma ↑j)⁻¹ * 2 ^ j) *  rexp (-2 - hy.1 * 2), by
                repeat apply mul_nonneg
                have := hy.2
                simp at this ⊢
                tauto
                apply tsum_nonneg
                intro i
                repeat apply mul_nonneg
                apply pow_nonneg
                have := hy.2
                simp at this
                tauto
                simp
                simp
                simp
                apply Gamma_nonneg_of_nonneg
                simp
                simp
                apply le_of_lt
                exact exp_pos (-2 - ↑hy * 2)⟩)
              (by
                simp only [measurable_coe_nnreal_ennreal_iff]
                apply Measurable.subtype_mk
                apply Measurable.mul
                · apply Measurable.mul
                  · simp only [measurable_inv_iff];exact measurable_subtype_coe
                  · apply Measurable.tsum -- after updating to 4.30
                    intro i
                    repeat apply Measurable.mul
                    refine Measurable.pow_const measurable_subtype_coe i
                    all_goals simp
                refine Measurable.exp ?_
                refine Measurable.add ?_ ?_
                simp
                simp
                apply Measurable.mul
                exact measurable_subtype_coe
                simp
                  )
                  (by simp)
          convert this
          rfl
          simp
        have : 0 < volume (Set.Ioi (0 : ℝ)) := by simp
        convert this
        rw [← friday]
        all_goals try tauto
        ext y
        simp
        have hnn (h : 0 ≤ y) :  0 ≤ y⁻¹ * ∑' (j : ℕ), y ^ j * 2 ^ j * (↑j.factorial)⁻¹ * (Gamma ↑j)⁻¹ * 2 ^ j
            := by
            repeat apply mul_nonneg
            simp
            tauto
            apply tsum_nonneg
            intro i
            repeat apply mul_nonneg
            apply pow_nonneg
            tauto
            simp
            simp
            simp
            apply Gamma_nonneg_of_nonneg
            simp
            simp
        have mk {a : ℝ} (ha : 0 ≤ a) (h : ⟨a,ha⟩ = (0 : NNReal)) :
            a = 0 := (Nonneg.mk_eq_zero ha).mp h
        constructor
        · intro ⟨h,hh⟩
          constructor
          · intro hc
            apply hh
            have : y⁻¹ * ∑' (j : ℕ), y ^ j * 2 ^ j * (↑j.factorial)⁻¹ * (Gamma ↑j)⁻¹ * 2 ^ j = 0 := by
                apply mk (hnn h) hc
            simp_rw [this]
            simp
            congr
          · tauto
        · intro ⟨h,hh⟩
          use h
          contrapose! hh
          have := mk (by
            apply mul_nonneg
            exact hnn h
            apply exp_nonneg) hh
          simp at this
          cases this with
          | inl h => subst y;simp;congr
          | inr h =>
            simp_rw [h]
            simp
            congr

/-- June 5, 2026.
-/
lemma tweedieMeasure'_isProbabilityMeasure {μ φ p : ℝ} (hμ : 0 ≤ μ) (hφ : 0 ≤ φ)
    (hp₁ : 1 < p) (hp₂ : p ≤ 2)
    (hμ' : μ = 1)
    (hφ' : φ = 1)
    (hp' : p = 3 / 2) :
    IsProbabilityMeasure
        (tweedieMeasure' μ hφ hp₁ hp₂) := by
    refine isProbabilityMeasure_iff.mpr ?_
    unfold tweedieMeasure'
    simp only [one_div, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, ENNReal.smul_one, MeasurableSet.univ, withDensity_apply, Measure.restrict_univ,
      smul_eq_mul]
    have ht : tweedie_prob_zero μ φ p ≤ 1 := tweedie_prob_zero_le_one μ φ p hμ hφ hp₂
    generalize tweedie_prob_zero μ φ p = α at *
    have hi₀ :  ∫⁻ (y : ℝ), tweediePDF' μ hp₁ hp₂ hφ y ≠ 0 := by
        apply tweedieMeasure'_isProbabilityMeasure.nonzero₁ <;> tauto
    have hi₁ :  ∫⁻ (y : ℝ), tweediePDF' μ hp₁ hp₂ hφ y ≠ ∞ := by
        subst μ φ p
        apply ne_of_lt
        convert tweedieDensity_lintegral_lt_top -- Aristotle
        unfold tweedieDensity tweediePDF' tweediePDF a
        simp
        ring_nf
        ext y
        split_ifs with g₀
        · rfl
        · simp
          ring_nf
          simp_rw [mul_assoc]
          simp_rw [mul_comm]
          congr
          ext j
          split_ifs with g₀
          · subst j;simp
          · simp;left;left;left
            have : (4 : ℝ) = 2 ^ 2 := by norm_num
            rw [this]
            rw [mul_comm]
            exact pow_mul 2 2 j
    rw [ENNReal.inv_mul_cancel hi₀ hi₁]
    simp only [ENNReal.smul_one, ENNReal.coe_sub, ENNReal.coe_one]
    refine add_tsub_cancel_of_le ?_
    convert ht
    simp

-- Aristotle:
theorem measurable_dite_withDensity_comap
    (f : { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } → ℝ → ENNReal)
    (hf : Measurable (Function.uncurry f)) :
    @Measurable { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 }
    (ℝ → ENNReal) Subtype.instMeasurableSpace
    (MeasurableSpace.comap volume.withDensity Measure.instMeasurableSpace)
    (fun x y ↦ if h : y < 0 then 0 else f x y) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Function.comp, withDensity_apply _ hs]
  apply Measurable.lintegral_prod_right
  apply Measurable.ite
  · exact measurableSet_lt measurable_snd measurable_const
  · exact measurable_const
  · exact hf


/-- June 7, 2026.
A specific subfamily of Tweedie distributions as a Kernel.
-/
def Tweedie : @ProbabilityTheory.Kernel (ℝ) ℝ _ Real.measurableSpace := {
            toFun :=
              fun μ => @tweedieMeasure μ 1 (3 / 2) (by simp) (by linarith) (by linarith)
            measurable' := by
                unfold tweedieMeasure
                apply Measurable.add
                · refine Measurable.smul_measure ?_ (Measure.dirac 0)
                  unfold tweedie_prob_zero
                  measurability
                · apply measurable_withDensity
                  change Measurable fun z : ℝ × ℝ ↦ if h : z ∈ {z : ℝ × ℝ | z.2 < 0} then 0 else _
                  ring_nf
                  have := @Measurable.dite (ℝ × ℝ) ENNReal {a : ℝ × ℝ | a.2 < 0}
                    Prod.instMeasurableSpace ENNReal.measurableSpace
                    (fun _ => decidableSetOf _ _) (fun _ => (0 : ENNReal)) (by simp)
                    (fun z => ENNReal.ofNNReal ⟨a z.1.2 1 (3 / 2) *
                        rexp (-(z.1.2 * z.1.1 ^ (-(1 : ℝ) / 2) * 2) - z.1.1 ^ ((1:ℝ) / 2) * 2), by
                                repeat apply mul_nonneg
                                · simp
                                · rw [inv_nonneg]
                                  apply le_of_not_gt
                                  convert z.2
                                  simp
                                · apply tsum_nonneg
                                  intro i
                                  repeat apply mul_nonneg
                                  · ring_nf
                                    rw [Real.rpow_natCast]
                                    apply pow_nonneg
                                    apply le_of_not_gt
                                    convert z.2
                                    simp
                                  · ring_nf
                                    simp
                                  simp
                                  ring_nf
                                  repeat apply mul_nonneg
                                  · rw [inv_nonneg]
                                    apply Gamma_nonneg_of_nonneg
                                    simp
                                  · simp
                                  · simp
                                · exact exp_nonneg _
                                ⟩)
                    (by
                    simp only [one_div, measurable_coe_nnreal_ennreal_iff]
                    apply Measurable.subtype_mk;unfold a;measurability)
                    (by measurability)
                  unfold tweediePDF a
                  convert this
                  ext
                  ring_nf
                  apply congrArg
                  apply Subtype.mk.congr_simp
                  unfold a
                  rw [mul_comm (a := rexp _)]
                  have (a b c d : ℝ) (h₀ : a = b) (h₁ : c = d) : a * c = b * d := by
                    have g₀ := congrArg (fun x => b * x) h₁
                    have g₁ := congrArg (fun x => x * c) h₀
                    apply Eq.trans g₁ g₀
                  apply this
                  · ring_nf
                    field_simp
                  · field_simp
    }
    -- have Tweedie : @ProbabilityTheory.Kernel (ℝ × ℝ × ℝ) ℝ
    --     Prod.instMeasurableSpace Real.measurableSpace := {
    --         toFun := by
    --             intro x
    --             by_cases hx : x ∈ {⟨μ, φ, p⟩ | 0 ≤ μ ∧ 1 < p ∧ p ≤ 2}
    --             · exact tweedieMeasure x.1 hx.1 hx.2.1 hx.2.2
    --             · exact Measure.dirac 0
    --         measurable' := by
    --             have := @Measurable.dite
    --                 (s := {⟨μ, φ, p⟩ : ℝ × ℝ × ℝ | 0 ≤ μ ∧ 1 < p ∧ p ≤ 2})
    --                 (β := Measure ℝ)
    --                 (f := by
    --                     intro x
    --                     exact tweedieMeasure x.1.1 x.2.1 x.2.2.1 x.2.2.2)
    --                 (g := fun _ => Measure.dirac 0)
    --             simp at this ⊢
    --             apply this
    --             · unfold tweedieMeasure
    --               apply Measurable.add
    --               · refine Measurable.smul_measure ?_ (Measure.dirac 0)
    --                 simp
    --                 unfold tweedie_prob_zero
    --                 measurability
    --               · apply Measurable.fun_comp
    --                 · exact Measurable.of_comap_le fun s a ↦ a

    --                 unfold tweediePDF'
    --                 simp

    --                 have (f : { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } → ℝ → ENNReal)
    --                     (hf : Measurable (Function.uncurry f))
    --                     :
    --                     @Measurable { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 }
    --                     (ℝ → ℝ≥0∞) Subtype.instMeasurableSpace
    --                     (MeasurableSpace.comap volume.withDensity Measure.instMeasurableSpace)
    --                     fun x y ↦
    --                     if h : y < 0 then 0 else f x y := by
    --                   apply measurable_dite_withDensity_comap _ hf
    --                 specialize this (by
    --                   intro x y
    --                   exact ENNReal.ofNNReal ⟨tweediePDF (x.1).1 x.1.1 x.1.2.2 y, by sorry⟩)
    --                 apply this
    --                 unfold tweediePDF a
    --                 simp
    --                 apply Measurable.comp -- !!
    --                 exact Measurable.of_comap_le fun s a ↦ a
    --                 have {α : Type} [MeasurableSpace α]
    --                   (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    --                   (h : Measurable f) : Measurable fun x => (⟨f x, hf x⟩ : {x : ℝ // 0 ≤ x}) := by
    --                   exact Measurable.subtype_mk h
    --                 specialize @this ( { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ)
    --                   Prod.instMeasurableSpace

    --                 have (f :  { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ → ℝ)
    --                     (hf : ∀ x, 0 ≤ f x) (hm : @Measurable
    --                         ({ x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ) ℝ Prod.instMeasurableSpace
    --                         (MeasurableSpace.comap (by exact fun a ↦ ENNReal.ofReal a) ENNReal.measurableSpace) f)
    --                     : @Measurable
    --                     ({ x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ) { r // 0 ≤ r } Prod.instMeasurableSpace
    --                     (MeasurableSpace.comap ENNReal.ofNNReal ENNReal.measurableSpace) fun x => (⟨f x, hf x⟩ : {x : ℝ // 0 ≤ x}) := by
    --                     -- (MeasurableSpace.comap ENNReal.ofNNReal ENNReal.measurableSpace)
    --                     clear this
    --                     clear this
    --                     clear this

    --                     sorry
    --                     --exact Measurable.subtype_mk hm
    --                 show @Measurable
    --                     ({ x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ) { r // 0 ≤ r } Prod.instMeasurableSpace
    --                     (MeasurableSpace.comap ENNReal.ofNNReal ENNReal.measurableSpace) _
    --                 apply this
    --                 have := @Measurable.mul ℝ ({ x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 } × ℝ)
    --                     (by exact (MeasurableSpace.comap (fun a ↦ ENNReal.ofReal a) ENNReal.measurableSpace)) _
    --                     (Prod.instMeasurableSpace)
    --                     (fun x => (x.2⁻¹ *
    --                         ∑' (j : ℕ),
    --                             x.2 ^ (-((j:ℝ) * ((2 - (x.1.1).2.2) / (1 - (x.1.1).2.2)))) *
    --                                 ((x.1.1).2.2 - 1) ^ ((2 - (x.1.1).2.2) / (1 - (x.1.1).2.2) * ↑j) /
    --                             ((x.1.1).1 ^ (↑j * (1 - (2 - (x.1.1).2.2) / (1 - (x.1.1).2.2))) * (2 - (x.1.1).2.2) ^ j * ↑j.factorial *
    --                                 Gamma (-(↑j * ((2 - (x.1.1).2.2) / (1 - (x.1.1).2.2)))))))
    --                     (fun x => rexp
    --                         ((x.1.1).1⁻¹ *
    --                             (x.2 * (x.1.1).1 ^ (1 - (x.1.1).2.2) / (1 - (x.1.1).2.2) - (x.1.1).1 ^ (2 - (x.1.1).2.2) / (2 - (x.1.1).2.2))))
    --                     (by

    --                     sorry) (by sorry) (by sorry)
    --                 apply this
    --                 -- apply Measurable.mul
    --                 -- apply this
    --                 -- refine measurable_uncurry_of_continuous_of_measurable ?_ ?_
    --                 -- intro x
    --                 -- refine ENNReal.continuous_coe_iff.mpr ?_
    --                 -- apply Continuous.subtype_mk
    --                 -- apply Continuous.mul
    --                 -- apply Continuous.mul
    --                 -- exact continuous_const
    --                 -- have : Continuous fun x : ℝ => ∑' n : ℕ, x^ n / n.factorial := by
    --                 --   sorry
    --                 -- sorry
    --                 -- sorry
    --                 -- intro ⟨(μ,φ,p),h₀,h₁⟩
    --                 -- simp at h₀ h₁ ⊢
    --                 -- apply?
    --                 -- have (f : ℝ → ℝ → ℝ) (hf : Measurable fun p : ℝ × ℝ => f p.1 p.2) :
    --                 --     Measurable f := by
    --                 --   refine measurable_pi_lambda f ?_
    --                 --   intro a
    --                 --   exact Measurable.of_uncurry_right hf
    --                 -- have := @measurable_pi_lambda
    --                 --     { x : ℝ × ℝ × ℝ // 0 ≤ x.1 ∧ 1 < x.2.2 ∧ x.2.2 ≤ 2 }
    --                 --     ℝ (fun _ => ENNReal) _ _
    --                 --     (by
    --                 --         intro x y
    --                 --         exact if h : y < 0 then 0 else
    --                 --         ENNReal.ofNNReal ⟨tweediePDF (x.1).1 x.1.1 x.1.2.2 y, by
    --                 --             apply tweediePDF_nonneg
    --                 --             exact x.2.1
    --                 --             exact x.2.2.1
    --                 --             exact x.2.2.2
    --                 --             linarith⟩
    --                 --         )
    --                 --     (by sorry)
    --                 -- apply Measurable.mono this
    --                 -- simp
    --                 -- rw [← measurable_iff_comap_le]
    --                 -- apply?
    --                 -- apply measurable_withDensity

    --                 -- rw [MeasurableSpace.comap] at hS -- works
    --                 -- rw [← measurable_iff_comap_le] at hS


    --                 /-
    --                 @Eq

    --                 @MeasurableSpace.comap (ℝ → ℝ≥0∞) (Measure ℝ) ℙ.withDensity Measure.instMeasurableSpace : MeasurableSpace (ℝ → ℝ≥0∞)

    --                 (@MeasurableSpace.pi ℝ (fun x ↦ ℝ≥0∞) fun a ↦ ENNReal.measurableSpace : MeasurableSpace (ℝ → ℝ≥0∞))
    --                 -/
    --             · sorry
    --     }
