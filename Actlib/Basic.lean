import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.ODE.Gronwall


/-!

## Financial Mathematis
Math 370
-/
open Finset

/-- The sum of a finite geometric series. -/
lemma sum_pow (n : ℕ) {x : ℝ} (hx : x ≠ 1) : ∑ i ∈ range n, x^i = (x ^ n - 1) / (x - 1) := by
  have hx : x - 1 ≠ 0 := sub_ne_zero_of_ne hx
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring_nf

theorem sum_pow_interest (n : ℕ) {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  ∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k - 1 = (1 - (1 + i)⁻¹ ^ n) / i :=
  .trans (congrArg (fun x => x-1) <| sum_pow (n+1)
    fun hc => hi <| left_eq_add.mp (inv_eq_one.mp hc).symm) (by grind)

namespace ann
/-!

# Section 2.4

This general theory of annuities is optional, i.e., not included in Exam FM.
-/
variable (acc : ℝ → ℝ)
-- accumulation function. Called `a` in namespace `interest` but as it is a primitive
-- the name is flexible.

/-- Present value of an annuity-immediate, general case.
We write the sum from 1 to n as a sum from 0 to n-1 by replacing `t` by `t+1`.
Although the PV of 1 varies continuously, only PV of 1 at integer times contribute to the PV of the annuity.
-/
noncomputable def a : ℕ → ℝ := fun n => Finset.sum (Finset.univ : Finset (Fin n))
    fun t => (1:ℝ) / acc (t.1+1)

/-- Present value of deferred (by `m` periods) annuity-immediate (with `n` installments), general case. -/
noncomputable def a_defer : ℕ → ℕ → ℝ := fun m n => Finset.sum (Finset.univ : Finset (Fin n))
    fun t => (1:ℝ) / acc (m + t.1+1)

/-- Present value of a continuous annuity, general case. -/
noncomputable def a_bar : ℝ → ℝ := fun n => ∫ t in 0..n,  (1:ℝ) / acc t

/-- Present value of a continuous annuity, general case. -/
noncomputable def s_bar : ℝ → ℝ := fun n => ∫ t in 0..n, acc (n - t)


/-- Present value of an annuity-due, general case. -/
noncomputable def a_dots : ℕ → ℝ := fun n => Finset.sum (Finset.univ : Finset (Fin n))
    fun t => (1:ℝ) / acc t.1

/-- Future value of an annuity, general case. -/
noncomputable def s : ℕ →  ℝ := fun n => Finset.sum (Finset.univ : Finset (Fin n))
    fun t => acc (n - (t.1+1))

local notation n "⌝" => n

end ann

/-- For "exponential" accumulation functions,
the dependence of the present value of the deferred annuity-immediate
upon `m` and `n` can be separated by multiplication `f m * g n`. -/
example (acc : ℝ → ℝ)
    (hacc: ∀ m n, acc (m + n) = acc m * acc n)
    (m n : ℕ) : ann.a_defer acc m n = (1 / acc m) * ann.a acc n := by
    unfold ann.a_defer ann.a
    simp_rw [hacc]
    simp_rw [mul_assoc]
    have : (fun x : Fin n => 1 / (acc ↑m * (acc ↑↑x * acc 1)))
        = fun x : Fin n => (1 / acc ↑m) * (1 / (acc ↑↑x * acc 1)) := by
      ext
      simp
      ring_nf
    simp_rw [this]
    rw [mul_sum univ]

/-- The exponential accumulation function is "nice". -/
example (i : ℝ) (hi : 0 < 1 + i):
    let acc := (fun t : ℝ => (1 + i) ^ t)
    ∀ m n, acc (m + n) = acc m * acc n := by
  intro acc
  unfold acc
  intro m n
  refine Real.rpow_add ?_ m n
  exact hi


/-- The present value of a continuous annuity under simple interest
is at most the future value.
-/

lemma present_value_continuous_annuity_simple_interest_le_future_value {r n : ℝ} (hr : 0 ≤ r)
    (hn : 0 ≤ n) :
    let acc := fun t => 1 + r * t
    ann.a_bar acc n ≤ ann.s_bar acc n := by
  intro acc
  unfold ann.a_bar ann.s_bar acc
  apply intervalIntegral.integral_mono_on_of_le_Ioo hn
  apply intervalIntegral.intervalIntegrable_one_div
  intro x hx
  simp
  have : 0 ≤ x := by
    have h₁ := hx.1
    have h₂ := hx.2
    simp at h₁ h₂
    cases h₁ with
    | inl h => tauto
    | inr h =>
        cases h₂ with
        | inl h =>
            have : n = 0 := by linarith
            subst this
            exact h
        | inr h => linarith
  positivity
  refine Continuous.comp_continuousOn' ?_ ?_
  exact continuous_add_left 1
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  refine Continuous.continuousAt ?_
  exact continuous_mul_left r

  apply IntervalIntegrable.add
  simp
  apply IntervalIntegrable.const_mul
  apply IntervalIntegrable.sub
  simp
  simp
  intro x hx
  simp at hx ⊢
  field_simp
  have hr₀ : 0 < 1 + r * x := by
    calc 0 < 1 := by simp
         _ ≤ 1 + r * x := by
            suffices 0 ≤ r * x by linarith
            apply mul_nonneg hr
            linarith
  suffices   1 ≤ (1 + r * (n - x)) * (1 + r * x) by
    exact (div_le_iff₀ hr₀).mpr this
  suffices  0 ≤  r * ↑n + (r ^ 2 * ↑n * x - r ^ 2 * x ^ 2) by
    linarith
  apply add_nonneg
  apply mul_nonneg
  tauto
  tauto
  suffices r ^ 2 * x ^ 2 ≤ r ^ 2 * ↑n * x by
    linarith
  rw [mul_assoc]
  suffices x ^ 2 ≤ (↑n * x) by
    refine mul_le_mul ?_ ?_ ?_ ?_
    simp
    rw [pow_two]
    suffices x ≤ (n:ℝ) by
        apply mul_le_mul
        convert this
        simp
        linarith
        tauto
    linarith
    positivity
    positivity

  rw [pow_two]
  suffices x ≤ n by
        apply mul_le_mul
        convert this
        simp
        linarith
        linarith
  linarith

/--
Under simple interest, the present value of an annuity-immediate is at most the
future value. -/
lemma present_value_annuity_simple_interest_le_future_value {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    let acc := fun t => 1 + r * t
    ann.a acc n ≤ ann.s acc n := by
  intro acc
  apply sum_le_sum
  intro i hi
  simp
  have hr₀ : 0 < 1 + r * (i.1+1) := by
    calc 0 < 1 := by simp
         _ ≤ 1 + r * (i.1+1) := by
            suffices 0 ≤ r * i.1 by linarith
            apply mul_nonneg hr
            simp
  field_simp
  suffices   1 ≤ (1 + r * (n - (i.1+1))) * (1 + r * (i.1+1)) by
    exact (div_le_iff₀ hr₀).mpr this
  ring_nf
  suffices  0 ≤  r * ↑n + (r ^ 2 * ↑n * (↑↑i+1) - r ^ 2 * (↑↑i+1) ^ 2) by
    linarith
  apply add_nonneg
  apply mul_nonneg
  tauto
  simp
  suffices r ^ 2 * (↑↑i+1) ^ 2 ≤ r ^ 2 * ↑n * (↑↑i+1) by
    linarith
  rw [mul_assoc]
  suffices (↑↑i+1) ^ 2 ≤ (↑n * (↑↑i+1)) by
    refine mul_le_mul ?_ ?_ ?_ ?_
    simp
    rw [pow_two]
    suffices i.1+1 ≤ (n:ℝ) by
        apply mul_le_mul
        convert this
        simp
        positivity
        simp
    have hi₂ := i.2
    norm_cast at *
    positivity
    positivity

  rw [pow_two]
  suffices i.1+1 ≤ n by
        apply mul_le_mul
        convert this
        simp
        positivity
        simp
  linarith [i.2]

namespace annuity

/-- The present value of the first `n` payments of an annuity of 1 per period,
with interest rate `i`.
There is a notation clash with the accumulation function `a`.
`annuity.a` versus `a`.
Etymology: a for annuity.
-/
noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k


/-- Can be used in `CPT_N_aux'` for instance. -/
lemma annuity_positive {n : ℕ} (hn : n ≠ 0) {i : ℝ} (hi : i > -1) :
  a n i > 0 := by
  unfold a
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k >
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_lt_sum ?_ ?_

  intro k hk
  apply le_of_lt
  apply this _ hk
  use 1
  constructor
  simp
  omega
  simp
  tauto

/-- Can be used in `CPT_N_aux'` for instance. -/
lemma annuity_nonnegative (n : ℕ) {i : ℝ} (hi : i > -1) :
  a n i ≥ 0 := by
  unfold a
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices  ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by simp at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply this _ hk


/-- Future value of an annuity-immediate.
s for sum.
-/
noncomputable def s : ℕ → ℝ → ℝ := fun n i =>
  (1 + i) ^ n * a n i


/-- Present value of an annuity-due.
Because double-dot notation is used, we call it `a_double_dot`
or for short `a_dots`.
-/
noncomputable def a_dots : ℕ → ℝ → ℝ := fun n i =>
  ∑ k ∈ Ico 0 n, (1 + i)⁻¹ ^ k

/-- Future value of an annuity-due. -/
noncomputable def s_dots : ℕ → ℝ → ℝ := fun n i =>
  (1 + i) ^ n * a_dots n i


/-- Actuarial notation. -/
local notation n "⌝" i => n i


--ä ä  s̈
local notation "ä" => a_dots
local notation "s̈" => s_dots

/-- In case of zero interest, the present value of the `n` payments of `1`
is simply `n`. -/
@[simp]
theorem annuity_due_interest_zero {n : ℕ} : (ä n ⌝ 0) = n := by simp [a_dots]

theorem future_value_annuity_due_interest_zero {n : ℕ} : (s̈ n ⌝ 0) = n := by simp [s_dots]

/-- Formula for the present value of an annuity-immediate.
This formula is only valid when i ≠ 0. -/
noncomputable def a_formula : ℕ → ℝ → ℝ  := fun n i =>
  (1 - ((1+i)⁻¹) ^ n) / i

/-- Annuities. Another variant. -/
noncomputable def a_variant : ℕ → ℝ → ℝ := fun n i =>
  (∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k) - 1



example (n : ℕ) (i : ℝ) : (ä n ⌝ i) = (1 + i) * (a n ⌝ i) := by
  unfold a_dots a
  simp
  generalize 1 + i = α
  sorry

open Finset
theorem a_eq_a_variant (n : ℕ) (i : ℝ) : (a n ⌝ i) = a_variant n i := by
  simp only [a, a_variant]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← add_eq_of_eq_sub ih]
    suffices ∑ x ∈ Icc 1 (n + 1), ((1 + i)⁻¹ ^ x)
           = ∑ x ∈ Icc 1 n,       ((1 + i)⁻¹ ^ x) + ((1 + i)⁻¹ ^ (n + 1))
      by rw [this];ring_nf
    exact sum_Icc_succ_top (by simp) fun k => (1+i)⁻¹ ^ k

example {n : ℕ} : a_variant n 0 = n := by simp [a_variant]

theorem a_eq_a_formula {i : ℝ} (hi : i ≠ 0) (hi' : 1 + i ≠ 0) :
  (fun n => a n ⌝ i) = fun n => a_formula n i := by
  ext n
  rw [a_eq_a_variant, a_formula, a_variant, ← sum_pow_interest n hi hi']

open Real Filter
/-- The value of a perpetuity of `1` per period with interest rate `i`
 is `1 / i`. For example, if `i = 1` we get `1/2 + 1/4 + ... = 1`. -/
theorem annuity_limiting_value {i : ℝ} (hi : 0 < i) :
  Tendsto (fun n => a n ⌝ i) atTop (nhds (1/i)) := by
  rw [a_eq_a_formula (by linarith) (by linarith)]
  have h₀ : 0 ≤ (1 + i)⁻¹ := inv_nonneg_of_nonneg (le_of_lt <| by linarith)
  apply ((continuous_mul_right _).tendsto _).comp
  conv => right; rw [← sub_zero 1]
  exact ((continuous_const.sub continuous_id').tendsto _).comp $
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one $
    abs_of_nonneg h₀ ▸ inv_lt_one_iff₀.mpr $ .inr $ lt_add_of_pos_right 1 hi



  /-- The value of an annuity decreases with rising interest. -/
  theorem annuity_value_decreasing_with_rising_interest {n : ℕ}
      {i j : ℝ} (hj : 0 < i) (hij : i ≤ j) :
    (a_formula n ⌝ j) ≤ a_formula n ⌝ i := by
    unfold a_formula
    have hi₀ : i ≠ 0 := by linarith
    have hi₁ : 1 + i ≠ 0 := by linarith
    have hj₀ : j ≠ 0 := by linarith
    have hj₁ : 1 + j ≠ 0 := by linarith
    rw [← sum_pow_interest n hi₀ hi₁, ← sum_pow_interest n hj₀ hj₁]
    apply tsub_le_tsub_right
    apply sum_le_sum
    intro k hk
    apply pow_le_pow_left₀
    · rw [inv_nonneg]
      linarith
    · exact inv_anti₀ (by linarith) (by linarith)

theorem annuity_value_pos {i : ℝ} (hi : i > 0) (n : ℕ) (hn : n > 0) :
    0 < a_formula n ⌝ i := by
  apply div_pos
  · simp only [inv_pow, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) (by omega))
  · exact hi

theorem annuity_value_bounded {i : ℝ} (hi : i > 0) (n : ℕ) :
    (a_formula n ⌝ i) ≤ 1 / i :=
  div_le_div₀ zero_le_one (by ring_nf;simp;positivity) hi (by simp)

example (n : ℕ) : ∑ i ∈ range (n+1), (1/(2 : ℝ))^i = 2 - (1/(2 : ℝ))^n := by
  induction n with
  | zero => simp;linarith
  | succ n ih =>
    rw [sum_range_succ, ih]
    field_simp
    ring_nf

  /-- The value of an annuity increases with the number of pay periods. -/
theorem annuity_value_increasing_with_time
  {n : ℕ} {i : ℝ} (hi : 0 < i) : (a_formula n ⌝ i) ≤ a_formula (n+1) ⌝ i := by
    have h₀ : (1 + i)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      linarith
    apply div_le_div₀
    · suffices (1 + i)⁻¹ ^ (n + 1) ≤ 1 by linarith
      apply pow_le_one₀ (by positivity) h₀
    · ring_nf
      suffices (1 + i)⁻¹ * (1 + i)⁻¹ ^ n ≤ 1 * (1 + i)⁻¹ ^ n by
        linarith
      refine mul_le_mul_of_nonneg_right h₀ ?_
      positivity
    · exact hi
    · linarith

theorem annuity_at_time_two {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 2 ⌝ i) = (2+i) / ((1+i)^2) := by grind [a_formula]

theorem annuity_at_time_one {i : ℝ} (H₀ : 1 + i ≠ 0) (H₁ : i ≠ 0) :
      (a_formula 1 ⌝ i) = (1+i)⁻¹ := by grind [a_formula]

theorem annuity_at_time_zero {i : ℝ} : (a_formula 0 ⌝ i) = 0 := by simp [a_formula]

theorem annuity_with_interest_zero {n : ℕ} : (a_formula n ⌝ 0) = 0 := by simp [a_formula]

theorem annuity_with_interest_one {n : ℕ} : (a_formula n ⌝ 1) = 1 - (1/2) ^ n := by
    simp [a_formula]
    congr
    exact one_add_one_eq_two

theorem annuity_with_interest_half {n : ℕ} : (a_formula n ⌝ (1/2)) = 2 * (1 - (2/3) ^ n) := by
    simp [a_formula]
    nth_rewrite 1 [mul_comm]
    congr
    ring_nf
    cases n with
    | zero => simp
    | succ n =>
      apply (pow_left_inj₀ ?_ ?_ ?_).mpr (by simp) <;> positivity

end annuity

/-- The BA II Plus Professional equation. -/
def annuity_equation (IY PMT PV FV : ℝ) (N : ℕ) : Prop :=
  PV +
  PMT *
  -- (Finset.sum (Finset.univ) (fun k : Fin N => (1 + IY/100) ^ k.1))
  (annuity.a N (IY / 100))
  + FV * (1 + IY/100)⁻¹ ^ N = 0

noncomputable def CPT_PV (IY PMT FV : ℝ) (N : ℕ) :=
  - PMT * (annuity.a N (IY / 100)) - FV * (1 + IY/100)⁻¹ ^ N

noncomputable def CPT_FV (IY PMT PV : ℝ) (N : ℕ) :=
  (- PV - PMT * (annuity.a N (IY / 100))) / ((1 + IY/100)⁻¹ ^ N)

noncomputable def CPT_N (IY PMT PV FV : ℝ) :=
  (Real.log ((PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100)))) /
      (Real.log (1 + IY / 100)⁻¹)

/-- [CPT] [PV] is quite simple: -/
lemma PV_eq_CPT_PV {IY PMT PV FV : ℝ} {N : ℕ} (h : annuity_equation IY PMT PV FV N) :
  PV = CPT_PV IY PMT FV N := by
  unfold annuity_equation at h
  unfold CPT_PV
  linarith

/-- [CPT] [FV] is simple as long as [I/Y] is not `-100`: -/
lemma FV_eq_CPT_FV {IY PMT PV FV : ℝ} {N : ℕ} (h : annuity_equation IY PMT PV FV N)
  (h₀ : IY ≠ -100) :
  FV = CPT_FV IY PMT PV N := by
  unfold annuity_equation at h

  rw [PV_eq_CPT_PV h]
  unfold CPT_PV CPT_FV
  ring_nf
  have : 1 + IY * (1 / 100) ≠ 0 := by
    contrapose! h₀
    linarith
  generalize 1 + IY * (1 / 100) = x at *
  field_simp



-- [CPT] [N] is simple enough using the `(1-v^n)/i` formula
lemma N_eq_CPT_N {IY PMT PV FV : ℝ} {N : ℕ} (h : annuity_equation IY PMT PV FV N)
  (h₀ : IY ≠ 0)
  (h₁ : IY ≠ -100)
  (h₂ : FV * (IY / 100) - PMT ≠ 0)
  (h₄ : IY / 100 ≠ -2) :
  N = CPT_N IY PMT PV FV := by

-- (PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100)) < 1
  unfold annuity_equation at h
  have := @annuity.a_eq_a_formula (IY / 100) (by contrapose! h₀; linarith)
    (by contrapose! h₁;linarith)
  rw [congrFun this] at h
  unfold annuity.a_formula at h
  have h₃ : Real.log ((1 + IY / 100)⁻¹ ^ N) = N * Real.log (1 + IY / 100)⁻¹ :=
    Real.log_pow (1 + IY / 100)⁻¹ N
  generalize (1 + IY / 100)⁻¹ ^ N = V at *
  have g₀ : - (PMT * ((1 - V) / (IY / 100)) + FV * V) = PV := by linarith
  have g₁ :  PMT * (1 - V) + FV * V * (IY / 100) = - PV * (IY / 100) := by
    rw [← g₀]
    field_simp
    linarith
  have g₂ : V * (FV * (IY / 100) - PMT) = - PV * (IY / 100) - PMT := by
    linarith
  have g₃ : V  = (- PV * (IY / 100) - PMT) / ((FV * (IY / 100) - PMT)) := by
    generalize FV * (IY / 100) - PMT = y at *
    field_simp
    linarith
  rw [g₃] at h₃
  have g₀ : Real.log (1 + IY / 100)⁻¹ ≠ 0 := by
    simp
    constructor
    · contrapose! h₁
      linarith
    constructor
    · exact h₀
    · contrapose! h₄
      linarith
  have : N =
    (Real.log ((-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT))) / (Real.log (1 + IY / 100)⁻¹)  := by
      generalize (Real.log (1 + IY / 100)⁻¹) = z at *
      generalize Real.log ((-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT)) = w at *
      field_simp
      linarith
  unfold CPT_N
  suffices (PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100))
   = (-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT) by rw [this];linarith
  have : FV * (IY / 100) - PMT = - (PMT - FV * (IY / 100)) := by linarith
  rw [this]
  have : (-PV * (IY / 100) - PMT) = - (PV * (IY / 100) + PMT) := by linarith
  rw [this]
  exact Eq.symm (neg_div_neg_eq (PV * (IY / 100) + PMT) (PMT - FV * (IY / 100)))


lemma annuity_equation_continuity {PMT PV FV i : ℝ} {N : ℕ} :
    ContinuousOn (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N) (Set.Icc 0 i) := by
        refine ContinuousOn.add ?_ ?_
        refine Continuous.comp_continuousOn' ?_ ?_
        exact continuous_add_left PV
        refine Continuous.comp_continuousOn' ?_ ?_
        exact continuous_mul_left PMT
        unfold annuity.a
        refine Continuous.comp_continuousOn' ?_ ?_
        exact continuous_finset_sum _ fun i a ↦ continuous_apply i
        refine continuousOn_pi.mpr ?_
        intro k
        refine ContinuousOn.pow ?_ k
        refine ContinuousOn.inv₀ ?_ ?_
        apply Continuous.continuousOn
        exact continuous_add_left 1
        intro x hx
        simp at hx
        apply ne_of_gt
        linarith

        refine Continuous.comp_continuousOn' ?_ ?_
        exact continuous_mul_left FV
        refine ContinuousOn.pow ?_ N

        refine ContinuousOn.inv₀ ?_ ?_
        apply Continuous.continuousOn
        exact continuous_add_left 1
        intro x hx
        simp at hx
        apply ne_of_gt
        linarith

lemma annuity_antitone {N : ℕ} (hN : N ≠ 0) ⦃a b : ℝ⦄ (hab : a < b) (ha : 0 ≤ a) :
  annuity.a N b < annuity.a N a := by
        unfold annuity.a
        apply sum_lt_sum
        intro t ht
        simp at ht ⊢
        refine inv_anti₀ ?_ ?_
        positivity
        refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_ <;> linarith
        use 1
        constructor
        simp
        omega
        simp
        refine inv_strictAnti₀ ?_ ?_ <;> linarith

/-- We do not use Global Axiom of Choice here,
but just Intermediate Value Theorem.

Actually, ∀ ε > 0, ∃ i > 0, f i < PV + ε but we don't need to prove that here.
-/
theorem CPT_IY_unique {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT > 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0):
    ∃! IY ≥ 0, annuity_equation IY PMT PV FV N := by
  unfold annuity_equation
  let f : ℝ → ℝ :=
    fun i => PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N
  have ⟨i,hi⟩ : ∃ i ≥ 0, f i = 0 := by
    let ι := 2 * (max FV PMT) / (-PV)
    have hι : ι > 0 := by
        simp [ι]
        have : -PV > 0 := by linarith
        apply mul_pos
        apply mul_pos
        simp
        exact lt_sup_of_lt_left hFV
        simp
        linarith
    have h₀ : ι > 0 ∧ f ι < 0 := by
        constructor
        · tauto
        · unfold f
          have (i : ℝ) (hi : i > 0) : annuity.a N i < 1/i := by
            have := @annuity.a_eq_a_formula i (by linarith) (by linarith)
            have := congrFun this N
            rw [this]
            unfold annuity.a_formula
            suffices  (1 - (1 + i)⁻¹ ^ N) < 1 by
                exact (div_lt_div_iff_of_pos_right hi).mpr this
            suffices 0 < (1 + i)⁻¹ ^ N by linarith
            positivity
          have := this ι hι
          apply lt_trans
          · show PV + PMT * annuity.a N ι + FV * (1 + ι)⁻¹ ^ N <
                 PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N
            have : PMT * annuity.a N ι <
              PMT * (1 / ι) := (mul_lt_mul_left hPMT).mpr this
            linarith
          calc _ ≤ PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ := by
                suffices PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N ≤ PMT * (1 / ι) + FV * (1 + ι)⁻¹ by linarith
                suffices FV * (1 + ι)⁻¹ ^ N ≤ FV * (1 + ι)⁻¹ by linarith
                suffices (1 + ι)⁻¹ ^ N ≤ (1 + ι)⁻¹ by exact
                  (mul_le_mul_iff_of_pos_left hFV).mpr this
                have : (1 + ι) > 1 := by linarith
                have : (1 + ι)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
                have : (1 + ι)⁻¹ > 0 := by simp;linarith
                generalize (1+ι)⁻¹ = α at *
                refine pow_le_of_le_one ?_ ?_ hN
                linarith
                linarith
               _ < _ := by
                unfold ι
                have : PMT * (1 / (2 * max FV PMT / -PV)) = PMT * (-PV / (2 * max FV PMT)) := by field_simp
                rw [this]
                have : (1 + 2 * max FV PMT / -PV)⁻¹ = 1 / (1 + 2 * max FV PMT / -PV) := by simp
                rw [this]
                have : 1 / (1 + 2 * max FV PMT / -PV) = ((-PV) * 1) / (-PV * (1 + 2 * max FV PMT / -PV)) := by
                    refine Eq.symm (IsUnit.mul_div_mul_left ?_ 1 (1 + 2 * max FV PMT / -PV))
                    simp
                    linarith
                rw [this]
                have : -PV * (1 + 2 * max FV PMT / -PV) = ((-PV) * 1 + (-PV) * (2 * max FV PMT / -PV)) := by ring_nf
                rw [this]
                have : -PV * (2 * max FV PMT / -PV) = 2 * max FV PMT := by
                        refine mul_div_cancel₀ (2 * max FV PMT) ?_
                        simp
                        linarith
                rw [this]
                have :  PV + PMT * (-PV / (2 * max FV PMT)) + FV * (-PV * 1 / (-PV * 1 + 2 * max FV PMT))
                    =  PV * (1 + PMT * (-1 / (2 * max FV PMT)) + FV * (-1 * 1 / (-PV * 1 + 2 * max FV PMT))) := by
                    ring_nf
                rw [this]
                apply mul_neg_of_neg_of_pos hPV
                simp
                suffices - ( PMT * (-1 / (2 * max FV PMT)) + FV * (-1 / (-PV + 2 * max FV PMT))) < 1 by
                    linarith
                cases max_choice FV PMT with
                | inl h =>
                    rw [h];ring_nf
                    have : PMT * FV⁻¹ ≤ 1 := by
                        refine mul_inv_le_one_of_le₀ ?_ ?_
                        exact sup_eq_left.mp h
                        linarith
                    have :  1 / 2 + FV * (FV * 2 - PV)⁻¹ < 1 := by
                        suffices FV * (FV * 2 - PV)⁻¹ < 1/2 by linarith
                        suffices FV / (FV * 2 + -PV) < 1/2 by simp at this ⊢;tauto
                        suffices  2 * (FV / (FV * 2 + -PV)) < 2 * (1 / 2) by linarith
                        simp
                        have :  2 * (FV / (FV * 2 + -PV)) =
                            (FV * 2) / (FV * 2 + -PV) := by ring_nf
                        rw [this]
                        suffices  FV * 2 < FV * 2 + -PV by apply (div_lt_one₀ _).mpr <;> linarith
                        linarith
                    calc _ ≤ (1 / 2) + FV * (FV * 2 - PV)⁻¹ := by linarith
                         _ < _ := this
                | inr h =>
                    rw [h];ring_nf
                    have : PMT * PMT⁻¹ =1 := CommGroupWithZero.mul_inv_cancel PMT <| by linarith
                    rw [this]
                    suffices FV * (PMT * 2 - PV)⁻¹ < 1/2 by linarith
                    have : FV ≤ PMT := le_of_sup_eq h
                    have : (PMT * 2 + -PV)⁻¹ = (PMT * 2 - PV)⁻¹ := by ring_nf
                    rw [← this]
                    have : 0 < -PV := by simp;tauto
                    have : 0 < PMT * 2 + -PV := by positivity
                    have : 0 < (PMT * 2 + -PV)⁻¹ := by positivity
                    suffices PMT * (PMT * 2 + -PV)⁻¹ < 1 / 2 by
                        calc _ ≤ _ := (mul_le_mul_iff_of_pos_right (by tauto)).mpr (by tauto)
                             _ < _ := this
                    suffices 2 * ( PMT * (PMT * 2 + -PV)⁻¹) < 2 * (1 / 2) by linarith
                    simp
                    have : 2 * (PMT * (PMT * 2 + -PV)⁻¹)
                        =  PMT * 2 / (PMT * 2 + -PV) := by ring_nf
                    rw [this]
                    suffices PMT * 2 < (PMT * 2 + -PV) by
                        apply (div_lt_one₀ _).mpr <;> tauto
                    linarith
    let i := ι
    have :  0 ∈ Set.Icc (f i) (f 0) := by
        simp
        constructor
        apply le_of_lt
        exact h₀.2
        unfold f
        simp
        unfold annuity.a
        simp
        tauto
    have ⟨j,hj⟩:= @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _ 0 i (by linarith) f annuity_equation_continuity 0 this
    use j
    simp at hj
    tauto
  have ha: StrictAntiOn f (Set.Ici 0) := by
    unfold f
    intro a ha b hb hab
    simp at ha hb ⊢
    suffices PMT * annuity.a N b + FV * ((1 + b) ^ N)⁻¹ < PMT * annuity.a N a + FV * ((1 + a) ^ N)⁻¹ by
        linarith
    have : ((1 + b) ^ N)⁻¹ < ((1 + a) ^ N)⁻¹ := by
        refine inv_strictAnti₀ ?_ ?_
        positivity
        refine pow_lt_pow_left₀ ?_ ?_ hN
        linarith
        linarith
    have : PMT * annuity.a N b  < PMT * annuity.a N a := (mul_lt_mul_left hPMT).mpr <| annuity_antitone hN hab ha
    have : FV * ((1 + b) ^ N)⁻¹ <  FV * ((1 + a) ^ N)⁻¹ := (mul_lt_mul_left hFV).mpr <| by tauto
    linarith

  have : ∃! i ≥ 0, f i = 0 := by
    use i
    constructor
    simp
    tauto
    intro j hj
    by_contra H
    have : i < j ∨ j < i := lt_or_gt_of_ne fun a ↦ H a.symm
    rcases (lt_or_gt_of_ne fun a ↦ H a.symm) with (g | g)
    all_goals specialize ha (by simp;tauto) (by simp;tauto) g; linarith
  obtain ⟨i,hi⟩ := this
  use i * 100
  constructor
  · constructor
    simp
    tauto
    unfold f at hi
    simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.mul_div_cancel_right]
    tauto
  · ring_nf
    intro J hJ
    have := hi.2 (J/100)
    simp at hJ ⊢ this
    specialize this (by linarith) (by
        unfold f;rw [← hJ.2]
        congr
        simp
        congr)
    linarith

/-- The [CPT] [IY] button combination on the BA II Plus Financial. -/
noncomputable def CPT_IY {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT > 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0): ℝ := (CPT_IY_unique hN hPMT h hPV hFV).choose

-- The [CPT] [IY] gives the only solution for interest rate per year.
lemma IY_eq_CPT_IY {PMT PV FV IY : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT > 0) (h :  0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) (hann : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≥ 0) : IY = CPT_IY hN hPMT h hPV hFV :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.2 _ ⟨h₀, hann⟩

noncomputable def CPT_PMT (IY PV FV : ℝ) (N : ℕ) :=
  (- FV * (1 + IY / 100)⁻¹ ^ N  - PV) / (annuity.a N (IY / 100))
--can in principle also create a CPT_IY using Intermediate Value Theorem and Choice.

lemma PMT_eq_CPT_PMT {IY PMT PV FV : ℝ} {N : ℕ} (h : annuity_equation IY PMT PV FV N)
  (h₀ : IY > -100) (h₁ : IY ≠ 0) (hN : N ≠ 0) :
  PMT = CPT_PMT IY PV FV (N)
   := by
  unfold annuity_equation at h
  have : annuity.a N (IY / 100) ≠ 0 := by
    have := @annuity.a_eq_a_formula (IY / 100) (by contrapose! h₁; linarith)
      (by contrapose! h₀;linarith)

    rw [congrFun this]
    unfold annuity.a_formula
    simp
    constructor
    field_simp
    contrapose! h₁
    have : 100 ^ N / (100 + IY) ^ N
      = (100 / (100 + IY)) ^ N := by ring_nf
    rw [this] at h₁
    have : ((100) / ((100) + IY)) ^ N = 1 ^ N := by field_simp;linarith
    have : (100) / ((100) + IY) = 1 := by
      have : 100 + IY > 0 := by linarith
      generalize 100 + IY = i at *
      have : 100 / i > 0 := by field_simp;linarith
      generalize 100 / i = j at *
      simp at *
      have : N > 0 := by omega
      have : N * Real.log j = Real.log (j ^ N) := by exact Eq.symm (Real.log_pow j N)
      have : j ^ N = Real.exp (N * Real.log j) := by
        rw [this]
        refine Eq.symm (Real.exp_log ?_)
        (expose_names; exact pow_pos this_5 N)
      have : Real.exp (N * Real.log j) = 1 := by linarith
      have : Real.exp (N * Real.log j) = Real.exp 0 := by rw [this];exact Eq.symm Real.exp_zero
      have : N * Real.log j = 0 := by apply Real.exp_injective this
      simp at this
      cases this with
      | inl h => omega
      | inr h =>
        cases h with
        | inl h => subst h;simp_all
        | inr h =>
          cases h with
          | inl h => tauto
          | inr h => linarith
    rw [this] at h₁
    simp at this
    have : 100 + IY ≠ 0 := by contrapose! h₀;linarith
    have : 100 / (100 + IY) = 100 / 100 := by simp;tauto
    have : 100 = 100 + IY := by
      generalize 100 + IY = z at *
      symm
      let hu := (100 : ℝ)
      have : hu / z = hu / 100 := this
      have : hu ≠ 0 := by simp [hu]
      have : z / hu = 100 / hu := by (expose_names; exact (div_eq_div_iff_comm hu z hu).mp this_6)
      simp at this
      ring_nf at this
      rw [mul_comm] at this
      have : hu⁻¹ ≠ 0 := by simp;tauto
      linarith
    linarith
    · exact h₁
  unfold CPT_PMT
  generalize annuity.a N (IY / 100) = α at *
  generalize (1 + IY / 100)⁻¹ ^ N = β at *
  have : PMT * α = - (FV * β)  - PV := by
    linarith
  field_simp
  rw [this]
