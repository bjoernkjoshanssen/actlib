import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.log
-- import LeanCert

/-!

## Five implicit functions from the Annuity Equation

The BA II Plus calculator values PMT, I/Y, N, FV, PV
can each be computed from the other four.

Main results:

* `annuity_equation_unique_solvability`
* `TVM_equation_unique_solvability`: by setting PMT=0 in
  the annuity equation we obtain unique solution for the
  Time Value of Money equation as well.

-/

open Finset Real Filter

/-- The sum of a finite geometric series. -/
lemma sum_pow (n : ℕ) {x : ℝ} (hx : x ≠ 1) :
    ∑ i ∈ range n, x^i = (x ^ n - 1) / (x - 1) := by
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


lemma sum_Icc_succ_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
  f 0 + ∑ k ∈ Finset.Icc 1 n, f k
    = ∑ k ∈ Finset.range (n+1), f k := by
  have := @Nat.range_succ_eq_Icc_zero
  rw [this]
  have : Finset.Icc 0 n = Finset.Ico 0 1 ∪ Finset.Icc 1 n := by
    ext j
    simp only [mem_Icc, zero_le, true_and, Nat.Ico_succ_singleton, singleton_union, mem_insert]
    constructor
    · intro
      by_cases H : j = 0
      · left
        tauto
      · right
        constructor
        · contrapose! H
          linarith
        · tauto
    intro h
    cases h with
    | inl h => subst h;simp
    | inr h => tauto
  rw [this]
  simp


namespace annuity

/-- The present value of the first `n` payments of an annuity of
1 per period, with interest rate `i`.
There is a notation clash with the accumulation function `a`.
`annuity.a` versus `a`.
Etymology: a for annuity.
-/
def geom_sum : ℕ → ℝ → ℝ := fun n v =>
  ∑ k ∈ Icc 1 n, v ^ k

def id_mul_geom_sum : ℕ → ℝ → ℝ := fun n v =>
  ∑ k ∈ Icc 1 n, k * v ^ k

lemma id_mul_geom_sum_formula₀ (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), k * x^k =
  (x * (n * x^(n + 1) - ((n + 1) * x^n) + 1))/(x - 1)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    have h₀ : (x - 1) ^ 2 ≠ 0 := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      contrapose! hx
      linarith
    set α := (x-1)^2
    field_simp
    ring_nf
    field_simp
    suffices (1 + x ^ n * (-1 - ↑n) + x ^ n * α * ↑(1 + n) + x * x ^ n * ↑n) =
        (1 + x * x ^ n * (-1 - ↑(1 + n)) + x ^ 2 * x ^ n * ↑(1 + n)) by
        simp only [Nat.cast_add, Nat.cast_one, mul_eq_mul_left_iff] at this ⊢
        left
        linarith
    suffices x ^ n * (-1 - ↑n) + x ^ n * α * ↑(1 + n) + x * x ^ n * ↑n =
      x * x ^ n * (-1 - ↑(1 + n)) + x ^ 2 * x ^ n * ↑(1 + n) by linarith
    unfold α
    ring_nf
    field_simp
    suffices (x * (↑n - ↑(1 + n) * 2 + x * ↑(1 + n)) + (-1 - ↑n) + ↑(1 + n))
        = x * (-1 - ↑(1 + n) + x * ↑(1 + n)) by
        simp at this ⊢
        linarith
    simp only [Nat.cast_add, Nat.cast_one]
    suffices x * (↑n - ↑(1 + n) * 2 + x * ↑(1 + n))
        = x * (-1 - ↑(1 + n) + x * ↑(1 + n)) by
            linarith
    suffices (↑n - ↑(1 + n) * 2 + x * ↑(1 + n)) = (-1 - ↑(1 + n) + x * ↑(1 + n)) by
        rw [this]
    simp
    linarith
/-- Rename to id_mul_geom_sum_formula -/
lemma id_mul_geom_sum_formula (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    id_mul_geom_sum n x =
  (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2 := by
  unfold id_mul_geom_sum
  let f : ℕ → ℝ := fun k => k * x^ k
  change ∑ k ∈ Finset.Icc 1 n, f k =
  (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2
  suffices f 0 + ∑ k ∈ Finset.Icc 1 n, f k =
    (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2 by
    rw [← this]
    unfold f
    simp
  rw [sum_Icc_succ_eq_sum_range]
  apply id_mul_geom_sum_formula₀
  tauto

noncomputable def a : ℕ → ℝ → ℝ := fun n i =>
  geom_sum n (1 + i)⁻¹

lemma annuity_zero (n : ℕ) : a n 0 = n := by simp [a, geom_sum]

/-- Increasing annuity. -/
noncomputable def Ia : ℕ → ℝ → ℝ := fun n i =>
  id_mul_geom_sum n (1 + i)⁻¹

def bond_price_sum : ℕ → ℝ → ℝ → ℝ := fun n r v =>
  (r * geom_sum n v + v ^ n)

/-- Price of a bond with unit redemption value, coupon rate r, interest rate i. -/
noncomputable def bond_price : ℕ → ℝ → ℝ → ℝ := fun n i r =>
  bond_price_sum n r (1+i)⁻¹
-- express in terms of `geom_sum` and `v`



lemma Ia_eq_Ia_formula (n : ℕ) (i : ℝ) (hi : i ≠ 0) :
    let x := (1 + i)⁻¹
    Ia n i =
    (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2 := by
    let x := (1 + i)⁻¹
    unfold Ia --id_mul_geom_sum
    have := @id_mul_geom_sum_formula x (by
        unfold x
        simp;tauto) n
    unfold x at this
    rw [this]

/-- The present value of a level-payments annuity
with at least one payment is positive. -/
lemma annuity_positive {n : ℕ} (hn : n ≠ 0) {i : ℝ} (hi : i > -1) :
  a n i > 0 := by
  unfold a geom_sum
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k >
     ∑ k ∈ Icc 1 n, 0 by
      simp only [inv_pow, sum_const_zero, gt_iff_lt] at this ⊢;exact this
  refine sum_lt_sum ?_ ?_
  · intro k hk
    apply le_of_lt
    apply this _ hk
  use 1
  constructor
  · simp
    omega
  simp
  tauto

lemma geom_sum_positive {n : ℕ} (hnn : n > 1) {i : ℝ} (hi : i > -1) :
    0 < geom_sum n (1 + i)⁻¹ := by
  have := @annuity_positive n (by linarith) i (by linarith)
  unfold a at this
  linarith

-- lemma annuity_antitone (n : ℕ) (hn : n ≠ 0) {i j : ℝ} (hi : i > -1)
--     (hij : i < j) :
--   a n j < a n i := by
--   unfold a
--   refine sum_lt_sum ?_ ?_
--   intro k hk
--   refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
--   simp
--   linarith
--   simp
--   linarith
--   simp at hk
--   linarith
--   apply inv_anti₀ <;>linarith
--   use 1
--   simp
--   constructor
--   contrapose! hn
--   linarith
--   refine (inv_lt_inv₀ ?_ ?_).mpr ?_
--   linarith
--   linarith
--   linarith



/-- The present value of a level-payments annuity is nonnegative. -/
lemma annuity_nonneg (n : ℕ) {i : ℝ} (hi : i > -1) :
  a n i ≥ 0 := by
  unfold a geom_sum
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by
      simp only [inv_pow, sum_const_zero, ge_iff_le] at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply this _ hk

lemma bond_price_pos (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : 0 ≤ r) : 0 < bond_price n i r := by
  have h₀ : a n i ≥ 0 := annuity_nonneg n hi
  have h₁ : r * a n i ≥ 0 := by apply mul_nonneg <;> tauto
  have h₂ : ((1 + i)⁻¹) > 0 := by simp;linarith
  have h₃ : ((1 + i)⁻¹ ^ n) > 0 := by apply pow_pos;linarith
  unfold bond_price
  exact calc 0 < (1 + i)⁻¹ ^ n := h₃
         _ ≤ _ := by apply le_add_of_nonneg_left;tauto


lemma increasing_annuity_nonneg (n : ℕ) {i : ℝ} (hi : i > -1) :
  Ia n i ≥ 0 := by
  unfold Ia id_mul_geom_sum
  have : 0 < 1 + i := by linarith
  have : 0 < (1 + i)⁻¹ := Right.inv_pos.mpr this
  have : ∀ k ∈ Finset.Icc 1 n, 0 < (1+i)⁻¹ ^ k := by
    intro k hk
    exact pow_pos this k
  suffices ∑ k ∈ Icc 1 n, k * (1 + i)⁻¹ ^ k ≥
     ∑ k ∈ Icc 1 n, 0 by
     simp only [inv_pow, sum_const_zero, ge_iff_le] at this ⊢;exact this
  refine sum_le_sum ?_
  intro k hk
  apply le_of_lt
  apply mul_pos
  · simp at hk ⊢
    linarith
  apply this _ hk


/-- Future value of an annuity-immediate. s for sum.
-/
noncomputable def s : ℕ → ℝ → ℝ := fun n i => (1 + i) ^ n * a n i


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

/-- In case of zero interest,
the present value of the `n` payments of `1` is simply `n`. -/
@[simp]
theorem annuity_due_interest_zero {n : ℕ} :
    (ä n ⌝ 0) = n := by simp [a_dots]

@[simp]
theorem annuity_immediate_interest_zero {n : ℕ} :
    (a n ⌝ 0) = n := by simp [a, geom_sum]

/-- In case of zero interest,
the future value of the `n` payments of `1` is simply `n`. -/
theorem future_value_annuity_due_interest_zero {n : ℕ} :
    (s̈ n ⌝ 0) = n := by simp [s_dots]

/-- Formula for the present value of an annuity-immediate.
This formula is only valid when i ≠ 0. -/
noncomputable def a_formula : ℕ → ℝ → ℝ  := fun n i =>
  (1 - ((1+i)⁻¹) ^ n) / i

noncomputable def Ia_formula : ℕ → ℝ → ℝ := fun n i =>
    let x := (1+i)⁻¹
    (x * (n * x ^ (n + 1) - ((n + 1) * x ^ n) + 1)) / (x - 1) ^ 2

def duration_equation (n : ℕ) (i r d : ℝ) :=
   d * annuity.bond_price n i r - (r * annuity.Ia n i + ↑n * (1 + i)⁻¹ ^ n) = 0

/-- Annuities. Another variant. -/
noncomputable def a_variant : ℕ → ℝ → ℝ := fun n i =>
  (∑ k ∈ range (n + 1), (1 + i)⁻¹ ^ k) - 1

theorem a_eq_a_variant (n : ℕ) (i : ℝ) : (a n ⌝ i) = a_variant n i := by
  simp only [a, a_variant, geom_sum]
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




/-- The value of a perpetuity of `1` per period with interest rate `i`
 is `1 / i`. For example, if `i = 1` we get `1/2 + 1/4 + ... = 1`. -/
theorem annuity_limiting_value {i : ℝ} (hi : 0 < i) :
  Tendsto (fun n => a n ⌝ i) atTop (nhds (1/i)) := by
  rw [a_eq_a_formula (by linarith) (by linarith)]
  have h₀ : 0 ≤ (1 + i)⁻¹ := inv_nonneg_of_nonneg (le_of_lt <| by linarith)
  apply ((continuous_mul_const _).tendsto _).comp
  conv => right; rw [← sub_zero 1]
  exact ((continuous_const.sub continuous_id').tendsto _).comp <|
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one <| abs_of_nonneg h₀ ▸
    inv_lt_one_iff₀.mpr <| .inr <| lt_add_of_pos_right 1 hi


lemma annuity_antitone {N : ℕ} (hN : N ≠ 0)
    ⦃a b : ℝ⦄ (hab : a < b) (ha : -1 < a) :
    annuity.a N b < annuity.a N a := by
  unfold annuity.a
  apply sum_lt_sum
  · intro t ht
    simp only [mem_Icc, inv_pow] at ht ⊢
    refine inv_anti₀ ?_ ?_
    · have : 0 < 1 + a := by linarith
      positivity
    refine (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_ <;> linarith
  use 1
  constructor
  · simp
    omega
  simp only [pow_one]
  refine inv_strictAnti₀ ?_ ?_ <;> linarith


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
  div_le_div₀ zero_le_one (by ring_nf;simp only [inv_pow, tsub_le_iff_right,
    le_add_iff_nonneg_right, inv_nonneg];positivity) hi (by simp)


/-- The value of an annuity increases with the number of payments. -/
theorem annuity_value_increasing_with_time
    {n : ℕ} {i : ℝ} (hi : 0 < i) :
    (a_formula n ⌝ i) ≤ a_formula (n+1) ⌝ i := by
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

end annuity

/-- The BA II Plus Professional equation. -/
def annuity_equation (IY PMT PV FV : ℝ) (N : ℕ) : Prop :=
  PV + PMT * (annuity.a N (IY / 100)) + FV * (1 + IY/100)⁻¹ ^ N = 0

noncomputable def CPT_PV (IY PMT FV : ℝ) (N : ℕ) :=
  - PMT * (annuity.a N (IY / 100)) - FV * (1 + IY/100)⁻¹ ^ N

noncomputable def CPT_FV (IY PMT PV : ℝ) (N : ℕ) :=
  (- PV - PMT * (annuity.a N (IY / 100))) / ((1 + IY/100)⁻¹ ^ N)

noncomputable def CPT_N (IY PMT PV FV : ℝ) :=
  (log ((PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100)))) /
      (log (1 + IY / 100)⁻¹)


-- -- example : CPT_N 8 1 (-3) 2 ≤ 10 := by
-- --   unfold CPT_N
-- --   have : ((1:ℝ) - 2 * (8 / 100))
-- --     = 0.84 := by
-- --       ring_nf
-- --   rw [this]
-- --   have : -(3:ℝ) * (8 / 100) + 1
-- --     = 0.76 := by ring_nf
-- --   rw [this]
-- --   have : ((1:ℝ) + 8/100)⁻¹ = 1 / 1.08 := by
-- --     ring_nf
-- --   rw [this]
-- --   have : Real.log (1 / 1.08) < 0 := by interval_decide

--   have : ∀ x ∈ Set.Icc (0.9:ℝ) 1, Real.log x > -1 := by
--     interval_bound
--   have : Real.log (1 / 1.08) > -1 := by
--     apply this
--     simp
--     constructor
--     interval_decide

--   have : log (0.76 / 0.84) < 0 := by interval_decide

--   suffices log (0.92 / 0.84) ≤ log (1 / 1.08) * 10
--     by sorry

--   have : Real.exp 3 > 20 := by interval_decide
--   have : Real.log 1 < 2 := by interval_decide
--   have : Real.log 0.08 < 2 := by interval_decide
--   have : Real.log 1.08⁻¹ < 2 := by interval_decide
--   have : (1 + 8/100) > Real.exp 0 := by
--     interval_decide
--   sorry

/-- [CPT] [PV] is quite simple: -/
lemma PV_eq_CPT_PV {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N) :
    PV = CPT_PV IY PMT FV N := by
  unfold annuity_equation at h
  unfold CPT_PV
  linarith

/-- [CPT] [FV] is simple as long as [I/Y] is not `-100`: -/
lemma FV_eq_CPT_FV {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≠ -100) :
    FV = CPT_FV IY PMT PV N := by
  unfold annuity_equation at h
  rw [PV_eq_CPT_PV h]
  unfold CPT_PV CPT_FV
  ring_nf
  have : 1 + IY * (1 / 100) ≠ 0 := by
    contrapose! h₀
    linarith
  have : (1 + IY * (1 / 100)) ^ N ≠ 0 := by
    contrapose! this
    simp only [one_div, pow_eq_zero_iff', ne_eq] at this ⊢
    rw [this.1]
  generalize 1 + IY * (1 / 100) = x at *
  field_simp
  ring_nf
  rw [inv_pow]
  field_simp



-- [CPT] [N] is simple enough using the `(1-v^n)/i` formula
lemma N_eq_CPT_N {IY PMT PV FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (h₀ : IY ≠ 0)
    (h₁ : IY ≠ -100)
    (h₂ : IY / 100 ≠ -2)
    (h_nonpar : FV * (IY / 100) - PMT ≠ 0) :
    N = CPT_N IY PMT PV FV := by
  unfold annuity_equation at h
  have := @annuity.a_eq_a_formula (IY / 100) (by contrapose! h₀; linarith)
    (by contrapose! h₁;linarith)
  rw [congrFun this] at h
  unfold annuity.a_formula at h
  have h₃ : log ((1 + IY / 100)⁻¹ ^ N) =
        N * log (1 + IY / 100)⁻¹ :=
    log_pow (1 + IY / 100)⁻¹ N
  generalize (1 + IY / 100)⁻¹ ^ N = V at *
  have g₀ : - (PMT * ((1 - V) / (IY / 100)) + FV * V) = PV := by linarith
  have g₁ : PMT * (1 - V) + FV * V * (IY / 100) = - PV * (IY / 100) := by
    rw [← g₀]
    field_simp
  have g₂ : V * (FV * (IY / 100) - PMT) = - PV * (IY / 100) - PMT := by
    linarith
  have g₃ : V  = (- PV * (IY / 100) - PMT)
               / ((FV * (IY / 100) - PMT)) := by
    generalize FV * (IY / 100) - PMT = y at *
    field_simp
    linarith
  rw [g₃] at h₃
  have g₀ : log (1 + IY / 100)⁻¹ ≠ 0 := by
    simp only [log_inv, ne_eq, neg_eq_zero, log_eq_zero, add_eq_left, div_eq_zero_iff,
      OfNat.ofNat_ne_zero, or_false, not_or]
    constructor
    · contrapose! h₁
      linarith
    constructor
    · exact h₀
    · contrapose! h₂
      linarith
  have : N = (log ((-PV * (IY / 100) - PMT)
    / (FV * (IY / 100) - PMT))) / (log (1 + IY / 100)⁻¹) := by
      generalize (log (1 + IY / 100)⁻¹) = z at *
      generalize
        log ((-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT))
        = w at *
      field_simp
      linarith
  unfold CPT_N
  suffices (PV * (IY / 100) + PMT) / (PMT - FV * (IY / 100))
   = (-PV * (IY / 100) - PMT) / (FV * (IY / 100) - PMT) by
    rw [this];linarith
  have : FV * (IY / 100) - PMT = - (PMT - FV * (IY / 100)) := by linarith
  rw [this]
  have : (-PV * (IY / 100) - PMT)
       = - (PV * (IY / 100) + PMT) := by linarith
  rw [this]
  exact (neg_div_neg_eq
    (PV * (IY / 100) + PMT) (PMT - FV * (IY / 100))).symm


lemma discount_continuity₀ (k : ℕ) :
  ContinuousOn (fun y ↦ (1 + y)⁻¹ ^ k) (Set.Ioi (-1 : ℝ)) := by
  apply ContinuousOn.pow
  apply (continuous_const_add _).continuousOn.inv₀
  intro x hx
  rw [Set.mem_Ioi] at hx
  apply ne_of_gt
  linarith

lemma discount_continuity {i : ℝ} (k : ℕ) :
  ContinuousOn (fun y ↦ (1 + y)⁻¹ ^ k) (Set.Ioc (-1) i) := by
  have := @discount_continuity₀
  apply ContinuousOn.mono (discount_continuity₀ k)
  intro j hj
  rw [Set.mem_Ioc] at hj
  rw [Set.mem_Ioi]
  exact hj.1


lemma annuity_continuous {i : ℝ} {N : ℕ} : ContinuousOn
    (fun i ↦ annuity.a N i)
    (Set.Ioc (-1) i) := by
      unfold annuity.a annuity.geom_sum
      exact  (continuous_finsetSum _ fun i _ ↦ continuous_apply i).comp_continuousOn'
        <|continuousOn_pi.mpr discount_continuity

lemma annuity_equation_continuity {PMT PV FV i : ℝ} {N : ℕ} : ContinuousOn
    (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    (Set.Ioc (-1) i) := by
  apply ContinuousOn.add
  · exact (continuous_const_add _).comp_continuousOn'
      <|(continuous_const_mul _).comp_continuousOn' annuity_continuous
  · exact (continuous_const_mul FV).comp_continuousOn' (discount_continuity _)

/-- We can eliminate the unnatural assumption by going to IY ≥ 0. -/
lemma of_IY_nonneg {IY PV PMT FV : ℝ} {N : ℕ}
    (h : annuity_equation IY PMT PV FV N)
    (hIY : IY ≥ 0) (hPMT : PMT ≥ 0) (hFV : FV > 0) :
    -- PMT ≥ 0 should be enough, and would give TVM equation as a special
    -- case.
    0 ≤ PV + PMT * ↑N + FV := by
  unfold annuity_equation at h
  rw [← h]
  suffices PMT * annuity.a N (IY / 100) + FV * (1 + IY / 100)⁻¹ ^ N
         ≤ PMT * ↑N + FV
    by linarith
  suffices PMT * annuity.a N (IY / 100) ≤ PMT * N ∧
    FV * (1 + IY / 100)⁻¹ ^ N ≤  FV by
      linarith
  constructor
  · by_cases H : PMT = 0
    · subst H
      simp
    have hPMT : PMT > 0 := by contrapose! H;linarith
    apply (mul_le_mul_iff_of_pos_left hPMT).mpr
    unfold annuity.a
    apply le_trans
    · apply sum_le_sum
      · intro i hi
        have : 1 + IY / 100 ≥ 1 := by linarith
        simp only [inv_pow, ge_iff_le]
        apply inv_le_one_of_one_le₀
        by_cases H : i = 0
        · subst H
          simp
        apply one_le_pow₀
        linarith
    simp
  apply (mul_le_iff_le_one_right hFV).mpr
  simp only [inv_pow]
  suffices 1 ≤ ((1 + IY / 100) ^ N) by
    exact inv_le_one_of_one_le₀ this
  by_cases H : N = 0
  · subst H
    simp
  refine one_le_pow₀ ?_
  linarith

lemma CPT_IY_unique.aux {PMT PV FV : ℝ}
    (hPMT : PMT > 0) (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * max FV PMT / -PV;
    PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ < 0 := by
  have his : IsUnit (-PV) := by simp;linarith
  intro ι
  rw [one_div_div, ← one_div, ← (IsUnit.mul_div_mul_left his 1 _)]
  rw [LeftDistribClass.left_distrib, mul_div_cancel₀ _ (by linarith)]
  have : PV + PMT * (-PV / (2 * max FV PMT))
       + FV * (-PV * 1 / (-PV * 1 + 2 * max FV PMT))
       = PV * (1 + PMT * (-1 / (2 * max FV PMT))
       + FV * (-1 * 1 / (-PV * 1 + 2 * max FV PMT))) := by
    ring_nf
  rw [this]
  apply mul_neg_of_neg_of_pos hPV
  simp only [mul_one]
  suffices - (PMT * (-1 / (2 * max FV PMT))
    + FV * (-1 / (-PV + 2 * max FV PMT))) < 1 by linarith
  cases max_choice FV PMT with
  | inl h =>
    rw [h];ring_nf
    have : PMT * FV⁻¹ ≤ 1 :=
      mul_inv_le_one_of_le₀ (sup_eq_left.mp h) <| le_of_lt hFV
    have h₀ : 1 / 2 + FV * (FV * 2 - PV)⁻¹ < 1 := by
      suffices FV * (FV * 2 - PV)⁻¹ < 1/2 by linarith
      suffices FV / (FV * 2 + -PV) < 1/2 by simp at this ⊢;tauto
      refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
      · apply add_pos
        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right]
          exact hFV
        · simp only [Left.neg_pos_iff]
          exact hPV
      · simp
      · simp only [one_mul, lt_add_iff_pos_right, Left.neg_pos_iff]
        exact hPV
    calc _ ≤ (1 / 2) + FV * (FV * 2 - PV)⁻¹ := by linarith
         _ < _ := h₀
  | inr h =>
    rw [h];ring_nf
    rw [CommGroupWithZero.mul_inv_cancel PMT <| by linarith]
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
    apply (mul_inv_lt_iff₀ _).mpr
    · rw [mul_add]
      ring_nf
      linarith
    apply add_pos
    all_goals simp; tauto

lemma natpow_rpow (M : ℕ) (x : ℝ) (hx : x > 0) :
    x ^ M = exp (M * log x) := by
  rw [mul_comm]
  apply Eq.trans (rpow_natCast x M).symm <| rpow_def_of_pos hx M

lemma TVM_interest_exists {PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0)
    (h : 0 ≤ PV + FV) :
    ∃ i, 0 ≤ i ∧ PV + FV * ((1 + i) ^ N)⁻¹ = 0 := by
  use exp ((log (FV / -PV)) * (1 / N)) - 1
  have : -PV ≤ FV := by linarith
  have : FV / -PV ≥ 1 := (one_le_div₀ (by linarith)).mpr (by linarith)
  constructor
  · generalize FV / -PV = α at *
    simp only [one_div, sub_nonneg, one_le_exp_iff]
    apply mul_nonneg
    · exact log_nonneg this
    · simp
  rw [add_sub_cancel, natpow_rpow]
  · field_simp
    simp only [mul_zero]
    have : - (FV / PV) = FV / -PV := by linarith
    rw [this]
    rw [log_exp]
    rw [mul_div_left_comm]
    field_simp
    rw [exp_log]
    · field_simp
      simp only [mul_eq_zero]
      right
      have : PV ≠ 0 := by linarith
      have : PV / PV = 1 := by field_simp
      rw [this]
      simp
    linarith
  exact exp_pos (log (FV / -PV) * (1 / ↑N))

lemma PV_FV_aux {PV FV : ℝ} (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * FV / -PV;
    ι ≥ 0 → PV + FV * (1 + ι)⁻¹ < 0 := by
  intro ι hι
  suffices PV + FV / (1 + ι) < 0 by simp at this ⊢;tauto
  suffices FV / (1 + ι) < -PV by linarith
  suffices FV < (-PV) * (1 + ι) by
    refine (div_lt_iff₀ ?_).mpr this
    linarith
  unfold ι
  suffices FV + PV < -PV * (2 * FV / -PV) by linarith
  have : -PV * (2 * FV / -PV) = 2 * FV := by
    refine mul_div_cancel₀ (2 * FV) ?_
    simp
    linarith
  rw [this]
  linarith

lemma CPT_IY.concrete.aux₀ {PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0) (hFV : FV > 0) :
    let ι := 2 * FV / -PV;
    PV + FV * (1 + ι)⁻¹ ^ N < 0 := by
  intro ι
  have hι : ι ≥ 0 := by
    repeat apply mul_nonneg
    all_goals
      try simp
      try linarith
  calc _ ≤  PV + FV * (1 + ι)⁻¹ := by -- same proof as below
        repeat apply (add_le_add_iff_left _).mpr
        apply (mul_le_mul_iff_of_pos_left hFV).mpr
        have h₀ : (1 + ι)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ <| by linarith
        have h₁ : (1 + ι)⁻¹ ≥ 0 := by simp;linarith
        exact pow_le_of_le_one h₁ h₀ hN
  _ < _ := by apply PV_FV_aux <;> tauto

lemma CPT_IY.concrete {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0) (hPV : PV < 0)
    (hFV : FV > 0) (H : ¬PMT = 0) :
    let ι := 2 * max FV PMT / -PV;
    ι > 0 → PV + PMT * annuity.a N ι + FV * (1 + ι)⁻¹ ^ N < 0 := by
      intro ι hι
      have (i : ℝ) (hi : i > 0) : annuity.a N i < 1/i := by
        rw [congrFun (annuity.a_eq_a_formula (i:=i) (by linarith) (by linarith)) N]
        apply (div_lt_div_iff_of_pos_right hi).mpr
        apply sub_lt_self
        positivity
      have hι₁ : ι > -1 := by
        apply lt_trans (b := 0)
        · simp
        apply mul_pos
        · simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left, lt_sup_iff]
          left
          exact hFV
        simp only [inv_neg, Left.neg_pos_iff, inv_neg'']
        exact hPV
      have := this ι hι
      by_cases hPMT : PMT < 0
      · apply lt_trans
        · change _ < PV + FV * (1 + ι)⁻¹ ^ N
          suffices PMT * annuity.a N ι < 0 by linarith
          apply mul_neg_iff.mpr
          · right
            constructor
            · exact hPMT
            · exact annuity.annuity_positive hN hι₁
        · convert CPT_IY.concrete.aux₀ hN hPV hFV
          · rfl
          apply max_eq_left
          linarith
      apply lt_trans
      · change _ < PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ ^ N
        have hPMT : PMT > 0 := by contrapose! H;linarith
        repeat rw [add_assoc]
        apply (add_lt_add_iff_left _).mpr
           <| (add_lt_add_iff_right _).mpr
           <| (mul_lt_mul_iff_of_pos_left hPMT).mpr this
      calc
      _ ≤ PV + PMT * (1 / ι) + FV * (1 + ι)⁻¹ := by
        repeat rw [add_assoc]
        repeat apply (add_le_add_iff_left _).mpr
        apply (mul_le_mul_iff_of_pos_left hFV).mpr
        have h₀ : (1 + ι)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ <| by linarith
        have h₁ : (1 + ι)⁻¹ ≥ 0 := by simp;linarith
        exact pow_le_of_le_one h₁ h₀ hN
      _ < _ := by
        apply CPT_IY_unique.aux
        · contrapose! H; linarith
        all_goals tauto

/-- Existence of interest rate satisfying
 annuity equation. -/
theorem CPT_IY.aux₀ {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (h : 0 ≤ PV + PMT * N + FV)
  (hPV : PV < 0) (hFV : FV > 0) :
  ∃ i ≥ 0, PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N = 0 := by
    by_cases H : PMT = 0
    · subst H
      simp only [zero_mul, add_zero, ge_iff_le, inv_pow] at h ⊢
      exact TVM_interest_exists hN hPV h
    let ι := 2 * (max FV PMT) / (-PV)
    have hι : ι > 0 := by
      repeat apply mul_pos
      · exact Nat.ofNat_pos
      · exact lt_sup_of_lt_left hFV
      simp only [inv_neg, Left.neg_pos_iff, inv_neg'']
      exact hPV
    let f := (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    have : 0 ∈ Set.Icc (f ι) (f 0) := by
        constructor
        · exact le_of_lt <| CPT_IY.concrete hN hPV hFV H hι
        · simp only [annuity.a, annuity.geom_sum, inv_pow, add_zero, one_pow, inv_one, sum_const,
          Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one, f]
          exact h
    have ⟨j,hj⟩:= intermediate_value_Icc'
      (by linarith) (by
        have := @annuity_equation_continuity
        apply ContinuousOn.mono
        · apply this
          exact ι
        intro x hx
        simp at hx ⊢
        constructor
        · linarith
        tauto) this
    use j
    exact ⟨hj.1.1, hj.2⟩

lemma annuity_strictAnti {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (hFV : FV > 0) : StrictAntiOn
    (fun i ↦ PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N)
    (Set.Ioi (-1)) := fun a ha b hb hab => by
  simp only [Set.mem_Ioi, inv_pow] at ha hb ⊢
  have : ((1 + b) ^ N)⁻¹ < ((1 + a) ^ N)⁻¹ := by
      refine inv_strictAnti₀ ?_ ?_
      · have : 0 < 1 + a := by linarith
        positivity
      refine pow_lt_pow_left₀ ?_ ?_ hN <;> linarith
  have : FV * ((1 + b) ^ N)⁻¹ < FV * ((1 + a) ^ N)⁻¹ :=
    (mul_lt_mul_iff_of_pos_left hFV).mpr this
  by_cases H : PMT = 0
  · subst H
    simp only [zero_mul, add_zero, add_lt_add_iff_left, gt_iff_lt]
    exact this
  have hPMT : PMT > 0 := by contrapose! H;apply le_antisymm H hPMT
  have : PMT * annuity.a N b  < PMT * annuity.a N a := by
    apply (mul_lt_mul_iff_of_pos_left _).mpr <| annuity.annuity_antitone hN hab ha
    tauto
  linarith

/-- Unique solution of annuity equation for interest rate,
 via the Intermediate Value Theorem. -/
theorem CPT_IY_unique {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0)
    (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) :
    ∃ IY, (IY ≥ 0 ∧ annuity_equation IY PMT PV FV N)
    ∧ ∀ IY', (IY' > -100 ∧ annuity_equation IY' PMT PV FV N) → IY' = IY
    := by
  unfold annuity_equation
  let f : ℝ → ℝ := fun i => PV + PMT * annuity.a N i + FV * (1 + i)⁻¹ ^ N
  have ⟨i,hi⟩ : ∃ i ≥ 0, f i = 0 := CPT_IY.aux₀ hN h hPV hFV
  have : ∃ i, (i ≥ 0 ∧ f i = 0) ∧ ∀ j, (j > -1 ∧ f j = 0) → j = i := by
    use i
    constructor
    · exact hi
    intro j hj
    by_contra H
    have Hi : i ∈ Set.Ioi (-1) := by simp;linarith
    have Hj : j ∈ Set.Ioi (-1) := by simp;linarith
    rcases (lt_or_gt_of_ne fun a ↦ H a.symm) with (g | g)
    all_goals
      have ha: StrictAntiOn f (Set.Ioi (-1)) := annuity_strictAnti hN hPMT hFV
      specialize ha (by tauto) (by tauto) g; linarith
  obtain ⟨i,hi⟩ := this
  use i * 100
  constructor
  · constructor
    · simp at hi
      linarith
    · unfold f at hi
      convert hi.1.2 <;> linarith
  · ring_nf
    intro J hJ
    have := hi.2 (J/100)
    simp only [gt_iff_lt, one_div, inv_pow, and_imp] at hJ ⊢ this
    specialize this (by linarith) (by
      unfold f
      rw [← hJ.2]
      congr
      simp
      congr)
    linarith


/-- The [CPT] [IY] button combination on the BA II Plus Financial. -/
noncomputable def CPT_IY_of_IY_nonneg {PMT PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) : ℝ :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose

noncomputable def CPT_IY {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hN : N ≠ 0) (hPMT : PMT ≥ 0) (hPV : PV < 0) (hFV : FV > 0)
    (h₀ : IY ≥ 0) :=
  CPT_IY_of_IY_nonneg hN hPMT (of_IY_nonneg hann h₀ hPMT hFV) hPV hFV


/-- [CPT] [IY] gives the only solution for interest rate per year. -/
lemma IY_eq_CPT_IY {PMT PV FV IY : ℝ} {N : ℕ} (hN : N ≠ 0)
    (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV)
    (hPV : PV < 0) (hFV : FV > 0) (hann : annuity_equation IY PMT PV FV N)
    (h₀ : IY > -100) : IY = CPT_IY_of_IY_nonneg hN hPMT h hPV hFV :=
  (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.2 _ ⟨h₀, hann⟩

noncomputable def CPT_PMT (IY PV FV : ℝ) (N : ℕ) :=
  (-PV - FV * (1 + IY / 100)⁻¹ ^ N) / annuity.a N (IY / 100)

lemma PMT_eq_CPT_PMT.aux {IY : ℝ} {N : ℕ}
    (h₀ : IY > -100) (hN : N ≠ 0)
    (h₂ : (100 / (100 + IY)) ^ N = 1 ^ N) : 100 / (100 + IY) = 1 := by
  have hα : 100 / (100 + IY) ≥ 0 := by
    apply div_nonneg
    · simp
    linarith
  generalize 100 / (100 + IY) = α at *
  rw [← Nonneg.mk_eq_one hα]
  simp only [one_pow, Nonneg.mk_eq_one] at h₂ ⊢
  exact (pow_eq_one_iff_of_nonneg hα hN).mp h₂


/-- [CPT] [PMT] gives the only solution for payment. -/
lemma PMT_eq_CPT_PMT {IY PMT PV FV : ℝ} {N : ℕ}
  (h : annuity_equation IY PMT PV FV N) (h₀ : IY > -100) (hN : N ≠ 0) :
  PMT = CPT_PMT IY PV FV (N) := by
  unfold annuity_equation at h
  have : annuity.a N (IY / 100) ≠ 0 := by
    by_cases H : IY = 0
    · unfold annuity.a annuity.geom_sum
      subst H
      simp
      tauto
    have := @annuity.a_eq_a_formula (IY / 100)
      (by contrapose! H; linarith) (by contrapose! h₀;linarith)
    rw [congrFun this]
    unfold annuity.a_formula
    simp
    constructor
    · field_simp
      contrapose! H
      have : ((100 + IY) / 100) ^ N ≠ 0 := by
        simp only [ne_eq, pow_eq_zero_iff', div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, not_and,
          Decidable.not_not]
        intro hh
        exfalso
        linarith
      field_simp at H
      simp at H
      ring_nf at H
      have : (1 + IY * (1 / 100)) ^ N = 1 := by linarith
      have : (1 + IY * (1 / 100)) = 1 := by
        have h₀ : (1 + IY * (1 / 100)) > 0 := by
            linarith
        generalize (1 + IY * (1 / 100)) = α at *
        apply (pow_eq_one_iff_of_nonneg _ _).mp this
        · linarith
        exact hN
      linarith
    · tauto
  unfold CPT_PMT
  grind


/--
Main theorem on unique solvability of the Annuity Equation.
To deduce interest rate we need time to pass,
and hence the number of periods N>0.
To deduce the payment there must be at least one payment,
and hence again N>0.
To deduce N, the coupon rate should not equal the yield rate and hence
`FV * (IY / 100) - PMT ≠ 0`.
These assumptions, together with appropriate positivity and negativity,
suffice for unique existence of all variables.
-/
theorem annuity_equation_unique_solvability {IY PMT PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY PMT PV FV N)
    (hPMT : PMT ≥ 0) (hPV : PV < 0) (hFV : FV > 0) (hIY : IY > 0) :
    ((hN : N ≠ 0) →
    PMT = CPT_PMT IY PV FV N ∧
    IY  = CPT_IY hann hN hPMT hPV hFV (le_of_lt hIY)) ∧
    PV  = CPT_PV IY PMT FV N ∧
    FV  = CPT_FV IY PMT PV N ∧ (FV * (IY / 100) - PMT ≠ 0 →
    N   = CPT_N IY PMT PV FV) := by
  have hI : IY > -100 := by linarith
  have hI₀ : IY ≠ 0 := by linarith
  have hI₁ : IY ≠ -100 := by linarith
  have hI₂ : IY / 100 ≠ -2 := by linarith
  constructor
  · intro hN
    constructor
    · exact PMT_eq_CPT_PMT hann hI hN
    exact IY_eq_CPT_IY _ _ (of_IY_nonneg hann (by linarith) hPMT hFV) _ _ hann hI
    -- exact IY_eq_CPT_IY _ _ (by apply of_IY_nonneg hann;linarith;tauto;tauto) _ _ hann hI₀
  · constructor
    · exact PV_eq_CPT_PV hann
    constructor
    · exact FV_eq_CPT_FV hann hI₁
    · exact N_eq_CPT_N hann hI₀ hI₁ hI₂


/-- By setting `PMT=0` we obtain the unique solvability of the
Time Value of Money equation. -/
theorem TVM_equation_unique_solvability {IY PV FV : ℝ} {N : ℕ}
    (hann : annuity_equation IY 0 PV FV N)
    (hPV : PV < 0) (hFV : FV > 0) (hIY : IY > 0) :
    ((hN : N ≠ 0) →
    0  = CPT_PMT IY PV FV N ∧
    IY = CPT_IY hann hN (by simp) hPV hFV (by linarith)) ∧
    PV = CPT_PV IY 0 FV N ∧
    FV = CPT_FV IY 0 PV N ∧
    N  = CPT_N IY 0 PV FV := by
  have hI₀ : IY > -100 := by linarith
  have hI₁ : IY ≠ -100 := by linarith
  have hI₂ : IY / 100 ≠ -2 := by linarith
  constructor
  · intro hN
    constructor
    · exact PMT_eq_CPT_PMT hann hI₀ hN
    exact IY_eq_CPT_IY _ _ _ _ _ hann hI₀
  · constructor
    · exact PV_eq_CPT_PV hann
    constructor
    · exact FV_eq_CPT_FV hann hI₁
    · exact N_eq_CPT_N hann (ne_of_gt hIY) hI₁ hI₂ (by
        simp
        constructor <;> linarith)

/-- CPT_IY returns a value satisfying the annuity equation. -/
lemma CPT_IY_satisfies {PV PMT FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (hFV : FV > 0) (hPV : PV < 0)
  (hPMT : PMT ≥ 0) (h : 0 ≤ PV + PMT * ↑N + FV) :
  let hann := (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1
  let IY := CPT_IY hann.2 hN hPMT hPV hFV hann.1
  annuity_equation IY PMT PV FV N :=
    (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1.2

-- of_IY_nonneg shows that `h` is equivalent to this happening:
lemma CPT_IY_satisfies_iff {PV PMT FV : ℝ} {N : ℕ} (hN : N ≠ 0)
  (hFV : FV > 0) (hPV : PV < 0)
  (hPMT : PMT ≥ 0) :
  0 ≤ PV + PMT * N + FV ↔
  ∃ IY ≥ 0,
  annuity_equation IY PMT PV FV N := by
    constructor
    · intro h
      let hann := (CPT_IY_unique hN hPMT h hPV hFV).choose_spec.1
      use CPT_IY hann.2 hN hPMT hPV hFV hann.1
      constructor
      · exact hann.1
      · exact CPT_IY_satisfies hN hFV hPV hPMT h
    · exact fun ⟨IY, hIY⟩ => of_IY_nonneg hIY.2 hIY.1 hPMT hFV



/-- If CPT_N returns a Nat then it satisfies the annuity equation.
(If it doesn't, we could prove it satisfies a modified annuity equation.)
-/
theorem CPT_N_satisfies {IY PMT PV FV : ℝ} (N : ℕ)
    (hIY₁ : IY / 100 > 0)
    (h_nonpar : PMT - FV * (IY / 100) ≠ 0) -- necessary if we're going to have hope computing N
    (hNat : N = CPT_N IY PMT PV FV) :
    0 < (PV * (IY/100) + PMT) / (PMT - FV * (IY/100)) ↔ annuity_equation IY PMT PV FV N := by
  constructor
  · intro hIY
    unfold annuity_equation
    rw [congrFun (@annuity.a_eq_a_formula (IY / 100) (by linarith) (by linarith)) N]
    unfold annuity.a_formula
    rw [natpow_rpow N (1 + IY / 100)⁻¹ (by simp;linarith)]
    unfold CPT_N at hNat
    rw [hNat]
    have hln : log (1 + IY / 100)⁻¹ ≠ 0 := by
      refine log_ne_zero_of_pos_of_ne_one ?_ ?_
      all_goals simp;linarith
    rw [div_mul, div_self hln]
    simp only [div_one]
    generalize IY / 100 = i at *
    rw [exp_log hIY]
    have : PMT - i * FV ≠ 0 := by rw [mul_comm];tauto
    field_simp
    ring_nf
  intro hann
  unfold annuity_equation at hann
  have := congrFun (@annuity.a_eq_a_formula (IY / 100) (by linarith) (by linarith)) N
  rw [this] at hann
  unfold annuity.a_formula at hann
  generalize IY / 100 = i at *
  have : (1 + i)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  generalize (1 + i)⁻¹ ^ N = x at *
  field_simp at hann
  have : PV * i + PMT  - (PMT - FV * i) * x = 0 := by
    linarith
  have h_nonpar' : PMT - i * FV ≠ 0 := by contrapose! h_nonpar;linarith
  have : x = (PV * i + PMT) / (PMT - FV * i) := by
    field_simp
    linarith
  rw [← this]
  tauto

theorem CPT_PV_satisfies {IY PMT FV : ℝ} {N : ℕ} :
    annuity_equation IY PMT (CPT_PV IY PMT FV N) FV N := by
  unfold CPT_PV annuity_equation
  linarith

theorem CPT_FV_satisfies {IY PMT PV : ℝ} {N : ℕ} (hIY : IY > -100) :
    annuity_equation IY PMT PV (CPT_FV IY PMT PV N) N := by
  unfold CPT_FV annuity_equation
  have : IY / 100 > -1 := by linarith
  generalize IY / 100 = i at *
  have : (1 + i)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  rw [div_mul]
  generalize (1 + i)⁻¹ ^ N = α at *
  field_simp
  linarith

theorem CPT_PMT_satisfies {IY PV FV : ℝ} {N : ℕ} (hN : N ≠ 0)
 (hIY : IY > -100) :
    annuity_equation IY (CPT_PMT IY PV FV N) PV FV N := by
  unfold CPT_PMT annuity_equation
  rw [div_mul]
  have : IY / 100 > -1 := by linarith
  have : annuity.a N (IY / 100) > 0 := annuity.annuity_positive hN this
  have : (1 + IY / 100)⁻¹ ^ N > 0 := by
    apply pow_pos <| inv_pos.mpr <| by linarith
  field_simp
  linarith

/-- If PV=0 and i=-1, the annuity equation holds for
PMT = CPT_PMT or any other PMT value. -/
theorem CPT_PMT_satisfies_when_PV_eq_zero {FV PMT : ℝ} {N : ℕ} (hN : N ≠ 0) :
    annuity_equation (-100) PMT 0 FV N := by
  simp only [annuity_equation, annuity.a, annuity.geom_sum, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, neg_div_self, add_neg_cancel, inv_zero, zero_add]
  rw [zero_pow_eq_zero.mpr hN]
  simp only [mul_zero, add_zero, mul_eq_zero]
  right
  have : ∑ x ∈ Icc 1 N, (0 ^ x : ℝ) = ∑ x ∈ Icc 1 N, (0 : ℝ) :=
    sum_congr rfl fun x hx => by
    simp at hx ⊢
    linarith
  rw [this]
  simp
