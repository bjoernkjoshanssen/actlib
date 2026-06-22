import Actlib.Aristotle_CPT_I
import Actlib.AristotleMagic
import Actlib.NFM
import Actlib.NFM_equiv
import Mathlib.Tactic.CancelDenoms.Core
/-!

## Five implicit functions from the Annuity Equation: duration version

The BA II Plus calculator values PMT, I/Y, N, FV, PV
can each be computed from the other four. Here we replace PV by D (duration)
for a speculative future calculator.

Main results:

* `eq_CPT_I_of_D`: if `D>1`, `n ≥ 2`, and `r>0` then we can uniquely
  compute the yield rate `i > -1` from the duration equation.
* `eq_CPT_N_of_D`: if `i,d,r>0` and `d<1+1/i` then we
can uniquely compute `n` from the duration equation.

-- * If d>1, n≥2, r>0, i>0 and d<1+1/i then i and n are both computed from
--   the others.
-/

open Finset Real Filter


/-

## DURATION

-/


open annuity

/-- Macaulay duration of a maturity `n`, level-payments bond (with redemption value 1)
with coupon rate `r` and yield rate `i`. -/
noncomputable def D : ℕ → ℝ → ℝ → ℝ := fun n i r =>
  (r * Ia n i + n * (1+i)⁻¹ ^ n) /
  bond_price n i r

/-- A bond with unit redemption value and maturity 1 has Macaulay duration 1. -/
lemma D_one {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D 1 i r = 1 := by
  unfold D Ia bond_price bond_price_sum geom_sum annuity.id_mul_geom_sum
  simp only [Icc_self, inv_pow, sum_singleton, Nat.cast_one, pow_one, one_mul, div_self_eq_one₀,
    ne_eq]
  have : (1 + i)⁻¹ > 0 := by
    simp
    linarith
  set v := (1+i)⁻¹
  have : r * v + v ≠ 0 := by
    apply ne_of_gt
    apply lt_of_le_of_lt (b := r * v)
    · positivity
    linarith
  field_simp
  simp
  constructor <;> linarith

/-- The Macaulay duration does indeed satisfy the duration equation. -/
lemma D_duration_equation (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) :
  duration_equation n i r (D n i r) := by
  unfold duration_equation D
  have := bond_price_pos n hi hr
  generalize bond_price n i r = b at *
  field_simp
  unfold Ia
  simp

/-- The maturity date as a trivial upper bound on the Macaulay duration. -/
lemma D_upper_bound (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) : D n i r ≤ n := by
  have h₄ := by apply bond_price_pos n hi hr
  unfold bond_price at h₄
  unfold bond_price_sum at *
  apply (div_le_iff₀ h₄).mpr
  suffices r * Ia n i ≤ r * (↑n * a n i) by
    unfold a at this
    linarith
  apply mul_le_mul_of_nonneg_left
  · unfold Ia a geom_sum
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro k hk
    simp only [mem_Icc] at hk
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · simp only [Nat.cast_le]
      exact hk.2
    apply pow_nonneg
    simp
    linarith
  exact hr

lemma D_upper_bound_strict {n : ℕ} (hn : n ≥ 2) {i r : ℝ} (hi : i > -1) (hr : r > 0) :
    D n i r < n := by
  have h₄ := by apply bond_price_pos n hi (by linarith)
  unfold bond_price at h₄
  unfold bond_price_sum at *
  apply (div_lt_iff₀ h₄).mpr
  suffices r * Ia n i < r * (↑n * a n i) by
    unfold a at this
    linarith
  suffices Ia n i < (↑n * a n i) by
    generalize Ia n i = α at *
    generalize n * a n i = β at *
    exact (mul_lt_mul_iff_of_pos_left hr).mpr this
  unfold Ia a geom_sum
  rw [Finset.mul_sum]
  apply sum_lt_sum
  · intro k hk
    simp only [mem_Icc] at hk
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · simp only [Nat.cast_le]
      exact hk.2
    apply pow_nonneg
    simp
    linarith
  use 1
  constructor
  · simp
    omega
  have : (1 + i)⁻¹ ^ 1 > 0 := by
    simp
    linarith
  generalize (1 + i)⁻¹ ^ 1 = v at *
  have : (1:ℝ) < (n:ℝ) := by simp;omega
  apply mul_lt_mul
  · convert this
    · rfl
    simp
  · simp
  · tauto
  · simp



/-- The duration of a bond is nonnegative. -/
lemma duration_nonneg (n : ℕ) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) :
    0 ≤ D n i r := by
  have h : 1 + i ≥ 0 := by linarith
  apply div_nonneg
  · apply add_nonneg <| mul_nonneg hr <| increasing_annuity_nonneg _ hi
    apply mul_nonneg <| Nat.cast_nonneg _
    apply pow_nonneg <| inv_nonneg.mpr h
  apply add_nonneg
  · exact mul_nonneg hr <| annuity_nonneg _ hi
  · apply pow_nonneg <| inv_nonneg.mpr h


/-- An at-par bond with unit (1) redemption value has price 1
as well, no matter what the maturity and interest rates are. -/
lemma par_bond_price (n : ℕ) {i : ℝ} (hi : i > 0) :
    bond_price n i i = 1 := by
  unfold bond_price bond_price_sum
  have := congrFun <| @a_eq_a_formula i (by linarith) (by linarith)
  unfold annuity.a at this
  rw [this]
  unfold a_formula
  field_simp
  linarith


/-- The maturity of an at-par bond with rate `i` and Macaulay duration `d`.
Note that the input to log is only positive if
d < 1 + 1 / i.
-/
noncomputable def CPT_N_of_D_par (i d : ℝ) :=
    log (1 - d * (1 - (1+i)⁻¹)) / log (1+i)⁻¹

/- The log 0 case, where d = 1 + 1 / i. -/
-- lemma eq_CPT_N_of_D_par_border (n : ℕ) {i : ℝ} (hi : i > 0) (d : ℝ)
-- (hn : n = CPT_N_of_D_par i (1 + 1 / i)) :
-- ¬ duration_equation n i i (1 + 1 / i) := by
--     unfold duration_equation
--     rw [hn]
--     unfold bond_price bond_price_sum Ia --geom_sum
--     rw [id_mul_geom_sum_formula]
--     unfold CPT_N_of_D_par
--     have : (1 - (1 + 1 / i) * (1 - (1 + i)⁻¹)) = 0 := by
--         sorry
--     rw [this]
--     simp
--     sorry
--     sorry


/-- Determine the maturity from the duration for an at-par bond. -/
lemma eq_CPT_N_of_D_par (n : ℕ) {i : ℝ} (hi : i > 0) (d : ℝ)
    (h : duration_equation n i i d) :
    n = CPT_N_of_D_par i d := by
    unfold CPT_N_of_D_par
    unfold duration_equation at h
    rw [par_bond_price n hi] at h
    unfold Ia annuity.id_mul_geom_sum at h
    have := @id_mul_geom_sum_formula (1+i)⁻¹ (by
        intro hc;simp only [inv_eq_one, add_eq_left] at hc;subst hc;simp at hi) n
    unfold id_mul_geom_sum at this
    rw [this] at h
    have : (1+i)⁻¹ ≠ 1 := by intro hc;simp at hc;linarith
    have : ((1+i)⁻¹ - 1)^2 ≠ 0 := by
        contrapose! this;simp at this;linarith
    have h₀ : i * (1+i)⁻¹ = 1 - (1+i)⁻¹ := by
        field_simp
        linarith
    have : (1+i)⁻¹ - 1 ≠ 0 := by
        contrapose! this
        rw [this]
        simp
    have : 1 - (1+i)⁻¹ ≠ 0 := by
        contrapose! this
        linarith
    have : i * (1+i)⁻¹ ≠ 0 := by
        simp;constructor <;> linarith
    have hiv : i = ((1+i)⁻¹)⁻¹ - 1 := by field_simp;linarith
    have hivn : log ((1+i)⁻¹ ^ n) = n * log (1+i)⁻¹ := by
        simp
    have hlogv : log (1+i)⁻¹ ≠ 0 := by
        simp
        constructor
        · linarith
        constructor <;> linarith
    have : (1+i)⁻¹ ≠ 0 := by simp;linarith
    set v := (1+i)⁻¹
    field_simp at h
    ring_nf at h
    set y := v^n
    have h :  d * (1-v) ^ 2 - v * i +
        y * (i * v * (1 + (1-v) * ↑n)
        -n * (1-v)^2) = 0 := by linarith [v,y]
    rw [h₀] at h
    have :  d * (1 - v) ^ 2 - v * i + y * ((1 - v)) = 0
        := by linarith
    have : y = (v * i - d * (1 - v) ^ 2)/ ((1 - v)) := by
        field_simp
        linarith
    have hv : v / (1 - v) = 1/i := by
        rw [← h₀];field_simp
    have : y = (v * i - d * (1 - v) ^ 2)/ ((1 - v)) := by
        field_simp
        linarith
    have : y = i * (v / (1 - v))  - d * (1-v):= by
        field_simp
        linarith
    rw [hv] at this
    field_simp at this
    have : log y = log (1 - d * (1-v)) := by rw [this]
    rw [hivn] at this
    rw [← this]
    field_simp

/-- Present value of an increasing annuity with interest rate 0. -/
lemma increasing_annuity_zero {n : ℕ} :
    annuity.Ia n 0 = (n+1) * n / 2 := by
  unfold annuity.Ia annuity.id_mul_geom_sum
  simp only [add_zero, inv_one, one_pow, mul_one]
  have h := Finset.sum_range_id n
  have : ∑ i ∈ range n, (i:ℝ)
    = ((∑ i ∈ range n, i) : ℝ) := by
    congr
  let α : ℕ := ∑ i ∈ range (n+1), i
  let β : ℕ := (n+1) * (n+1 - 1) / 2
  have : α = β := Finset.sum_range_id (n+1)
  have hα : (α : ℝ) = (β : ℝ) := by
    rw [this]
  have := @sum_Icc_succ_eq_sum_range (fun n => n) n
  simp only [CharP.cast_eq_zero, zero_add] at this
  rw [this]
  unfold α at hα
  simp only [Nat.cast_sum] at hα
  rw [hα]
  unfold β
  cases Nat.even_or_odd n with
  | inl h =>
    choose k hk using h
    subst hk
    simp only [add_tsub_cancel_right, Nat.cast_add]
    repeat rw [← Nat.two_mul, ← two_mul]
    have : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by ring_nf
    rw [this]
    simp
    ring_nf
  | inr h =>
    choose k hk using h
    subst hk
    simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have : (2 * k + 1 + 1) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) := by ring_nf
    rw [this]
    simp
    ring_nf

/-- A pleasant formula for the Macaulay duration of a zero-yield bond
    in terms of the coupon rate `r` and maturity `n`.
    Note that when `r=0` it reduces to `d=n`. -/
lemma duration_yield_zero {n : ℕ}
    (hn : n ≠ 0)
    {d : ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : duration_equation n 0 r d) :
    d = (r*(n+1)*n/2 + n) / (r*n + 1) := by
  unfold duration_equation
    annuity.bond_price
    annuity.bond_price_sum
    annuity.geom_sum
    at h
  simp only [add_zero, inv_one, one_pow, sum_const, Nat.card_Icc, add_tsub_cancel_right,
    nsmul_eq_mul, mul_one] at h
  rw [increasing_annuity_zero] at h
  have : r * n + 1 ≠ 0 := by
      apply ne_of_gt
      positivity
  field_simp
  linarith


lemma annuity_bond_price_ne_zero {n : ℕ} (hnn : n > 1) {i r : ℝ} (hi : i > -1) (hr : r ≥ 0) :
    annuity.bond_price n i r ≠ 0 := by
  apply ne_of_gt
  calc _ < 0 + (1 + i)⁻¹ ^ n := by simp only [inv_pow, zero_add, inv_pos];apply pow_pos;linarith
        _ ≤ _ := add_le_add
          (mul_nonneg hr <| le_of_lt <| geom_sum_positive hnn hi) <| le_refl _

lemma eq_D_of_duration_equation {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hi : i > -1) (hr : r ≥ 0)
    (hann : duration_equation n i r d) : d = D n i r := by
  apply mul_right_cancel₀ (annuity_bond_price_ne_zero hnn hi hr)
  have hdur := D_duration_equation n (by linarith : i > -1) hr
  unfold duration_equation at hann hdur
  linarith

lemma duration_bounded_by_maturity {n : ℕ} (hnn : n > 1) {i d r : ℝ} (hi : i > -1) (hr : r ≥ 0)
    (hann : duration_equation n i r d) : d ≤ n :=
  eq_D_of_duration_equation hnn hi hr hann ▸ D_upper_bound n hi hr


/-- For a bond with maturity `n=2`, explicitly find the yield rate `i`
  from the Macaulay duration `d`
  and the coupon rate `r`. For larger `n` it is not generally uniquely solvable.
  `n=3` might be an interesting quadratic equation.
  Note that if i=r, (d-1)r = 2-d, i.e., i = (2-d)/(d-1).
-/
lemma eq_CPT_I_of_D_maturity2
    {i d r : ℝ} (hi : i > -1) (hd : 1 ≠ d) (hri : r > 0)
    (h : duration_equation 2 i r d) :
    i = (2 - d) * (r + 1)
     / ((d - 1) * r) - 1 := by
  have : d < 2 := by
    have := @eq_D_of_duration_equation 2 (by simp) i d r hi (le_of_lt hri) h
    rw [this]
    exact D_upper_bound_strict (by simp) hi hri
  set v := (1+i)⁻¹
  unfold duration_equation annuity.bond_price
    annuity.bond_price_sum annuity.Ia annuity.geom_sum annuity.id_mul_geom_sum at h
  repeat rw [Finset.sum_Icc_succ_top] at h
  · simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty, zero_add, pow_one, Nat.reduceAdd,
      Nat.cast_one, one_mul, Nat.cast_ofNat] at h
    ring_nf at h
    have hv : v ≠ 0 := by
        simp [v]
        linarith
    have : (d-2) * (r+1) * v + (d-1) * r = 0 :=
        (mul_eq_zero_iff_left hv).mp <| by linarith
    have hβ : (d-2) * (r+1) ≠ 0 := by simp; constructor <;> linarith
    have hγ : (1-d)*r       ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, not_or]
      constructor
      · contrapose hd
        linarith
      linarith
    have : v = (- (d-1) * r) / ((d-2) * (r+1)) := by
      have := Mathlib.Tactic.CancelDenoms.cancel_factors_eq_div
        (h2 := hβ) (e := v) (e' := -(d - 1) * r)
      rw [this]
      linarith
    field_simp [v] at this
    unfold v at this
    field_simp at this
    have h₃ : (1+i) ≠ 0 := by linarith
    have h₀ : (1+i)⁻¹ ≠ 0 := by simp;tauto
    have h₁ : d-1≠0 := by contrapose! hd;linarith
    have h₂ : d-2≠0 := by linarith
    field_simp at this ⊢
    linarith
  all_goals simp


lemma deriv_bond_price_sum {n : ℕ} (r x : ℝ) :
    deriv (annuity.bond_price_sum n r) x =
    r * ∑ k ∈ Icc 1 n, k * x ^ (k - 1) + n * x ^ (n - 1) := by
  unfold annuity.bond_price_sum annuity.geom_sum
  rw [deriv_fun_add]
  · simp
  · apply Differentiable.differentiableAt
    apply Differentiable.mul <;> simp
  apply Differentiable.differentiableAt
  simp


open Filter Finset

/-- Inferring the interest rate from the maturity,
duration, and coupon rate. With great help from Aristotle. -/
lemma eq_CPT_I_of_D {n : ℕ} (hnn : n ≥ 2) {i d r : ℝ} (hd : d ∈ Set.Ioo (1 : ℝ) n)
    (hr : r > 0) :
    ∃! i > -1, duration_equation n i r d := by
  unfold duration_equation
    annuity.bond_price
  set v := (1+i)⁻¹
  let F := fun v => d * annuity.bond_price_sum n r v -
      (r * annuity.id_mul_geom_sum n v + ↑n * v ^ n)
  have ⟨v,hv⟩ := @unique_root_f n hnn d r hd.1 hd.2 hr
  use 1/v-1
  simp only [f, and_imp, one_div, gt_iff_lt, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, inv_pos,
    add_sub_cancel, inv_inv, inv_pow] at hv ⊢
  constructor
  · constructor
    · tauto
    · unfold annuity.bond_price_sum annuity.geom_sum annuity.Ia annuity.id_mul_geom_sum
      convert hv.1.2
      field_simp
      have : v ≠ 0 := by linarith
      ring_nf
      field_simp
  intro i hi h
  unfold annuity.bond_price_sum annuity.geom_sum annuity.Ia annuity.id_mul_geom_sum at h
  have := hv.2 (1 / (1 + i)) (by
    apply div_pos
    · simp
    linarith) (by
    simp only [inv_pow, one_div] at h ⊢
    exact h)
  rw [← this]
  field_simp at this ⊢
  linarith







/-- Aristotle's proof. -/
theorem eq_CPT_N_of_D.helper₀ {n : ℕ} (hnn : n > 1) {i r : ℝ} (hi : i > 0) (hri : r ≥ i) :
  (r * (∑ k ∈ Finset.Icc 1 n, (k : ℝ) * (1 + i)⁻¹ ^ k) + (n : ℝ) * (1 + i)⁻¹ ^ n) /
  (r * (∑ k ∈ Finset.Icc 1 n, (1 + i)⁻¹ ^ k) + (1 + i)⁻¹ ^ n) < 1 + 1 / i := by
    rw [ add_div', div_lt_div_iff₀ ] <;> try positivity;
    · -- We'll use the fact that <|\sum_{k=1}^n kx^k = x \frac{1 - (n+1)x^n + nx^{n+1}}{(1-x)^2}<|.
      have h_sum_formula : ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * (1 + i)⁻¹ ^ k
        = (1 + i)⁻¹ * (1 - (n + 1) * (1 + i)⁻¹ ^ n + n * (1 + i)⁻¹ ^ (n + 1))
        / (1 - (1 + i)⁻¹) ^ 2 :=
        eq_div_of_mul_eq (pow_ne_zero 2 <| by nlinarith [inv_mul_cancel₀ (by linarith : 1 + i ≠ 0)])
          <| Nat.recOn n (by norm_num) fun n ihn => by
            norm_num [pow_succ, Finset.sum_Ioc_succ_top,
              (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
            nlinarith [inv_mul_cancel₀ (by linarith : (1 + i) ≠ 0)]
      -- We'll use the fact that <|\sum_{k=1}^n x^k = \frac{x - x^{n+1}}{1 - x}<|.
      have h_sum_formula2 : ∑ k ∈ Finset.Icc 1 n, (1 + i)⁻¹ ^ k = (1 + i)⁻¹ * (1 - (1 + i)⁻¹ ^ n)
        / (1 - (1 + i)⁻¹) := by
        erw [ geom_sum_Ico ] <;> norm_num [ hi.ne' ];
        -- Combine and simplify the fractions
        field_simp
        ring;
      field_simp [h_sum_formula, h_sum_formula2] at *;
      rw [ h_sum_formula, h_sum_formula2 ] ; ring_nf ; norm_num;
      field_simp at *; ring_nf at *; (
      nlinarith [
          show 0 < i ^ 2 * n by positivity,
          show 0 < i * n by positivity,
          show (1 + i) ^ n > 1 by exact one_lt_pow₀ (by linarith) (by linarith) ]);
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith)
        (Finset.sum_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (by linarith)) _))
        (pow_pos (inv_pos.2 (by linarith)) _)


/-- Incorporate Aristotle's `inequality_proof` into our setting. -/
lemma eq_CPT_N_of_D.helper {n : ℕ} (hnn : n > 1)
    {i d r : ℝ} (hi : i > 0) (hri : r ≥ i)
    (hann : duration_equation n i r d) :
     d < 1 + 1 / i :=
  eq_D_of_duration_equation hnn (by linarith) (by linarith : r ≥ 0) hann
     ▸ eq_CPT_N_of_D.helper₀ hnn hi hri

/-- This version does not assume r<i or r>i. -/
noncomputable def CPT_N_of_D {i d r : ℝ} (hd : 0 < d) (hi : i > 0)
  (hr : r > 0)
  (hdi : d < 1 + 1 / i) : ℝ :=
  (AriMagic.unique_solution_n hd hi hr hdi).choose

/--
A temporary lemma to prove that the equation presented to Aristotle
is indeed the duration equation. -/
lemma equation_presented_to_aristotle {n : ℕ} {i d r : ℝ} (hi : i > 0)
    (hann : duration_equation n i r d) :
    d * (r * ((1 - (1 + i)⁻¹ ^ (n:ℝ)) / i) + (1 + i)⁻¹ ^ (n:ℝ)) -
    (r * ((1 + i)⁻¹ * ((n:ℝ) * (1 + i)⁻¹ ^ ((n:ℝ) + 1) - (↑n + 1) * (1 + i)⁻¹ ^ (n:ℝ) + 1) /
    ((1 + i)⁻¹ - 1) ^ 2) + (n:ℝ) * (1 + i)⁻¹ ^ (n:ℝ)) = 0 := by
  unfold duration_equation bond_price
    bond_price_sum geom_sum Ia annuity.id_mul_geom_sum at hann
  rw [← hann]
  have : (1+i)⁻¹ ≠ 0 := by simp;linarith
  have : (1+i)⁻¹ ≠ 1 := by simp;linarith
  set v := (1+i)⁻¹
  have temp :=id_mul_geom_sum_formula _ this
  unfold id_mul_geom_sum at temp
  rw [temp]
  have : ∑ k ∈ Icc 1 n, v ^ k
    = (1-v^(n)) / i := by
    have := congrFun <| @annuity.a_eq_a_formula i (by linarith) (by linarith)
    unfold a geom_sum a_formula at this
    rw [this]
  rw [this]
  have h₀ : v ^ (n:ℝ) = v ^ n := by norm_num
  rw [h₀]
  have : v ^ ((n:ℝ) + 1) = v ^ (n+1) := by
    have : v ^ (n + 1) = v^n * v := rfl
    rw [this]
    rw [← h₀]
    refine rpow_add_one ?_ ↑n
    tauto
  rw [this]


lemma eq_CPT_N_of_D {n : ℕ} (hnn : (n : ℝ) > 0)
    {i d r : ℝ} (hd : 0 < d) (hi : 0 < i)
    (hr : 0 < r) (hdi : d < 1 + 1 / i)
    (hann : duration_equation n i r d) :
    n = @CPT_N_of_D i d r hd hi hr hdi := by
    have := (AriMagic.unique_solution_n hd hi hr hdi).choose_spec.2
    simp only [and_imp, CPT_N_of_D] at this ⊢
    exact this n hnn (equation_presented_to_aristotle hi hann)


-- Try to CPT_I when N is also unknown
-- lemma CPT_I_of_PV_DUR
--     {n₁ n₂ : ℕ}
--     {i₁ i₂ DUR r PMT PV FV : ℝ}
--     (hr : 0 < r)
--     (hPMT: 0 < PMT)
--     (hFV : 0 < FV)
--     (hPV : PV < 0)
--     (hDUR : 1 < DUR)
--     (hDUR₁ : DUR < n₁)
--     (hDUR₂ : DUR < n₂)
--     (hi₁ : i₁ > 0) (hdi₁ : DUR < 1 + 1 / i₁)
--     (hi₂ : i₂ > 0) (hdi₂ : DUR < 1 + 1 / i₂)
--     (h : duration_equation n₁ i₁ (PMT / FV) DUR
--     ∧ annuity_equation (100 * i₁) PMT PV FV n₁
--     ∧ duration_equation n₂ i₂ (PMT / FV) DUR
--     ∧ annuity_equation (100 * i₂) PMT PV FV n₂) :
--     n₁ = n₂ ∧ i₁ = i₂
--      := by
--     unfold annuity_equation
--         duration_equation bond_price bond_price_sum
--             geom_sum at h
--     have : 100 * i₁ / 100 = i₁ := by sorry
--     rw [this] at h
--     clear this
--     have : 100 * i₂ / 100 = i₂ := by sorry
--     rw [this] at h
--     clear this
--     sorry
