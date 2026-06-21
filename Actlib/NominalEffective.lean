import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real


import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Chan & Tse Exercise 1.1
-/

-- Wrong:
#eval 20000 * (1.08)^4

-- RIght:
#eval (20000
  * ((1 + ((0.08) / 2)) ^ 2)
  * ((1 + ((0.08) / 4)) ^ 4)
  * ((1 + ((0.08) / 6)) ^ 6)
  * ((1 + ((0.08) / 12)) ^ 12)
  )

/-!
# Chan & Tse Exercise 1.2
-/

open Real


lemma neg_log {w : ℝ} (h₂ : w ≠ 0) (this : 1 - w > 0) : w < -log (1 - w) := by
  suffices log (1 - w) < - w by linarith
  have h₁ : 1 - w = 1 + (-w) := by linarith
  rw [h₁]
  apply exp_lt_exp.mp
  rw [exp_log (by linarith), add_comm]
  exact add_one_lt_exp <| by contrapose! h₂; linarith


/-- Here we start to work with `-1 < u ≠ 0`
instead of `0 < u`. -/
lemma exercise_1_2_chan_tse_pos {u x : ℝ} (hu : -1 < u) (hu₀ : u ≠ 0) (hx : 1 < x) :
  0 < rexp (x * log (1 + u / x)) * (log (1 + u / x) + x * ((1 + u / x)⁻¹ * (-u / x ^ 2))) := mul_pos (exp_pos _) <| by
  suffices x * ((1 + u / x)⁻¹ * (u / x ^ 2)) < log (1 + u / x) by
    simp at this ⊢
    ring_nf at this ⊢
    linarith
  have hxu : 0 < x + u := by linarith
  have : x * ((1 + u / x)⁻¹ * (u / x ^ 2))
    = ((1 + u / x)⁻¹ * (u / x)) := by
      rw [pow_two]
      field_simp
      ring_nf
  rw [this]
  have h₃ : u / x + 1 ≠ 0 := ne_of_gt <| by
    clear this
    field_simp
    linarith
  have h₀ : 1 + u / x ≠ 0 := by
    contrapose! h₃
    linarith
  have h₂ : u / (x + u) ≠ 0 := by
    apply div_ne_zero hu₀ <| ne_of_gt hxu
  have hpaper:  (1 + u / x)⁻¹ * (u / x) = u / (x + u) := by
      field_simp
      ring_nf
  rw [hpaper]
  have : 1 + u / x = (x + u) / x := by field_simp
  rw [this]
  have : log ((x + u)/ x) = - log (x / (x + u)) := by
    rw [log_div, log_div]
    all_goals linarith
  rw [this]
  have : x / (x + u) = 1 - (u / (x + u)) := by
    field_simp
  rw [this]
  have : 1 - u / (x + u) > 0 := by
    field_simp
    exact hxu
  apply neg_log h₂ this

lemma exercise_1_2_chan_tse_deriv₀ {u x : ℝ} (hu : -1 < u)
  (hu₀ : u ≠ 0)
  (hx : 1 < x) :
  0 < deriv (fun t ↦ rexp (t * log (1 + u / t))) x := by
  have H₀ : x ≠ 0 := by linarith
  have H₁ : 0 < x := by linarith
  have H :  DifferentiableAt ℝ (fun t ↦ u / t) x := DifferentiableAt.div (by simp) (by simp) H₀
  have H' : DifferentiableAt ℝ (fun t ↦ 1 + u / t) x := DifferentiableAt.add (by simp) H
  have H₂ : 1 + u / x ≠ 0 := by
    field_simp
    apply ne_of_gt
    linarith
  conv =>
    right; left
    change rexp ∘ fun t => t * log (1 + u / t)
  rw [deriv_comp, Real.deriv_exp]
  conv =>
    right; right; left
    change (fun t => t) * (fun t => log (1 + u / t))
  rw [deriv_mul]
  conv =>
    right; right; right; right; left
    change log ∘ fun t => 1 + u / t
  rw [deriv_comp, deriv_log]
  conv =>
    right; right; right; right; right; left
    change (fun t => 1) + fun t => u / t
  rw [deriv_add]
  simp
  conv =>
    right;right;right;right;right;left
    change (fun t => u) / fun t => t
  rw [deriv_div]
  simp
  apply exercise_1_2_chan_tse_pos
  linarith
  tauto
  exact hx

  exact differentiableAt_const u
  simp
  exact H₀
  exact differentiableAt_const 1
  exact H
  exact differentiableAt_log H₂
  exact H'
  simp
  exact DifferentiableAt.log H' H₂
  exact DifferentiableAt.exp (by simp)
  exact DifferentiableAt.mul (by simp) <| DifferentiableAt.log H' H₂


lemma exercise_1_2_chan_tse_deriv {u : ℝ} (hu : -1 < u)
  (hu₀ : u ≠ 0) :
  ∀ x ∈ interior (Set.Ici 1), 0 < deriv (fun t ↦ (1 + u / t) ^ t) x := by
  intro x hx; simp at hx
  have : deriv (fun t ↦ (1 + u / t) ^ t) x
       = deriv (fun t => rexp (t * log (1 + u / t))) x :=
       Filter.EventuallyEq.deriv_eq <| eventually_eventuallyEq_nhds.mp <|
        eventually_mem_nhds_iff.mpr <| mem_interior_iff_mem_nhds.mp <| by
        suffices Set.Ioi 1 ⊆ interior {x | (fun x ↦ (fun t ↦ (1 + u / t) ^ t) x = (fun t ↦ rexp (t * log (1 + u / t))) x) x} by
          apply this
          simp
          exact hx
        simp
        suffices  Set.Ioi 1 ⊆ {x | (1 + u / x) ^ x = rexp (x * log (1 + u / x))} by
          refine (IsOpen.subset_interior_iff ?_).mpr this
          exact isOpen_Ioi
        intro y hy
        simp at hy ⊢
        rw [mul_comm]
        apply rpow_def_of_pos <| by
          field_simp
          linarith
  rw [this]
  apply exercise_1_2_chan_tse_deriv₀
  linarith
  tauto
  exact hx




-- -- see also @Real.one_sub_div_pow_le_exp_neg
theorem effInt_increasing {k u w : ℝ}
  (hu : -1 < u)
  (hu₀ : u ≠ 0)
  (hw : 1 ≤ w) (h : w < k) :
  let f := fun t ↦ (1 + u / t) ^ t;
  f w < f k := by
  intro f
  apply strictMonoOn_of_deriv_pos
  · exact convex_Ici w
  · apply (continuousOn_congr (by
      show Set.EqOn (fun t ↦ rexp (t * log (1 + u / t))) (fun t ↦ (1 + u / t) ^ t) (Set.Ici w)
      intro t ht
      simp at ht
      simp
      rw [mul_comm]
      refine Eq.symm (rpow_def_of_pos ?_ t)
      have : 0 < 1 + u / t := by
        have : 1 ≤ t := by linarith
        field_simp
        linarith

      exact this)).mp
    exact ContinuousOn.rexp <| by
      apply ContinuousOn.mul (continuousOn_id' (Set.Ici w))
      apply ContinuousOn.log
      apply ContinuousOn.add continuousOn_const
      apply ContinuousOn.div continuousOn_const (continuousOn_id' _)
      · intro x hx;simp at hx;linarith
      · intro x hx
        simp at hx
        have : 1 ≤ x := by linarith
        field_simp
        linarith
  suffices  ∀ x ∈ interior (Set.Ici 1), 0 < deriv f x by
    intro x hx
    apply this
    simp at hx ⊢
    linarith
  apply exercise_1_2_chan_tse_deriv
  linarith
  tauto
  simp
  simp
  linarith
  tauto



theorem rational_exponent_interest_le_integer {ε m n k : ℝ} (hε : 0 < ε) (hk : 1 < k)
  (hn : 0 < n) (hm : 0 < m) :
  (1 + ε/m) ^ (n + 1 / k) <
  (1 + ε/m) ^ n * (1 + ε/(k * m)) ^ 1 := by
  have : (1 + ε / m) ^ (n + 1 / k)
    = (1 + ε / m) ^ (n) * (1 + ε / m) ^ (1 / k) := by
    refine rpow_add' ?_ ?_
    positivity
    apply ne_of_gt
    apply add_pos
    tauto
    simp
    linarith
  rw [this]
  suffices  (1 + ε / m) ^ (1 / k) < (1 + ε / (k * m)) ^ 1 by
    refine (mul_lt_mul_left ?_).mpr this
    refine rpow_pos_of_pos ?_ n
    apply add_pos
    simp
    apply div_pos <;> tauto
  have hr {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ (c) < b ^ (c)) : a < b := by
      clear this hm hn hk hε ε m n k
      exact (@rpow_lt_rpow_iff a b c (by linarith) (by linarith)
        (by tauto)).mp h
  suffices  ((1 + ε / m) ^ (1 / k)) ^ k < ((1 + ε / (k * m)) ^ 1) ^ k by
    apply hr
    · apply rpow_pos_of_pos
      apply add_pos (by simp)
      apply div_pos <;> tauto
    · simp
      apply add_pos
      · simp
      · apply div_pos
        · tauto
        · apply mul_pos <;> linarith
    · show 0 < k
      linarith
    exact this
  have :  ((1 + ε / m) ^ (1 / k)) ^ k
    =  (1 + ε / m) ^ ((1 / k) * k) := by
      rw [rpow_mul]
      apply add_nonneg (by simp)
      apply div_nonneg <;> linarith
  rw [this]
  simp
  rw [inv_mul_cancel₀ (by linarith)]
  rw [div_mul_eq_div_div_swap]
  have hu : 0 < ε / m := by apply div_pos;tauto;tauto
  generalize ε / m = u at *
  let f : ℝ → ℝ := fun t => (1 + u / t) ^ t
  suffices f 1 < f k by
    unfold f at this
    convert this
    simp
  apply effInt_increasing
  linarith
  linarith
  simp
  tauto

lemma chan_tse_exercise_1_2 (ε : ℝ) (hε : 0 < ε) :
  (1 + ε/4) ^ ((8:ℝ) + 1/3) <
  (1 + ε/4) ^ (8:ℝ) * (1 + ε/(3 * 4)) ^ 1 := by
    exact @rational_exponent_interest_le_integer ε 4 8 3 hε (by simp) (by simp) (by simp)


/-- Exercise 1.3
`h1_3₁` means the `first` assumption stated in `1.3` and so on.
-/
lemma chan_tse_1_3 {A I i : ℝ → ℝ}
  (h1_3₁ : A 4 = 1200)
  (h1_3₂ : ∀ t, i t = t ^ 2 / 100)
  (h1_10₁ : ∀ t, I t = A (t - 1) * i t)
  (h1_10₂ : ∀ t, I t = A t - A (t - 1)) :
  I 5 = 300 ∧ A 6 = 2040 := by
  have h₅ : (5:ℝ) - 1 = 4 := by linarith
  have h₆ : (6:ℝ) - 1 = 5 := by linarith
  have h₀ : I 5 = 300 := by
    rw [h1_10₁, h₅, h1_3₁, h1_3₂]
    linarith
  have h₁ : A 5 = 1500 := by
    specialize h1_10₂ 5
    rw [h₅] at h1_10₂
    linarith
  constructor
  · exact h₀
  · have h₅ : I 6 = A 6 - A 5 := by convert h1_10₂ 6;linarith
    rw [h1_10₁ 6, h1_3₂, h₆, h₁] at h₅
    linarith

lemma chan_tse_1_4 {A I i : ℝ → ℝ}
  (h1_4₀ : A 0 = 300)
  (h1_4₁ : I 1 = 5)
  (h1_4₂ : I 2 = 7)
  (h1_4₃ : I 3 = 9)
  (h1_4₄ : I 4 = 14)
  (h1_10₁ : ∀ t, I t = A (t - 1) * i t)
  (h1_10₂ : ∀ t, I t = A t - A (t - 1)) :
  A 3 = 321 ∧ i 4 = 14 / 321 := by
  have g₁ := h1_10₂ 1
  have g₂ := h1_10₂ 2
  have g₃ := h1_10₂ 3
  have g₄ := h1_10₂ 4
  simp at g₁
  have hA₁ : A 1 = 305 := by
    linarith
  rw [show (2:ℝ)-1=1 by linarith] at g₂
  rw [show (3:ℝ)-1=2 by linarith] at g₃
  have hA₂ : A 2 = 312 := by
    linarith
  have hA₃ : A 3 = 321 := by linarith
  constructor
  · exact hA₃
  · have h := h1_10₁ 4
    rw [show (4:ℝ)-1=3 by linarith, h1_4₄, hA₃] at h
    rw [h]
    simp

/--
The solutions to `1.5(a)(b)(c)(d)(e)(f)` have been verified with
Google calculator and the back of the book in Chan and Tse!

Note that *simple* discount is not compound.
This answer is equal to 1315.78947368
-/
lemma chan_tse_exercise_1_5_a {A : ℝ → ℝ} (h₀ : A 0 = 1000) (d : ℝ)
  (hd : d = 6e-2) (h : ∀ t k, A t = A (t + k) * (1 - d * k)) :
  A 4 = 1000 / (1 - 6e-2 * 4) := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]
  field_simp

lemma chan_tse_exercise_1_5_b {A : ℝ → ℝ} (h₀ : A 0 = 1000) (i : ℝ)
  (hd : i = 6e-2) (h : ∀ t k, A (t + k) = A t * (1 + i * k)) :
  A 4 =  1000 * (1 + 6e-2 * 4) := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]

lemma chan_tse_exercise_1_5_c {A : ℝ → ℝ} (h₀ : A 0 = 1000) (i : ℝ)
  (hd : i = 6e-2) (h : ∀ t k, A (t + k) = A t * (1 + i) ^ k) :
  A 4 = 1000 * (1 + 6e-2) ^ 4 := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]

lemma chan_tse_exercise_1_5_d {A : ℝ → ℝ} (h₀ : A 0 = 1000) (i : ℝ)
  (hd : i = 6e-2) (h : ∀ t k, A (t + k) = A t * (1 + i/4) ^ (4*k)) :
  A 4 = 1000 * (1 + 6e-2 / 4) ^ (16 : ℝ) := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]
  congr
  linarith

lemma chan_tse_exercise_1_5_e {A : ℝ → ℝ} (h₀ : A 0 = 1000) (d : ℝ)
  (hd : d = 6e-2) (h : ∀ t k, A t = A (t + k) * (1 - d/12) ^ (12*k)) :
  A 4 =  1000 * (1 - 6e-2 / 12) ^ (- (48:ℝ)) := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]
  rw [mul_assoc]
  have : (12:ℝ) * 4 = 48 := by linarith
  rw [this]
  field_simp
  left
  rw [mul_comm]
  rfl

lemma chan_tse_exercise_1_5_f {A : ℝ → ℝ} (h₀ : A 0 = 1000) (i : ℝ)
  (hd : i = 6e-2) (h : ∀ t k, A (k + t) = A (t) * rexp (i * k)):
  A 4 = 1000 * rexp (6e-2 * 4) := by
  have h₁ := h 0 4
  simp at h₁
  rw [h₀, hd] at h₁
  rw [h₁]

/-- We calculate `i 2` but not `i 3` since it's similar.
Google says
(log (2 + e) + 2 ^ (3 / 10) / 20) / (log (1/2 + e) + 1/20) - 1 =
0.31870400583 but
(ln (2 + e) + 2 ^ (3 / 10) / 20) / (ln (1/2 + e) + 1/20) - 1 =
0.32338276212
and
book says 32.34%.
-/
lemma chan_tse_exercise_1_6_a₁ {a i : ℝ → ℝ}
  (h1_6 : ∀ t, a t = log (t^2 / 2 + exp 1) + t^((3:ℝ) / 10) / 20)
  (h1_10₃ : ∀ t, a t = (1 + i t) * a (t - 1)) :
  i 2 = (log (2 + rexp 1) + 2 ^ ((3:ℝ) / 10) / 20) /  (log (2⁻¹ + rexp 1) + 20⁻¹) - 1 := by
    have := h1_10₃ 2
    rw [show (2:ℝ)-1 = 1 by linarith] at this
    rw [h1_6 1, h1_6 2] at this
    simp at this
    have h₀ : (2 : ℝ) ^ 2 / 2 = 2 := by field_simp;linarith
    rw [h₀] at this
    have hr : 1 < rexp 1 := one_lt_exp_iff.mpr (by simp)
    have h₁ : log (2⁻¹ + rexp 1) + 20⁻¹ ≠ 0 := ne_of_gt <| add_pos (log_pos (by linarith)) (by linarith)
    suffices 1 + i 2 = (log (2 + rexp 1) + ((2:ℝ) ^ ((3:ℝ) / 10)) / 20)
      / (log (2⁻¹ + rexp 1) + 20⁻¹) by linarith
    exact eq_div_of_mul_eq h₁ this.symm

lemma chan_tse_exercise_1_6_a₂ {a i : ℝ → ℝ}
    (h1_6 : ∀ t, a t = log (t^2 / 2 + exp 1) + t^((3:ℝ) / 10) / 20)
    (h1_10₃ : ∀ t, a t = (1 + i t) * a (t - 1)) :
    i 3 = ( log ((3:ℝ) ^ 2 / 2 + rexp 1) + 3 ^ ((3:ℝ) / 10) / 20) / (log (2 ^ 2 / 2 + rexp 1) + 2 ^ ((3:ℝ) / 10) / 20) - 1 := by
  have := h1_10₃ 3
  rw [show (3:ℝ)-1 = 2 by linarith] at this
  rw [h1_6 2, h1_6 3] at this
  generalize log ((3:ℝ)^2 / 2 + rexp 1) + (@HPow.hPow ℝ ℝ ℝ instHPow 3 (3 / 10) : ℝ) / 20 = β at *
  generalize i 3 = j at *
  suffices 1 + j = β / (log ((2:ℝ) ^ 2 / 2 + rexp 1) + ((2 : ℝ) ^ ((3:ℝ) / 10) / 20)) by linarith
  generalize 1 +j = k at *
  refine eq_div_of_mul_eq ?_ (id (Eq.symm this))
  apply ne_of_gt
  apply add_pos
  apply log_pos
  have : (2:ℝ) ^ 2 / 2 = 2 := by linarith
  rw [this]
  suffices 0 < rexp 1 by linarith
  exact exp_pos 1
  apply div_pos
  refine rpow_pos_of_pos ?_ (3 / 10)
  simp
  simp

/-- The subtlety here is whether
to use t^2 or t^(2:ℝ). They are the same, but
not by definition.
-/
lemma chan_tse_exercise_1_6_b {a A I : ℝ → ℝ}
    (h1_6 : ∀ t, a t = log (t^2 / 2 + exp 1) + t^((3:ℝ) / 10) / 20)
    (hA : A 0 = 1200)
    (h1_1 : ∀ t, I t = A t - A (t - 1))
    (h1_1' : ∀ t, A t = A 0 * a t) :
    I 3 = 1200 * (log ((3:ℝ) ^ (2) / 2 + rexp 1) + (3:ℝ) ^ ((3:ℝ) / 10) / 20)
        - 1200 * (log ((2:ℝ) ^ (2) / 2 + rexp 1) + (2:ℝ) ^ ((3:ℝ) / 10) / 20) := by
  rw [h1_1, h1_1', show (3:ℝ)-1 = 2 by linarith]
  nth_rw 2 [h1_1']
  rw [hA, h1_6, h1_6]

/--
a 0 = 1
a 2 = (1 + i 1) (1 + i 2) = (1 + 1/100 + 1/200) ((1 + 1/100 + 2/200))  etc.
-/
lemma chan_tse_exercise_1_7 {a i : ℝ → ℝ} (c : ℝ)
    (h1_10₃ : ∀ t, a t = (1 + i t) * a (t - 1))
    (h1_1'' : a 0 = 1)
    (h : ∀ t, i t = (1 / 100) + (1 / 200) * t) :
    ∀ t, a t = c := by
  intro t
  sorry

/-

# Theory of nominal and effective interest and discount rates



-/

/-- Nominal interest rate
corresponding to effective rate `i` with compounding frequency `m`.

i ^ (m) is the nominal interest which when compounded `m` times corresponds
to the actual annual interest `i`
(1 + i ^ (2) / 2) ^ 2 = 1 + i


-/
noncomputable def Real.nomInt (i : ℝ) (m : ℝ) := m * ((1 + i) ^ ((1:ℝ) / m) - 1)

noncomputable def Real.effInt (im m : ℝ) := (1 + im / m) ^ m - 1

lemma compound_leftinv {i m : ℝ} (hm : m ≠ 0)
    (hi : 0 ≤ 1 + i) : (i.nomInt m).effInt m = i := by
  unfold nomInt effInt
  rw [← eq_sub_of_add_eq']
  generalize 1 + i = j at *
  suffices (1 + m * (j ^ (1 / m) - 1) / m) = j ^ (1 / m) by
    rw [this]
    simp
    rw [← rpow_mul]
    rw [inv_mul_cancel₀ hm]
    simp
    exact hi
  ring_nf
  field_simp

/-- Here we use `1 ≤ m` instead of `m ≠ 0`...
is it necessary?
-/
lemma compound_rightinv {i m : ℝ} (hml : 1 ≤ m)
    (hi : 0 ≤ 1 + i) : (i.effInt m).nomInt m = i := by
  unfold nomInt effInt
  suffices ((1 + ((1 + i / m) ^ m - 1)) ^ (1 / m) - 1) = i / m by
    rw [this]
    field_simp
  have h₀ : 0 ≤ 1 + i / m := by
    field_simp
    apply div_nonneg
    linarith
    linarith
  generalize i / m = j at *
  suffices (1 + ((1 + j) ^ m - 1)) ^ (1 / m) = 1 + j by
    rw [this]
    linarith

  generalize 1 +j  = k at *
  field_simp
  ring_nf
  rw [← rpow_mul h₀]
  have hm : m ≠ 0 := by linarith
  rw [mul_inv_cancel₀ hm]
  simp

lemma pow_pow {x y z : ℝ} (h : x ^ y < z ^ y)
    (hx : 1 < x)
    (hy : 0 < y)
    (hz : 1 < z)
    : x < z := by
  rw [rpow_def_of_pos (by linarith)] at h
  rw [rpow_def_of_pos (by linarith)] at h
  have h₀ : log x * y < log z * y := exp_lt_exp.mp h
  have : log x < log z := (mul_lt_mul_iff_of_pos_right hy).mp h₀
  refine (log_lt_log_iff ?_ ?_).mp this <;> linarith


/-- Conversion between nominal and effective interest rate
 is a bijection on `[0, ∞)`. -/
noncomputable def compound_interest {m : ℝ} (hm : 1 ≤ m) : PartialEquiv ℝ ℝ := {
  toFun := fun i => i.nomInt m
  invFun := fun i => i.effInt m
  source := {i | 0 ≤ i}
  target := {i | 0 ≤ i}
  map_source' := by
    intro i hi
    unfold nomInt
    simp at hi ⊢
    apply mul_nonneg
    linarith
    suffices 1 ≤ (1 + i) ^ m⁻¹ by linarith
    suffices 1 ^ m⁻¹ ≤ (1 + i) ^ m⁻¹ by simpa using this
    have : 1 ≤ 1 + i := by linarith
    have : 0 < m⁻¹ := by field_simp;linarith
    refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr (by tauto)
    simp
    linarith
    simp
    linarith
  map_target' := by
    intro i hi
    unfold effInt
    simp at hi ⊢
    suffices 1 ^ m ≤ (1 + i / m) ^ m by simpa using this
    have : 1 ≤ 1 + i := by linarith
    have : 0 < m⁻¹ := by field_simp;linarith
    refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr (by
      suffices 0 ≤ i / m by linarith
      apply div_nonneg
      tauto
      linarith)
    simp
    apply add_nonneg
    simp
    apply div_nonneg
    tauto
    linarith
    simp at this
    tauto
  left_inv' := fun i hi => compound_leftinv (by linarith) (by simp at hi;linarith)
  right_inv' := fun i hi => compound_rightinv hm (by simp at hi;linarith)
}


/-- i ^ (1) in actuarial notation, is just i.  -/
example (i : ℝ) : i.nomInt 1 = i := by simp [nomInt]

/-- The nominal interest rate with frequency of compounding `n`
is strictly less than the effective interest rate.
-/
theorem nomIntLt (i n : ℝ) (hn : 1 < n) (hi : 0 < i) :

    i.nomInt n < i := by

  have h₀ : ((1 + i) ^ n⁻¹) ^ n = (1 + i) ^ (n⁻¹ * n) := by
    rw [rpow_mul]
    apply add_nonneg
    simp
    linarith
  have h₂ : Invertible n := by
    refine invertibleOfNonzero ?_
    linarith
  have h₁ : n⁻¹ * n = 1 := inv_mul_cancel_of_invertible n
  simp [nomInt]
  suffices ((1 + i) ^ n⁻¹) < 1 + i / n by
    have : 0 < n := by linarith
    suffices ((1 + i) ^ n⁻¹ - 1) < i / n by
      generalize  (1 + i) ^ n⁻¹ - 1 = m at *
      exact (lt_div_iff₀' (by tauto)).mp this
    linarith
  suffices ((1 + i) ^ n⁻¹) ^ n < (1 + i / n) ^ n by
    apply pow_pow this
    have : (1:ℝ) = (1:ℝ) ^ n⁻¹ := by simp
    nth_rw 1 [this]
    exact (rpow_lt_rpow_iff (by simp) (by linarith) (by simp;linarith)).mpr <| by linarith
    linarith
    suffices 0 < i / n by linarith
    apply div_pos hi
    linarith
  rw [← rpow_mul]
  rw [h₁]
  simp
  have := @effInt_increasing n i 1 (by linarith) (by linarith)
    (by simp) hn
  simp at this
  exact this
  linarith


/-- This is probably covered by other results. -/
example (i x : ℝ) (n : ℝ) (hi : 0 ≤ i) (hn : n > 0)
  (h : 1 + x = (1 + i / n) ^ (n:ℝ)) :
  i = n * ((1 + x) ^ (1 / n) - 1) := by
  have : (1 + x) ^ ((1:ℝ) / n) = 1 + i / n := by
    have hu : 1 + i / n ≥ 0 := by
      apply add_nonneg
      simp
      apply div_nonneg
      exact hi
      linarith
    generalize 1 + i / n = u at *
    rw [h]
    have : (u ^ n) ^ (1 / n) = u ^ (n * (1 / n)) := by
      refine Eq.symm (rpow_mul ?_ n (1 / n))
      tauto
    rw [this]
    have : u = u ^ (1:ℝ) := by exact Eq.symm (rpow_one u)
    nth_rw 2 [this]
    congr
    field_simp
  generalize x ^ (1 / n) = v at *
  rw [this]
  field_simp
