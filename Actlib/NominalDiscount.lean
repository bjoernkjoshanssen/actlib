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

import Batteries.Data.Rat.Float
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.ODE.Gronwall


/-!
# Chan & Tse Exercise 1.1
-/

#eval 20000 * (1.08)^4

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
  have : x / (x + u) = 1 - (u / (x + u)) := by field_simp
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
  (hu : -1 < u) (hu₀ : u ≠ 0)
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
      have : 0 < 1 + u / t := by
        have : 1 ≤ t := by linarith
        field_simp
        linarith
      simp
      rw [mul_comm]
      refine Eq.symm (rpow_def_of_pos ?_ t)
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
    positivity
  rw [this]
  suffices  (1 + ε / m) ^ (1 / k) < (1 + ε / (k * m)) ^ 1 by
    refine (mul_lt_mul_left ?_).mpr this
    positivity
  have hr {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ (c) < b ^ (c)) : a < b := by
      clear this hm hn hk hε ε m n k
      exact (@rpow_lt_rpow_iff a b c (by linarith) (by linarith)
        (by tauto)).mp h
  suffices  ((1 + ε / m) ^ (1 / k)) ^ k < ((1 + ε / (k * m)) ^ 1) ^ k by
    apply hr
    · positivity
    · positivity
    · show 0 < k; linarith
    exact this
  have :  ((1 + ε / m) ^ (1 / k)) ^ k
    =  (1 + ε / m) ^ ((1 / k) * k) := by
      rw [rpow_mul]
      positivity
  rw [this]
  simp
  rw [inv_mul_cancel₀ (by linarith)]
  rw [div_mul_eq_div_div_swap]
  have hu : 0 < ε / m := by positivity
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

namespace force

/-! Here we develop interest theory, taking the force of interest δ as basic. -/

variable (δ : ℝ → ℝ)

noncomputable def a_sub (t τ : ℝ) := Real.exp (∫ (s : ℝ) in t..(t + τ), δ s)

noncomputable def a (t : ℝ) := a_sub δ 0 t

-- Principal
variable (A₀ : ℝ)

-- Amount function
noncomputable def A : ℝ → ℝ := fun t => a δ t * A₀

end force

theorem a_zero (δ : ℝ → ℝ) : force.a_sub δ 0 0 = 1 := by
  unfold force.a_sub
  simp

/-- In name space `interest`, a(0)=1 was not automatic but here it is: -/
theorem a_zero' (δ : ℝ → ℝ) : force.a δ 0 = 1 := by
  unfold force.a force.a_sub
  simp

namespace interest

/-!
Interest namespace will clash with annuity namespaces since they use `a` for different things.
-/

-- Principal
variable (A₀ : ℝ)

-- Accumulation function
variable (a : ℝ → ℝ)

-- Amount function
def A : ℝ → ℝ := fun t => a t * A₀ -- BAD BECAUSE IT MAKES a 0 = 1 NOT AUTOMATIC

lemma A_def (t : ℝ) : A A₀ a t = a t * A₀ := by rfl

-- Interest function. Probably best to define it directly in terms of a, A₀
def I : ℝ → ℝ := fun t => (a t - a (t - 1)) * A₀

/-- Effective interest over an interval, not annualized.
i₂ u v = (a v - a u) / (a u)
This should be used when u ≤ v.
See Chan & Tse (1.15).

One can prove that the limit of i₂ u (u + h) / h as h → 0 is a' u / a u:
(a (u+h) - a u) / (h * (a u))
-/
noncomputable def i₂ : ℝ → ℝ → ℝ := fun u v => a v / a u - 1

/-- Force of interest with not necessarily constant interest rates. -/
noncomputable def δ : ℝ → ℝ := fun u  => deriv a u / a u


/-- Annualized effective interest over an interval.
Equation (1.13) in Chan & Tse.
-/
noncomputable def i₂ann : ℝ → ℝ → ℝ := fun u v => (a v / a u) ^ (1 / (v - u)) - 1

-- Multiple forward rate
noncomputable def iF : ℝ → ℝ → ℝ := fun t τ => i₂ann a t (t + τ)

-- Assume c = 1 and b = 2
example (a b : ℝ) : 27 * a * 2
  < a ^ 3 + 2 ^ 3 + 1 + 6 * a * 2
  + 3 * a^2 * 2
  + 3 * a^2
  + 3 * 2^2 * a
  + 3 * 2^2
  + 3 * a
  + 3 * 2
  := by
  ring_nf
  suffices  (a - 1) * 27 < a ^ 2 * (9 + a) by linarith
  by_cases H : a = 4
  subst H
  linarith
  sorry


lemma i₂ann_def {u v : ℝ} (h : u < v) (hu : 0 < a u) (hv : 0 ≤ a v) :
    a v = a u * (1 + i₂ann a u v) ^ (v - u) := by
  field_simp [i₂ann]
  rw [← rpow_mul]
  · simp
    rw [inv_mul_cancel₀]
    · field_simp
    · linarith
  positivity

/-- The effective interest rate function `i(t)` is defined so that
`a t = (1 + i t) * a (t - 1)`.
-/
noncomputable def i : ℝ → ℝ := fun t => i₂ a (t-1) t

noncomputable def v : ℝ → ℝ := fun t => 1 / a t

/-- Exercise 1.21 in Chan and Tse.
i(1) fits with back-of-the-book solution.
(Unfortunately `v` and `i` are denoted `v a` and `i a` since they depend on `a`.)
-/
lemma chan_tse_exe_1_21 (h : ∀ t, v a t = 20 / (20 + t)) {t : ℝ} (ht : 0 ≠ 20 + t):
    i a (t+1) = 1 / (20 + t) := by
  simp [i, i₂]
  simp [v] at h
  have ha (t) : a t = (20 + t) / 20 := by
    have ht := h t
    rw [← inv_inv (a t)]
    rw [ht]
    field_simp
  rw [ha (t+1), ha t]
  field_simp

lemma chan_tse_exe_1_33 (h : ∀ t, a t = 1 / (1 - 0.01 * t)) :
    ∀ t, v a t = 1 - 0.01 * t := by
  intro t
  unfold v
  rw [h]
  field_simp

lemma chan_tse_exe_1_34 (h : ∀ t, A A₀ a t = t^2 + 2*t + 4) :
    δ a 5 = 4 / 13 := by
  unfold δ
  unfold A at h
  have hA₀ : A₀ ≠ 0 := by
    intro hc
    subst hc
    simp at h
    specialize h 0
    simp at h
  have h₅ : a 5 ≠ 0 := by
    specialize h 5
    intro hc
    rw [hc] at h
    simp at h
    linarith
  have : a = fun t => A₀⁻¹ * (t ^ 2 + 2 * t + 4) := by
    ext t
    field_simp
    rw [h]
  suffices deriv a 5 = a 5 * (4 / 13) by
    rw [this]
    generalize a 5 = α at *
    ring_nf
    rw [mul_comm]
    have : α * α⁻¹ = 1 := by
      field_simp
    rw [this]
    field_simp
  rw [this]
  rw [deriv_const_mul]
  simp
  rw [mul_assoc]
  congr
  conv =>
    left
    left
    change (fun y => y ^ 2) + fun y => 2 * y
  rw [deriv_add]
  simp
  rw [deriv_const_mul]
  simp
  linarith
  simp
  apply DifferentiableAt.pow
  simp
  apply DifferentiableAt.const_mul
  simp
  apply DifferentiableAt.add
  apply DifferentiableAt.add
  apply DifferentiableAt.pow
  simp
  apply DifferentiableAt.const_mul (by simp)
  simp

-- example (x y c d : ℝ) (h₀ : x^2+y-3=0) (h₁: x+(1/2)*y^2-3/2=0) : x = c ∧ y = d := by
--   sorry
-- f = (x^2+y-3, x+(1/2)y^2-3/2), g = (x^2-1,y^2-1)
-- h = γ (1-t) g(x,y) + t f(x,y), γ random in ℂ, t in [0,1]

lemma eq_of_deriv_eq (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g)
    (h : deriv f = deriv g) (h₀ : f 0 = g 0) : f = g := by
    exact @eq_of_fderiv_eq ℝ ℝ _ _ _ _ ℝ _ _ f g hf hg (by
        intro x
        rw [← deriv_fderiv]
        rw [← deriv_fderiv]
        simp
        rw [h]) 0 h₀


open scoped Real

theorem solutions_of_deriv_eq_self {f : ℝ → ℝ} (hf : Differentiable ℝ f)
  (h : ∀ x, deriv f x = f x) :
  ∃ c : ℝ, ∀ x, f x = c * Real.exp x := by
  let g := fun x => f x * Real.exp (-x)
  have : ∀ x, deriv g x = (deriv f x - f x) * Real.exp (-x) := by
    intro x
    calc
      deriv g x
        = deriv f x * Real.exp (-x) + f x * deriv (fun y => Real.exp (-y)) x := by
          exact (deriv_mul (hf x) (by
            refine DifferentiableAt.exp ?_
            refine Differentiable.differentiableAt ?_
            exact differentiable_neg))
      _ = (deriv f x - f x) * Real.exp (-x) := by
          conv =>
            left
            right
            right
            change deriv (rexp ∘ fun y ↦ (-y)) x
          rw [deriv_comp]
          rw [Real.deriv_exp]
          simp
          linarith
          exact differentiableAt_exp
          refine differentiableAt_of_deriv_ne_zero ?_
          rw [deriv_neg]
          simp
  have g_deriv_zero : ∀ x, deriv g x = 0 := fun x => by
    rw [this]
    rw [h]
    simp
  have : ∃ c, ∀ x, g x = c := by
    use g 0
    intro x
    apply is_const_of_deriv_eq_zero
    unfold g
    refine Differentiable.fun_mul hf ?_
    refine Differentiable.exp ?_
    exact differentiable_neg
    exact g_deriv_zero
  obtain ⟨c, hc⟩ := this
  use c
  intro x
  calc f x = g x * Real.exp x := by
        unfold g;rw [mul_assoc]
        rw [← exp_add]
        simp
    _   = c * Real.exp x := by rw [hc]


example (a δ : ℝ → ℝ) (ha : Differentiable ℝ a) (hδ : Continuous δ)
    (h : deriv a = a * δ) :
    ∃ c, a = fun t => c * rexp (∫ s in 0..t, δ s) := by
  have := @solutions_of_deriv_eq_self
  sorry
/-
algebraic statistics for s4cs:
binomial distribution
(p₀, p₁, p₂) = (P(X=0),...)
p₀^2 = 4p₀p₂
and p₀ + p₁ + p₂ = 1
implies that there exist parameters

-/


example : (1 : Float) + (2 : Float) ≤ (3 : Float) := by native_decide
example : (1 : Float) + (2 : Float) ≥ (3 : Float) := by native_decide
example : (1 : Float) + (2 : Float) == (3 : Float) := by
        native_decide -- doesn't work


lemma edist_mul {c : ℝ} (hδ : 0 ≤ c) (x y : ℝ) :
    edist (c * x) (c * y) = ENNReal.ofReal c * edist x y := by
  rw [edist_dist]
  rw [edist_dist]
  have : dist (c * x) (c * y) =
    (c) * dist x y := by
    have hδ : |c| = c := abs_eq_self.mpr hδ
    generalize c = α at *
    show |α * x - α * y| = α * |x - y|
    suffices |α * x + α * -y| = α * |x + -y| by
      convert this using 2
      ring_nf
    generalize -y = z
    have : α * x + α * z = α * (x + z) := by ring_nf
    rw [this]
    generalize x + z = w
    nth_rw 2 [← hδ]
    exact abs_mul α w
  rw [this]
  refine ENNReal.ofReal_mul hδ



/-- The equation `a(t) = e^(∫^t δ(s) ds)`. -/
lemma general_force (a : ℝ → ℝ)
    (hnz : ∀ (t : ℝ), a t ≠ 0) (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1)
    {n : ℝ} (hn : 0 ≤ n)
    (hcontδ: ContinuousOn (δ a) (Set.Ici 0))
    (hδ : ∀ t ≥ 0, 0 < δ a t ∧ δ a t ≤ 1) -- ideally should generalize to `δ a t ≤ K`.
    (hc₀ : ContinuousAt (δ a) 0)
    (hme: StronglyMeasurableAtFilter (δ a) (nhds 0) MeasureTheory.volume) -- should follow from hc₀?
    :
    Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Icc 0 n) := by
  have hcont : Continuous a := Differentiable.continuous hdiff
  have hcool (t) (ht: 0 ≤ t) :
    IntervalIntegrable (δ a) MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      simp [Set.uIcc] at hx ⊢
      have hm₀: min 0 t = 0 := by apply min_eq_left ht
      rw [hm₀]
      have hm₁: max 0 t = t := by apply max_eq_right ht
      rw [hm₁]
      have := hcontδ x (by
        simp
        cases hx.1 <;> linarith)
      have hs : Set.Icc 0 t ⊆ Set.Ici 0 := by
        unfold Set.Icc Set.Ici
        simp
        intros
        trivial
      clear hx hm₀ hm₁ ht hcont hδ hcontδ hn n ha₀ hdiff hnz
      generalize δ a = f at *
      clear a
      apply ContinuousWithinAt.mono this hs
  have hlip : ∀ t ∈ Set.Ico 0 n, LipschitzOnWith 1 ((fun t x ↦ x * δ a t) t) ((fun x ↦ Set.univ) t) := by
      simp
      intro t ht hnt
      have h₀ : 0 ≤ δ a t := le_of_lt (hδ t ht).1
      have h₁ : δ a t ≤ 1 := (hδ t ht).2
      intro x y
      simp
      nth_rw 1 [mul_comm]
      nth_rw 2 [mul_comm]
      rw [edist_mul h₀ _ _]
      calc _ ≤ 1 * edist x y := mul_le_mul_right' (by norm_cast at *) (edist x y)
           _ ≤ _ := by simp
  have hcontexp : ContinuousOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) (Set.Icc 0 n) := by
        conv =>
          left
          change rexp ∘ fun t ↦ (∫ (s : ℝ) in 0..t, δ a s)
        refine continuous_exp.comp_continuousOn ?_

        apply (intervalIntegral.continuousOn_primitive ((intervalIntegrable_iff_integrableOn_Icc_of_le hn).mp (hcool _ hn))).congr
        intro x hx
        simp [intervalIntegral] at hx ⊢
        have : Set.Ioc x 0 = ∅ := by ext;simp;intro;linarith
        rw [this]
        simp
  have hhas :  ∀ t ∈ Set.Ico 0 n,
      HasDerivWithinAt (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s))
      ((fun t x ↦ x * δ a t) t ((fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) t)) (Set.Ici t) t := by
          intro t ht
          simp at ht
          have hii : IntervalIntegrable (δ a) MeasureTheory.volume 0 t := by
            apply hcool _ ht.1
          have hδat : δ a t ≠ 0 := by
            specialize hδ t ht.1
            linarith
          have hc : ContinuousAt (δ a) t := by
            by_cases H : t = 0
            · subst t
              exact hc₀
            specialize hcontδ t (by simp;exact ht.1)
            have : t ∈ Set.Ici 0 := ht.1
            generalize δ a = f at *
            have h₀ : Set.Ici (0:ℝ) ∈ nhds t := by
              refine Ici_mem_nhds ?_
              have := ht.1
              by_contra H₀
              apply H
              linarith
            generalize Set.Ici (0:ℝ) = A at *
            unfold ContinuousWithinAt at hcontδ
            unfold ContinuousAt
            convert hcontδ
            ext s
            constructor
            · intro h
              revert h
              exact fun h ↦ mem_nhdsWithin_of_mem_nhds h
            · exact fun a ↦ nhds_of_nhdsWithin_of_nhds h₀ a
          have hs : StronglyMeasurableAtFilter (δ a) (nhds t) MeasureTheory.volume := by
            by_cases H₀ : t = 0
            · subst t
              exact hme
            apply ContinuousOn.stronglyMeasurableAtFilter (s := Set.Ioi 0)
            · exact isOpen_Ioi
            · apply ContinuousOn.mono hcontδ
              intro;simp;intro;linarith
            simp
            by_contra H
            apply H₀
            linarith
          generalize δ a = f at *
          have : (fun t ↦ rexp (∫ (s : ℝ) in 0..t, f s))
            = rexp ∘ (fun t ↦ (∫ (s : ℝ) in 0..t, f s)) := by ext;simp
          rw [this]
          refine HasDerivAt.hasDerivWithinAt ?_
          simp
          apply @HasDerivAt.comp (h₂ := rexp)
            (h := fun t ↦ ∫ (s : ℝ) in 0..t, f s) (h' := f t)
            (h₂' := rexp (∫ (s : ℝ) in 0..t, f s))
            (x := t) _
          generalize (∫ (s : ℝ) in 0..t, f s) = q
          exact Real.hasDerivAt_exp q
          have := @intervalIntegral.deriv_integral_right (f := f)
            (a := 0) _ _ _ _ t hii hs hc
          rw [← this]
          refine DifferentiableAt.hasDerivAt ?_
          refine differentiableAt_of_deriv_ne_zero ?_ -- not so good as δ=0 should be allowed
          rw [intervalIntegral.deriv_integral_right hii hs hc]
          exact hδat

  exact @ODE_solution_unique_of_mem_Icc_right ℝ _ _ (λ t x ↦ x * δ a t) -- fix
    (f := fun t => rexp (∫ s in 0..t, δ a s)) (g := a)
    (fun _ => Set.univ)
    1 0 n
    hlip hcontexp hhas (by simp) (Continuous.continuousOn hcont)
      (by
        simp
        intro t ht htn
        unfold δ
        rw [mul_comm]
        have h₀ : deriv a t / a t * a t = deriv a t := div_mul_cancel₀ _ (hnz t)
        rw [h₀]
        refine HasDerivAt.hasDerivWithinAt ?_
        exact DifferentiableAt.hasDerivAt (hdiff t)) (by simp) (by simp;rw [ha₀])


lemma this_is_proved_instead₀ (a : ℝ → ℝ) (h : δ a = fun t ↦ 1 / (10 * (1 + t) ^ 3))
  (hnz : ∀ (t : ℝ), a t ≠ 0) (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1)
  (n : ℝ) (hn : 0 ≤ n) :
  Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Icc 0 n) := by
  apply general_force _ hnz hdiff ha₀ hn
    (by
      rw [h]
      simp
      refine (((continuous_add_left 1).continuousOn.pow 3).inv₀ ?_).div_const 10
      · intro x hx hcontra
        simp at hcontra hx
        have : x = -1 := by linarith
        subst this
        simp at hx
        linarith) (by
      intro t ht
      constructor
      · rw [h]
        positivity
      · rw [h]
        have h₁₀ : 0 < 10 * (1 + t)^3 := by positivity
        apply (div_le_one₀ h₁₀).mpr
        have : 1 ≤ (1 + t) ^ 3 := one_le_pow₀ (by linarith)
        linarith) (by
      rw [h]
      simp
      apply ContinuousAt.mul
      refine ContinuousAt.inv₀ ?_ ?_
      refine ContinuousAt.pow ?_ 3
      refine Continuous.continuousAt ?_
      exact continuous_add_left 1
      simp
      exact continuousAt_const) (by
            rw [h]
            refine (MeasureTheory.StronglyMeasurable.const_mul ?_ 1).stronglyMeasurableAtFilter
            exact (measurable_inv_iff.mpr <| measurable_const.mul <| (measurable_const_add 1).pow_const 3).stronglyMeasurable

      )



lemma this_is_proved_instead (a : ℝ → ℝ) (h : δ a = fun t ↦ 1 / (10 * (1 + t) ^ 3))
  (hnz : ∀ (t : ℝ), a t ≠ 0) (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1) :
  Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Ici 0) := by
  intro x hx
  simp at hx
  have := this_is_proved_instead₀ a h hnz hdiff ha₀ x hx
  apply this
  simp
  exact hx

lemma chan_tse_exe_1_36 (h : δ a = fun t => 1 / (10 * (1 + t) ^ 3))
    (h₀ : A₀ = 100) (hcont : Continuous a) (hnz : ∀ t, a t ≠ 0)
    (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1)
    :
    I A₀ a 5 = (Real.exp (7 / 144) -  Real.exp (6 / 125)) * 100
            ∧ (Float.exp (7 / 144) - Float.exp (6 / 125)) * 100 < 65e-3
            ∧ (Float.exp (7 / 144) - Float.exp (6 / 125)) * 100 > 64e-3 := by
  have h₁_₂₆ : ∀ t ≥ 0, a t = rexp (∫ s in 0..t, δ a s) :=
    fun _ ht => (this_is_proved_instead a h hnz hdiff ha₀ ht).symm
  unfold I
  rw [h₁_₂₆]
  rw [h₁_₂₆]
  simp_rw [h]
  rw [h₀]
  rw [show (5:ℝ)-1=4 by linarith]
  have : ∫ (s : ℝ) in 0..5, 1 / (10 * (1 + s) ^ 3) = (1 / 20) * (1 - 1 / 36) := by
    sorry
  rw [this]
  have : ∫ (s : ℝ) in 0..4, 1 / (10 * (1 + s) ^ 3) = (1 / 20) * (1 - 1 / 25) := by
    sorry
  rw [this]
  have : ((1:ℝ) / 20) * (1 - 1 / 36) = 7 / 144 := by
    linarith
  rw [this]
  have : ((1:ℝ) / 20) * (1 - 1 / 25) = 6 / 125 := by
    linarith
  rw [this]
  constructor
  · rfl
  · constructor
    · native_decide
    · native_decide
  · simp
  · simp

-- #eval (Float.exp ((7 / 144) - Float.exp (6 / 125)) * 100).toRat0
-- #eval (Float.exp ((7 / 144) - Float.exp (6 / 125)) * 100).toString
-- #eval (Float.exp ((7 / 144) - Float.exp (6 / 125)) * 100).repr 10
-- #eval (Float.exp 600).toRat0
-- 2251799813685248 = 2^51 (used with e^1)
--  562949953421312 = 2^49 (used with e^2)
--  140737488355328 = 2^47 (used with e^3 and Exercise 1.36)
--   35184372088832 = 2^45 (used with e^5)
--   17592186044416 = 2^44 (used with e^4 and e^6)
--    2199023255552 = 2^40 (used with e^7)
--    1099511627776 = 2^39 (used with e^8)
--     549755813888 = 2^38 (used with e^9)
--         33554432 = 2^25 (used with e^(19))
--             1024 = 2^10 (used with e^(29))
-- Lean thinks e^35 is not an integer but e^36 is :)
-- e^700 is a huge integer too big for a tweet, e^800 == 0
-- e^600 huge integer

-- #eval Float.exp ((7 / 144) - Float.exp (6 / 125)) * 100 == 36.767365

-- example : False := by
--     -- have h₀ : (0 / 0 : Float) == 0 / 0 := rfl
--     have h₀ : (0 / 0 : Float) = 0 / 0 := rfl
--     have h₁ : (0 / 0 : Float) != 0 / 0 := by native_decide
--     have h₁ : (0 / 0 : Float) != (0 / 0 : Float) := by native_decide
--     have h₁ : ¬ (0 / 0 : Float) == 0 / 0 := by native_decide
--     have (x : Float) : x == x := by sorry
--     sorry
-- Where 140737488355328 = 2^47

/-- The effective discount rate function `d(t)` is defined so that
`a (t - 1) = (1 - d t) * a t`.
-/
noncomputable def d : ℝ → ℝ := fun t => 1 - a (t - 1) / a t
end interest

/-- If the principal is zero then so is the amount function. -/
lemma principal_zero (a : ℝ → ℝ) : interest.A 0 a = fun _ => 0 := by
  unfold interest.A
  simp

lemma effective_interest_rate_def (a : ℝ → ℝ) (t : ℝ)
    (h : a (t - 1) ≠ 0) :
    a t = (1 + interest.i a t) * a (t - 1) := by
  field_simp [interest.i₂,interest.i]

lemma effective_discount_rate_def (a : ℝ → ℝ) (t : ℝ)
    (h : a t ≠ 0) :
    a (t - 1) = (1 - interest.d a t) * a t := by
  field_simp [interest.d]

/-- This lemma can replace `h1_10₁` in `chan_tse_1_3`. -/
lemma h1_10₁ {a : ℝ → ℝ}
  {t : ℝ} (h : a (t - 1) ≠ 0) (A₀: ℝ) : interest.I A₀ a t = interest.A A₀ a (t - 1) * interest.i a t := by
  unfold interest.I interest.A interest.i interest.i₂
  field_simp
  ring_nf



-- not needed
-- lemma h1_10₂ {a : ℝ → ℝ} (A₀ t : ℝ) :
--   interest.I A₀ a t = interest.A A₀ a t - interest.A A₀ a (t - 1) := by
--   unfold interest.I interest.A
--   ring_nf

/--
This is a more theoretical version of `chan_tse_1_3`.
-/
lemma chan_tse_1_3NEW {a : ℝ → ℝ} (A₀ : ℝ)
  (h1_3₁ : interest.A A₀ a 4 = 1200)
  (h1_3₂ : ∀ t, interest.i a t = t ^ 2 / 100) :
  interest.I A₀ a 5 = 300 ∧ interest.A A₀ a 6 = 2040 := by
  have h₅ : (5:ℝ) - 1 = 4 := by linarith
  have h₆ : (6:ℝ) - 1 = 5 := by linarith
  have ha : a (5 - 1) ≠ 0 := by
      rw [show (5:ℝ)-1=4 by linarith]
      unfold interest.A at h1_3₁
      intro hc
      rw [hc] at h1_3₁
      simp at h1_3₁
  have h₀ : interest.I A₀ a 5 = 300 := by
    rw [h1_10₁ ha, h₅, h1_3₁, h1_3₂]
    linarith
  have h₁ : interest.A A₀ a 5 = 1500 := by
    unfold interest.I at h₀
    unfold interest.A at h1_3₁ ⊢
    rw [h₅] at h₀
    linarith
  constructor
  · exact h₀
  · have h₅ : interest.I A₀ a 6 = interest.A A₀ a 6 - interest.A A₀ a 5 := by
      unfold interest.I at h₀ ⊢
      unfold interest.A at h1_3₁ ⊢ h₁
      rw [h₅] at h₀
      rw [h₆]
      linarith
    rw [h1_10₁, h1_3₂, h₆, h₁] at h₅
    linarith
    rw [h₆]
    intro hc
    rw [interest.A_def, hc] at h₁
    simp at h₁


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
  · apply log_pos
    have : (2:ℝ) ^ 2 / 2 = 2 := by linarith
    rw [this]
    suffices 0 < rexp 1 by linarith
    exact exp_pos 1
  positivity

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

/-
a 0 = 1
a 2 = (1 + i 1) (1 + i 2) = (1 + 1/100 + 1/200) ((1 + 1/100 + 2/200))  etc.
-/
-- lemma chan_tse_exercise_1_7 {a i : ℝ → ℝ} (c : ℝ)
--     (h1_10₃ : ∀ t, a t = (1 + i t) * a (t - 1))
--     (h1_1'' : a 0 = 1)
--     (h : ∀ t, i t = (1 / 100) + (1 / 200) * t) :
--     ∀ t, a t = c := by
--   intro t
--   sorry

/-

# Theory of nominal and effective interest and discount rates

i ^ (m) is the nominal interest which when compounded `m` times corresponds
to the actual annual interest `i`
(1 + i ^ (2) / 2) ^ 2 = 1 + i


-/

/-- Nominal interest rate
corresponding to effective rate `i` with compounding frequency `m`.  -/
noncomputable def Real.nomInt (i : ℝ) (m : ℝ) := m * ((1 + i) ^ ((1:ℝ) / m) - 1)

/-- The force of interest corresponding to
effective interest rate `i` is the nominal interest with
`m = ∞` times a year compounding frequency.
-/
noncomputable def Real.force (i : ℝ) := log (1 + i)



lemma antitone_of_deriv_neg {f : ℝ → ℝ} (hc :  ContinuousOn f (Set.Ici 1))
    (h₀ : ∀ x > 1, deriv f x < 0) : StrictAntiOn f (Set.Ici 1) := by
        apply strictAntiOn_of_deriv_neg
        exact convex_Ici 1
        exact hc
        simp
        tauto

lemma antitone_of_deriv_neg' (f : ℝ → ℝ) (z  : ℝ) (hc :  ContinuousOn f (Set.Ici 1))
    (h₀ : ∀ x > 1, deriv f x < 0) (a : ℝ) (ha : 1 ≤ z ∧ z < a) :
    f a < f z := by
    apply @antitone_of_deriv_neg f hc h₀ z (ha.1) a
    · exact le_trans ha.1 <| le_of_lt ha.2
    · exact ha.2

-- #eval Float.log 2
/-- Rule of 69.3: if a = fun t => (1+i)^t
then
a t = 2 * a 0
when
t = Real.log 2 / interest.δ a
and also
Float.log 2 = 0.693
-/

lemma force_lt_average_interest_discount_aux : ∀ x > 1, deriv (fun α => 2 * log α + 1 / α - α) x < 0 := by
    intro x hx
    conv => left; left; change (fun α ↦ 2 * log α) + (fun α ↦ 1 / α) - (fun α ↦ α)
    rw [deriv_sub]
    · simp
      rw [deriv_add]
      · rw [deriv_const_mul]
        · rw [deriv_inv, deriv_log]
          simp
          ring_nf
          suffices 0 < (x⁻¹ - 1) ^ 2 by linarith
          suffices x⁻¹ - 1 ≠ 0 by positivity
          field_simp
          linarith
        · refine differentiableAt_log ?_
          linarith
      · refine DifferentiableAt.fun_comp' x ?_ ?_
        · apply DifferentiableAt.const_mul (by simp)
        · refine differentiableAt_log (by linarith)
      refine differentiableAt_inv ?_
      linarith
    · refine DifferentiableAt.add ?_ ?_

      apply DifferentiableAt.const_mul
      refine differentiableAt_log (by linarith)
      refine differentiableAt_of_deriv_ne_zero ?_
      simp
      linarith
    · simp

/--
This result could be strengthened:
assuming `0 < i`,
actually `d < Real.force i` holds, but
that seems to require a proof like `anti'` above.
If `i=0` then `d=0` and `Real.force i = 0` too.
-/
theorem discount_le_force {i d : ℝ} (hi : 0 < 1 + i)
    (h : (1 - d) * (1 + i) = 1) :
    d ≤ Real.force i := by
  unfold force
  have h : 0 < 1 + i := by linarith
  have : d = 1 - 1 / (1 + i) := by
    field_simp
    linarith
  rw [this]
  have g₀ := @Real.one_sub_inv_le_log_of_pos (1 + i) h
  simp at g₀ ⊢
  exact g₀

/--
For concave down accumulation functions `a`,
the discount rate is not bounded by the force of interest.
We prove it here for `a t = ln (1 + t)` with `t = 1`.
-/
theorem not_discount_le_force :
    let a := fun t => log (1 + t)
    ¬ ∀ t ≥ 0, interest.d a t ≤ interest.δ a t := by
    intro a
    push_neg
    use 1
    constructor
    · simp
    simp [interest.d, interest.δ, a]
    conv => left; left; left; change log ∘ fun t => 1 + t
    rw [deriv_comp]
    simp
    conv => left; left; right; left; change (fun _ => 1) + fun t => t
    simp
    have : (1:ℝ)+1 = 2 := by linarith
    rw [this]
    have : 0 < log 2 := by positivity
    suffices  (2⁻¹ / log 2) * log 2 < 1 * log 2 by
      apply (mul_lt_mul_iff_of_pos_right (by tauto)).mp this
    suffices 2⁻¹ < log 2 by
        simp
        have :  2⁻¹ / log 2 * log 2 = 2⁻¹ := by field_simp;ring_nf
        rw [this]
        tauto
    field_simp
    suffices (1 / 2) * 2 < log 2 * 2 by
        have := @mul_lt_mul_iff_of_pos_right ℝ _ _ _
            2 (1 / 2) (log 2) _ _ (by simp)
        tauto
    suffices 1 < 2 * log 2 by
        ring_nf;linarith
    have h₀ : (0:ℝ) < 2 := by linarith
    suffices 1 < log (2 ^ (2:ℝ)) by
        convert this using 1
        refine (mul_log_eq_log_iff h₀ ?_).mpr ?_
        simp
        rfl
    have : (2:ℝ) ^ (2:ℝ) = 4 := by linarith
    rw [this]
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    simp
    linarith [Real.exp_one_lt_d9]
    simp
    apply DifferentiableAt.add (by simp) (by simp)

/-- For simple interest, the force is still above the discount.
However, we need to restrict the time interval to [0,∞].
From a classroom discussion on September 12, 2025.
-/
theorem simple_discount_le_force (r : ℝ) (hr : 0 ≤ r) :
    let a := fun t => 1 + r * t
    ∀ t ≥ 0, interest.d a t ≤ interest.δ a t := by
    intro a x hx
    simp [interest.d, interest.δ, a]
    rw [deriv_const_mul]
    field_simp
    suffices  1 * (1 + r * x) ≤ ((r + (1 + r * (x - 1))) / (1 + r * x)) * (1 + r * x) by
        exact le_of_mul_le_mul_right this <| by positivity
    field_simp
    linarith
    simp

theorem force_lt_average_interest_discount {i d : ℝ} (hi : 0 < i)
  (h : (1 - d) * (1 + i) = 1) :
  Real.force i < (i + d) / 2 := by
  have h : 0 < 1 + i := by linarith
  have h₀ : 1 < 1 + i := by linarith
  unfold force
  have : d = 1 - 1 / (1 + i) := by
    field_simp
    linarith
  rw [this]
  rw [add_sub_assoc']
  have g₁ := @Real.log_le_sub_one_of_pos (1 + i) h
  nth_rw 2 [add_comm]
  generalize 1 + i = α at *
  have g₃ :  (fun α ↦ 2 * log α + 1 / α - α) α < (fun α ↦ 2 * log α + 1 / α - α) 1 := by
    have g₄ := @antitone_of_deriv_neg' (fun α => 2 * log α + 1 / α - α)
        (h₀ := force_lt_average_interest_discount_aux) 1 (a := α)
        (by
            refine ContinuousOn.add ?_ ?_
            · refine ContinuousOn.add ?_ ?_
              · refine Continuous.comp_continuousOn' ?_ ?_
                exact continuous_mul_left 2
                refine continuousOn_of_forall_continuousAt ?_
                simp
                intros
                linarith
              · show ContinuousOn (fun x => 1 / x) _
                apply ContinuousOn.div
                exact continuousOn_const
                intro x hx
                refine ContinuousWithinAt.star ?_
                apply Continuous.continuousWithinAt
                exact continuous_id'
                intro x hx
                simp at hx
                linarith
            exact continuousOn_neg
        ) (⟨by linarith,by linarith⟩)
    tauto
  simp at g₃
  suffices 2 * log α + 1 / α - α < 0 by linarith
  simp
  exact g₃

/-- Verify that interest.δ are Real.force cohere:
if the accumulation function is t ↦ (1+i)^t then δ = force i
 -/
example {t i : ℝ} (hi : 0 < 1 + i) :
  interest.δ (fun t => (1 + i)^t) t = i.force := by
  unfold interest.δ force
  simp
  have h₀ : (1 + i)^t ≠ 0 := ne_of_gt <| by positivity
  rw [← eq_div_of_mul_eq h₀]
  simp_rw [rpow_def_of_pos hi]
  have : (fun t ↦ rexp (log (1 + i) * t)) = rexp ∘ fun t ↦ (log (1 + i) * t) := by
      ext t
      simp only [Function.comp_apply]
  rw [this]
  rw [deriv_comp]
  · rw [Real.deriv_exp]
    rw [deriv_const_mul]
    · simp
      nth_rw 1 [mul_comm]
    · simp
  · apply DifferentiableAt.exp (by simp)
  · exact DifferentiableAt.mul
      (DifferentiableAt.log (by simp) (by linarith)) (by simp)

noncomputable def Real.effIntTop (i : ℝ) := rexp i - 1

lemma force_effIntTop (i : ℝ) (hi : 0 < 1 + i) : i.force.effIntTop = i := by
  unfold force effIntTop
  rw [exp_log hi]
  simp

lemma effIntTop_force (i : ℝ) : i.effIntTop.force = i := by
  simp [force, effIntTop]

example : Function.RightInverse Real.effIntTop Real.force := by
  intro x
  simp [force, effIntTop]


lemma l₁ (i : ℝ) : i ≤ i.effIntTop := by
  unfold effIntTop
  suffices i + 1 ≤ rexp i by linarith
  exact add_one_le_exp i




/-- As a limiting form of nominal interest rate,
the force of interest is less than the effective interest rate.
  -/
example (i : ℝ) (hi : 0 < 1 + i) : i.force ≤ i := by
  unfold force
  refine (log_le_iff_le_exp ?_).mpr ?_
  exact hi
  rw [add_comm]
  exact add_one_le_exp i



noncomputable def Real.effInt (im m : ℝ) := (1 + im / m) ^ m - 1

-- example (i : ℝ) (h : 0 < 1 + i) : i.force ≤ i.nomInt 2 := by
--   suffices (i.force).effInt 2 ≤ (i.nomInt 2).effInt 2 by
--     have := @effInt_increasing

--     sorry
--   have : (i.nomInt 2).effInt 2 = i := sorry
--   rw [this]
--   unfold force effInt
--   suffices (1 + log (1 + i) / 2) ^ (2:ℝ) ≤ 1 + i by
--     linarith
--   generalize 1 + i = j
--   sorry

-- example (i : ℝ) (h : 0 < 1 + i) : i.force ≤ i.nomInt 2 := by
--   suffices (i.force).effIntTop ≤ (i.nomInt 2).effIntTop by
--     have := @effInt_increasing

--     sorry
--   have : (i.nomInt 2).effInt 2 = i := sorry
--   rw [force_effIntTop _ h]
--   unfold effIntTop nomInt
--   sorry

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
    apply div_nonneg <;> linarith
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

open Real

lemma pow_pow {x y z : ℝ} (h : x ^ y < z ^ y)
    (hy : 0 < y) (hz : 1 < z) : x < z := by
  -- Proof by DeepSeek
  by_contra! H  -- H : z ≤ x
  have : z ^ y ≤ x ^ y := Real.rpow_le_rpow (by linarith) H hy.le
  linarith


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
    · linarith
    · suffices 1 ≤ (1 + i) ^ m⁻¹ by linarith
      suffices 1 ^ m⁻¹ ≤ (1 + i) ^ m⁻¹ by simpa using this
      have : 1 ≤ 1 + i := by linarith
      have : 0 < m⁻¹ := by field_simp;linarith
      refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr (by tauto)
      simp
      linarith
      positivity
  map_target' := by
    intro i hi
    unfold effInt
    simp at hi ⊢
    suffices 1 ^ m ≤ (1 + i / m) ^ m by simpa using this
    have : 1 ≤ 1 + i := by linarith
    have : 0 < m⁻¹ := by positivity
    refine (rpow_le_rpow_iff ?_ ?_ ?_).mpr (by
      suffices 0 ≤ i / m by linarith
      positivity)
    all_goals positivity
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
    positivity
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
    linarith
    suffices 0 < i / n by linarith
    positivity
  rw [← rpow_mul]
  rw [h₁]
  simp
  have := @effInt_increasing n i 1 (by linarith) (by linarith)
    (by simp) hn
  simp at this
  exact this
  linarith


/-!

# Nominal discount rate
corresponding to effective rate `d` with compounding frequency `m`.  -/

noncomputable def Real.nomDis (d : ℝ) (m : ℝ) := m * (1 - (1 - d) ^ ((1:ℝ) / m))

/--  1 - d = (1 - d_m/m)^m  -/
noncomputable def Real.effDis (d : ℝ) (m : ℝ) := 1 - (1 - d / m) ^ m

/--
Broverman's Exercise 1.5.10 (b) holds as long as the interest is ≥ 0.
It is a generalization of the equation
i (1-d) = d
(1+i) (1-d) = 1
and together with part (a) actually just says
`(1 - d^(m)/m) (1 + i^(m)/m) = 1`
-/
theorem broverman_exercise_1_5_10_b {m i d : ℝ} (hid : (1+i) * (1-d)=1)
    (hm₀ : 1 ≤ m) (hi : 0 ≤ i) :
    i.nomInt m = d.nomDis m / (1 - d.nomDis m / m) := by

  rcases Or.symm (Decidable.lt_or_eq_of_le hi) with (hi | hi)
  · symm at hi
    subst hi
    simp at hid
    subst hid
    simp [nomInt, nomDis]
  have hi : 0 ≤ 1 + i := by linarith
  have hd₁ : 0 < d := by
    by_contra H
    simp at H
    have : 1 ≤ 1 - d := by linarith
    have : (1:ℝ) < 1 := calc
        _ < (1 + i) * 1 := by linarith
        _ ≤ (1 + i) * (1 - d) := by
            exact mul_le_mul_of_nonneg_left this hi
        _ = 1 := hid
    simp at this
  have hd : 0 < 1 - d := by
    by_contra H
    have : 0 = 1 - d ∨ 0 > 1 - d := eq_or_lt_of_not_gt H
    cases this with
    | inl h => rw [← h] at hid;simp at hid
    | inr h =>
        cases Or.symm (Decidable.lt_or_eq_of_le hi) with
        | inl h =>
            rw [← h] at hid;simp at hid
        | inr h₀ =>
            have : (1 + i) * (1 - d) < 0 := mul_neg_of_pos_of_neg h₀ h
            rw [hid] at this
            linarith
  have hm : (1 - d.nomDis m / m) ≠ 0 := by
    unfold nomDis
    field_simp
    linarith

  have h₀ : d.nomDis m / (1 - d.nomDis m / m) * (1 - d.nomDis m / m)
    = d.nomDis m := by
    generalize (1 - d.nomDis m / m) = x at *
    field_simp

  suffices i.nomInt m * (1 - d.nomDis m / m) =
    (d.nomDis m / (1 - d.nomDis m / m)) * (1 - d.nomDis m / m) by
        rw [h₀] at this
        generalize (1 - d.nomDis m / m) = x at *
        field_simp
        exact this
  field_simp
  have : m - d.nomDis m ≠ 0 := by
    unfold nomDis
    intro hc
    have : m * ((1 - d) ^ (1 / m)) = 0 := by linarith
    have : ((1 - d) ^ (1 / m)) = 0 := by
        have hm₀ : m ≠ 0 := by linarith
        exact (mul_eq_zero_iff_left hm₀).mp this
    ring_nf at this
    have hr := @rpow_eq_zero (x := 1 - d) (y := m⁻¹) (by linarith) (by simp;linarith)
    rw [hr] at this
    linarith
  have : d.nomDis m * m * (m - d.nomDis m) * m / ((m - d.nomDis m) * m)
       = d.nomDis m * m := by field_simp;ring_nf
  rw [this]
  simp [nomInt,nomDis]
  ring_nf
  rw [mul_assoc, ← mul_rpow, hid]
  simp
  linarith
  linarith



/-- This shows that our definition of
`nomDis` is good. -/
lemma nomDis_good {d m : ℝ} (hd : 0 ≤ 1 - d) (hm : m ≠ 0):
    (1 - (d.nomDis m) / m) ^ (m:ℝ) = 1 - d := by
  simp [Real.nomDis]
  have h₀ := (@rpow_left_inj (z := 1 / m) (x := ((1 - m * (1 - (1 - d) ^ m⁻¹) / m) ^ m))
    (y := 1 - d) (by
      apply rpow_nonneg
      field_simp
      apply rpow_nonneg hd) hd (by field_simp)).mp
  apply h₀
  rw [← rpow_mul]
  field_simp
  ring_nf
  field_simp
  apply rpow_nonneg hd

lemma compound_LeftDis {d m : ℝ} (hd : 0 ≤ 1 - d) (hm : m ≠ 0) :

    (d.nomDis m).effDis m = d := by

  have := nomDis_good hd hm
  unfold effDis at *
  linarith

lemma compound_RightDis {d m : ℝ} (hd : d ≤ m) (hm₁ : 1 ≤ m) : (d.effDis m).nomDis m = d := by
  have hm : m ≠ 0 := by linarith
  unfold nomDis effDis at *
  field_simp
  ring_nf
  rw [CommGroupWithZero.mul_inv_cancel m hm]
  rw [← rpow_mul]
  rw [CommGroupWithZero.mul_inv_cancel m hm]
  field_simp
  suffices d * m⁻¹ ≤ 1 by linarith
  apply mul_inv_le_one_of_le₀ <;> linarith


lemma desmosInspired {m : ℝ} (hm : 0 < m)
  (d : ℝ) (h : d ≤ m) :
  d.effDis m ≤ 1 := by
  unfold effDis
  suffices 0 ≤  (1 - d / m) ^ m by linarith
  apply rpow_nonneg
  suffices d / m ≤ 1 by linarith
  suffices d / m ≤ m / m by field_simp at this;tauto
  refine (div_le_div_iff_of_pos_right ?_).mpr h
  linarith

lemma desmosInspired₂ {m : ℝ} (hm : 1 ≤ m)
  (d : ℝ) (h : d ≤ 1) :
  d.nomDis m ≤ m := by
  unfold nomDis
  suffices 0 ≤ (1 - d) ^ (1 / m) by field_simp;tauto
  apply rpow_nonneg
  suffices d / m ≤ 1 by linarith
  suffices d / m ≤ m / m by convert this;field_simp
  have : d ≤ m := by linarith
  refine (div_le_div_iff_of_pos_right ?_).mpr this
  linarith


/-- Conversion between nominal and effective interest rate. -/
noncomputable def compound_discount {m : ℝ} (hm : 1 ≤ m) : PartialEquiv ℝ ℝ := {
  toFun := fun d => d.nomDis m
  invFun := fun d => d.effDis m
  source := Set.Ioo 0 1
  target := Set.Ioo 0 m
  map_source' := by
    intro d hd
    constructor
    · unfold nomDis
      simp at hd ⊢
      apply mul_pos
      · positivity
      · suffices (1 - d) ^ m⁻¹ < 1 ^ m⁻¹ by
          simp at this; linarith
        apply rpow_lt_rpow
        linarith
        linarith
        positivity
    · unfold nomDis
      simp at hd ⊢
      field_simp
      apply rpow_pos_of_pos
      linarith
  map_target' := by
    intro d hd
    unfold effDis
    simp at hd ⊢
    constructor
    · suffices (1 - d / m) ^ m < 1 ^ m by
        simp at this
        exact this
      apply rpow_lt_rpow
      suffices d / m ≤ 1 by linarith

      suffices d ≤ m by
        field_simp
        suffices d / m ≤ m / m by field_simp at this;exact this
        refine (div_le_div_iff_of_pos_right ?_).mpr this
        linarith
      linarith
      suffices 0 < d / m by linarith
      apply div_pos
      · tauto
      · linarith
      linarith
    · apply rpow_pos_of_pos
      field_simp
      tauto
  left_inv' := fun d hd => by
    have := @compound_LeftDis
    apply this
    simp at hd
    linarith
    linarith
  right_inv' := fun d hd => by
    simp at hd
    exact @compound_RightDis d m (by linarith) hm
}

example : (1:ℝ).nomDis 2 = 2 := by
  unfold nomDis
  simp

example : ((2:ℝ) / 3).nomDis 2 = 2 * (1 - 1 / √ 3) := by
  unfold nomDis
  simp
  field_simp
  have : ((3:ℝ) - 2) / 3 = 1 / 3:= by field_simp;linarith
  rw [this]
  have : ((1:ℝ) / 3) ^ ((1:ℝ) / 2) = √(1 / 3) := by
    exact Eq.symm (sqrt_eq_rpow (1 / 3))
  rw [this]
  simp


/-- Aug 25: Nominal discount is greater than
effective discount. -/
theorem nomDis_gt {d m : ℝ} (hm : 1 < m) (hd₀ : 0 < d)
    (hd₁ : 0 < 1 - d) :

    d.nomDis m > d := by

  by_cases H : d.nomDis m ≥ 1
  linarith
  have h₁ := @nomDis_good d m (by linarith) (by linarith)
  have h₀ := @effInt_increasing (w := 1) (u := - d.nomDis m) (k := m)
    (by linarith) (by
      simp [Real.nomDis]
      constructor
      linarith
      intro hc
      have : 1 = (1 - d) ^ m⁻¹ := by linarith
      have : 1 ^ m⁻¹ = (1 - d) ^ m⁻¹ := by
        rw [← this]
        simp
      have : 1 = 1 - d :=  (@rpow_left_inj 1 (1-d) m⁻¹ (by simp)
          (by linarith) (by simp;linarith)).mp this
      linarith) (by simp) hm
  simp at h₀
  suffices 1 - d.nomDis m < 1 - d by linarith
  rw [← h₁]
  suffices 1  < (1 - d.nomDis m / m) ^ m + d.nomDis m by
    linarith
  convert h₀ using 1
  congr
  generalize d.nomDis m = D
  ring_nf



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




-- noncomputable def compound_discount_neg {m : ℝ} (hm : 1 ≤ m) : PartialEquiv ℝ ℝ := {
--   toFun := fun d => d.nomDis m
--   invFun := fun d => d.effDis m
--   source := Set.Iic 0
--   target := Set.Iic 0
--   map_source' := by
--     intro x hx
--     simp [nomDis] at hx ⊢
--     sorry
--   map_target' := by
--     intro x hx
--     simp [effDis] at hx ⊢
--     sorry
--   left_inv' := by
--     intro x hx
--     simp [effDis, nomDis] at hx ⊢
--     suffices  1 - x = (1 - m * (1 - (1 - x) ^ m⁻¹) / m) ^ m
--       by linarith
--     suffices  (1 - x) ^ m⁻¹ = (1 - m * (1 - (1 - x) ^ m⁻¹) / m)
--       by field_simp;sorry
--     have : m * (1 - (1 - x) ^ m⁻¹) / m =
--       (1 - (1 - x) ^ m⁻¹) := by sorry
--     rw [this]
--     simp
--   right_inv' := by
--     intro x hx
--     simp [nomDis, effDis] at hx ⊢
--     sorry
-- }


-- noncomputable def compound_discount'' {m : ℝ} (hm : 1 ≤ m) : PartialEquiv ℝ ℝ := {
--   toFun := fun d => d.nomDis m
--   invFun := fun d => d.effDis m
--   source := Set.Iio m
--   target := Set.Iio 1
--   map_source' := by
--     intro x hx
--     have : x ∈ Set.Iic 0 ∨ x ∈ Set.Ioo 0 m := by
--       simp at hx ⊢
--       by_cases H : x ≤ 0
--       tauto
--       simp at H
--       tauto
--     cases this with
--     | inl h =>
--       have := (compound_discount_neg hm).map_source'
--       unfold compound_discount_neg at this
--       -- have := (compound_discount hm).map_source'
--       -- unfold compound_discount at this
--       simp at this ⊢
--       simp at hx h
--       sorry
--     | inr h =>
--       have := (compound_discount_neg hm).map_source'
--       unfold compound_discount_neg at this
--       simp at this
--       have := (compound_discount hm).map_source'
--       unfold compound_discount at this
--       simp at this hx h ⊢
--       sorry
--   map_target' := by sorry
--   left_inv' := by sorry
--   right_inv' := by sorry
-- }
