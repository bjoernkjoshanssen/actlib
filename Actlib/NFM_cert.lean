import LeanCert.Validity.Bounds.Bridge
import LeanCert.Validity.DyadicBounds
import Mathlib.Analysis.ODE.ExistUnique
import LeanCert

/-!
# Chan & Tse Exercise 1.1
-/

-- #eval 20000 * (1.08)^4

-- #eval (20000
--   * ((1 + ((0.08) / 2)) ^ 2)
--   * ((1 + ((0.08) / 4)) ^ 4)
--   * ((1 + ((0.08) / 6)) ^ 6)
--   * ((1 + ((0.08) / 12)) ^ 12)
--   )

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

/-- The effective interest rate function `i(t)` is defined so that
`a t = (1 + i t) * a (t - 1)`.
-/
noncomputable def i : ℝ → ℝ := fun t => i₂ a (t-1) t

noncomputable def v : ℝ → ℝ := fun t => 1 / a t


lemma chan_tse_exe_1_33 (h : ∀ t, a t = 1 / (1 - 0.01 * t)) :
    ∀ t, v a t = 1 - 0.01 * t := by
  intro t
  unfold v
  rw [h]
  field_simp


-- example (x y c d : ℝ) (h₀ : x^2+y-3=0) (h₁: x+(1/2)*y^2-3/2=0) : x = c ∧ y = d := by
--   sorry
-- f = (x^2+y-3, x+(1/2)y^2-3/2), g = (x^2-1,y^2-1)
-- h = γ (1-t) g(x,y) + t f(x,y), γ random in ℂ, t in [0,1]

lemma eq_of_deriv_eq (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g)
    (h : deriv f = deriv g) (h₀ : f 0 = g 0) : f = g := by
    exact @eq_of_fderiv_eq ℝ ℝ _ _ _ _ ℝ _ _ f g hf hg (by
        intro x
        rw [← toSpanSingleton_deriv]
        rw [← toSpanSingleton_deriv]
        simp only [ContinuousLinearMap.toSpanSingleton_inj]
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
          · rw [Real.deriv_exp]
            simp
            linarith
          · exact differentiableAt_exp
          · refine differentiableAt_of_deriv_ne_zero ?_
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
    · refine Differentiable.fun_mul hf ?_
      refine Differentiable.exp ?_
      exact differentiable_neg
    · exact g_deriv_zero
  obtain ⟨c, hc⟩ := this
  use c
  intro x
  calc f x = g x * Real.exp x := by
        unfold g;rw [mul_assoc]
        rw [← exp_add]
        simp
    _   = c * Real.exp x := by rw [hc]


/-
algebraic statistics for s4cs:
binomial distribution
(p₀, p₁, p₂) = (P(X=0),...)
p₀^2 = 4p₀p₂
and p₀ + p₁ + p₂ = 1
implies that there exist parameters

-/


-- example : (1 : Float) + (2 : Float) ≤ (3 : Float) := by native_decide
-- example : (1 : Float) + (2 : Float) ≥ (3 : Float) := by native_decide
-- example : (1 : Float) + (2 : Float) == (3 : Float) := by
--         native_decide -- doesn't work


lemma edist_mul {c : ℝ} (hδ : 0 ≤ c) (x y : ℝ) :
    edist (c * x) (c * y) = ENNReal.ofReal c * edist x y := by
  rw [edist_dist]
  rw [edist_dist]
  have : dist (c * x) (c * y) =
    (c) * dist x y := by
    have hδ : |c| = c := abs_eq_self.mpr hδ
    generalize c = α at *
    change |α * x - α * y| = α * |x - y|
    suffices |α * x + α * -y| = α * |x + -y| by
      convert this using 2
      · ring_nf
      · congr
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
    (hcontδ : ContinuousOn (δ a) (Set.Ici 0))
    (hδ : ∀ t ≥ 0, 0 < δ a t ∧ δ a t ≤ 1) -- ideally should generalize to `δ a t ≤ K`.
    (hc₀ : ContinuousAt (δ a) 0)
    (hme : StronglyMeasurableAtFilter (δ a) (nhds 0) MeasureTheory.volume) : -- follows from hc₀?
    Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Icc 0 n) := by
  have hcont : Continuous a := Differentiable.continuous hdiff
  have hcool (t) (ht: 0 ≤ t) :
    IntervalIntegrable (δ a) MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      intro x hx
      simp only [Set.uIcc, Set.mem_Icc, inf_le_iff, le_sup_iff] at hx ⊢
      have hm₀: min 0 t = 0 := by apply min_eq_left ht
      rw [hm₀]
      have hm₁: max 0 t = t := by apply max_eq_right ht
      rw [hm₁]
      have := hcontδ x (by
        simp
        cases hx.1 <;> linarith)
      have hs : Set.Icc 0 t ⊆ Set.Ici 0 := by
        unfold Set.Icc Set.Ici
        simp only [Set.setOf_subset_setOf, and_imp]
        intros
        trivial
      clear hx hm₀ hm₁ ht hcont hδ hcontδ hn n ha₀ hdiff hnz
      generalize δ a = f at *
      clear a
      apply ContinuousWithinAt.mono this hs
  have hlip : ∀ t ∈ Set.Ico 0 n,
    LipschitzOnWith 1 ((fun t x ↦ x * δ a t) t) ((fun x ↦ Set.univ) t) := by
      simp only [Set.mem_Ico, lipschitzOnWith_univ, and_imp]
      intro t ht hnt
      have h₀ : 0 ≤ δ a t := le_of_lt (hδ t ht).1
      have h₁ : δ a t ≤ 1 := (hδ t ht).2
      intro x y
      simp only [ENNReal.coe_one, one_mul]
      nth_rw 1 [mul_comm]
      nth_rw 2 [mul_comm]
      rw [edist_mul h₀ _ _]
      calc _ ≤ 1 * edist x y := mul_le_mul_left (by norm_cast at *) (edist x y)
           _ ≤ _ := by simp
  have hcontexp : ContinuousOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) (Set.Icc 0 n) := by
        conv =>
          left
          change rexp ∘ fun t ↦ (∫ (s : ℝ) in 0..t, δ a s)
        refine continuous_exp.comp_continuousOn ?_
        apply (intervalIntegral.continuousOn_primitive
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hn).mp (hcool _ hn))).congr
        intro x hx
        simp only [Set.mem_Icc, intervalIntegral, sub_eq_self] at hx ⊢
        have : Set.Ioc x 0 = ∅ := by
            ext;simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_and, not_le]
            intro;linarith
        rw [this]
        simp
  have hhas :  ∀ t ∈ Set.Ico 0 n,
      HasDerivWithinAt (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s))
      ((fun t x ↦ x * δ a t) t ((fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) t)) (Set.Ici t) t := by
          intro t ht
          simp only [Set.mem_Ico] at ht
          have hii : IntervalIntegrable (δ a) MeasureTheory.volume 0 t := by
            apply hcool _ ht.1
          have hδat : δ a t ≠ 0 := by
            specialize hδ t ht.1
            linarith
          have hc : ContinuousAt (δ a) t := by
            by_cases H : t = 0
            · subst t
              exact hc₀
            specialize hcontδ t ht.1
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
              intro
              simp only [Set.mem_Ioi, Set.mem_Ici]
              intro
              linarith
            simp only [Set.mem_Ioi]
            by_contra H
            apply H₀
            linarith
          generalize δ a = f at *
          have : (fun t ↦ rexp (∫ (s : ℝ) in 0..t, f s))
            = rexp ∘ (fun t ↦ (∫ (s : ℝ) in 0..t, f s)) := by ext;simp
          rw [this]
          refine HasDerivAt.hasDerivWithinAt ?_
          apply @HasDerivAt.comp (h₂ := rexp)
            (h := fun t ↦ ∫ (s : ℝ) in 0..t, f s) (h' := f t)
            (h₂' := rexp (∫ (s : ℝ) in 0..t, f s))
            (x := t) _
          · exact Real.hasDerivAt_exp _
          have := @intervalIntegral.deriv_integral_right (f := f)
            (a := 0) _ _ _ _ t hii hs hc
          rw [← this]
          refine DifferentiableAt.hasDerivAt ?_
          refine differentiableAt_of_deriv_ne_zero ?_ -- not so good as δ=0 should be allowed
          rw [intervalIntegral.deriv_integral_right hii hs hc]
          exact hδat
  exact @ODE_solution_unique_of_mem_Icc_right ℝ _ _ (fun t x ↦ x * δ a t) -- fix
    (f := fun t => rexp (∫ s in 0..t, δ a s)) (g := a)
    (fun _ => Set.univ) 1 0 n
    hlip hcontexp hhas (by simp) (Continuous.continuousOn hcont) (by
        simp only [Set.mem_Ico, and_imp]
        intro t ht htn
        unfold δ
        rw [mul_comm]
        have h₀ : deriv a t / a t * a t = deriv a t := div_mul_cancel₀ _ (hnz t)
        rw [h₀]
        refine HasDerivAt.hasDerivWithinAt ?_
        exact DifferentiableAt.hasDerivAt (hdiff t)) (by simp) (by
            simp only [intervalIntegral.integral_same, exp_zero]
            rw [ha₀])


lemma this_is_proved_instead₀ (a : ℝ → ℝ) (h : δ a = fun t ↦ 1 / (10 * (1 + t) ^ 3))
  (hnz : ∀ (t : ℝ), a t ≠ 0) (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1)
  (n : ℝ) (hn : 0 ≤ n) :
  Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Icc 0 n) := by
  apply general_force _ hnz hdiff ha₀ hn
    (by
      rw [h]
      simp only [one_div, mul_inv_rev]
      refine (((continuous_const_add 1).continuousOn.pow 3).inv₀ ?_).div_const 10
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
      simp only [one_div, mul_inv_rev]
      apply ContinuousAt.mul
      · refine ContinuousAt.inv₀ ?_ ?_
        · exact (continuous_const_add 1).continuousAt.pow 3
        · simp
      · exact continuousAt_const) (by
            rw [h]
            refine (MeasureTheory.StronglyMeasurable.const_mul ?_ 1).stronglyMeasurableAtFilter
            exact (measurable_inv_iff.mpr <| measurable_const.mul
                <| (measurable_const_add 1).pow_const 3).stronglyMeasurable)



lemma this_is_proved_instead (a : ℝ → ℝ) (h : δ a = fun t ↦ 1 / (10 * (1 + t) ^ 3))
  (hnz : ∀ (t : ℝ), a t ≠ 0) (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1) :
  Set.EqOn (fun t ↦ rexp (∫ (s : ℝ) in 0..t, δ a s)) a (Set.Ici 0) := by
  intro x hx
  have := this_is_proved_instead₀ a h hnz hdiff ha₀ x hx
  apply this
  simp only [Set.mem_Icc, Std.le_refl, and_true]
  exact hx

/-
The integral of 1 / (10 * (1 + s) ^ 3) from 0 to 5 is 1 / 20 * (1 - 1 / 36).
(Aristotle)
-/
theorem integral_one_div_ten_one_add_pow_three_0_to_5 : ∫ (s : ℝ) in (0)..5, 1 / (10 * (1 + s) ^ 3)
    = 1 / 20 * (1 - 1 / 36) := by
  have h_integral : ∫ s in (0 : ℝ)..5, (1 / (10 * (1 + s) ^ 3)) = (1 / 20) * (1 - 1 / 36) := by
    have : ∫ s in (0 : ℝ)..5, (1 / (10 * (1 + s) ^ 3))
      = (1 / 10) * ∫ s in (0 : ℝ)..5, (1 + s) ^ (-3 : ℝ) := by
      norm_cast ; norm_num [ mul_comm ]
    rw [ this, intervalIntegral.integral_comp_add_left
        fun x => x ^ ( -3 : ℝ ), integral_rpow ] <;> norm_num
  exact h_integral

/-
The integral of 1 / (10 * (1 + s) ^ 3) from 0 to 4 is 1 / 20 * (1 - 1 / 25).
(Aristotle)
-/
theorem integral_one_div_ten_one_add_pow_three_0_to_4 :
    ∫ (s : ℝ) in (0)..4, 1 / (10 * (1 + s) ^ 3) = 1 / 20 * (1 - 1 / 25) := by
  rw [ intervalIntegral.integral_comp_add_left fun x => 1 / ( 10 * x ^ 3 ) ] ; norm_num;
  group ; erw [ integral_zpow ] <;> norm_num

lemma chan_tse_exe_1_36 (h : δ a = fun t => 1 / (10 * (1 + t) ^ 3))
    (h₀ : A₀ = 100) (hnz : ∀ t, a t ≠ 0)
    (hdiff : Differentiable ℝ a) (ha₀ : a 0 = 1) : I A₀ a 5 ∈ Set.Ioo 64e-3 65e-3 := by
  have :     I A₀ a 5 = (Real.exp (7 / 144) -  Real.exp (6 / 125)) * 100
            ∧ (Real.exp (7 / 144) - Real.exp (6 / 125)) * 100 < 65e-3
            ∧ (Real.exp (7 / 144) - Real.exp (6 / 125)) * 100 > 64e-3 := by
    have h₁_₂₆ : ∀ t ≥ 0, a t = rexp (∫ s in 0..t, δ a s) :=
      fun _ ht => (this_is_proved_instead a h hnz hdiff ha₀ ht).symm
    unfold I
    rw [h₁_₂₆]
    · rw [h₁_₂₆]
      · simp_rw [h]
        rw [h₀, show (5:ℝ)-1=4 by linarith]
        rw [integral_one_div_ten_one_add_pow_three_0_to_4,
            integral_one_div_ten_one_add_pow_three_0_to_5]
        have : ((1:ℝ) / 20) * (1 - 1 / 36) = 7 / 144 := by linarith
        rw [this]
        have : ((1:ℝ) / 20) * (1 - 1 / 25) = 6 / 125 := by linarith
        rw [this]
        constructor
        · rfl
        · constructor
          · interval_decide
          · have : ∀ x ∈ Set.Icc (7/144) (71/1440),
              (Real.exp x - Real.exp (6 / 125)) * 100 > 64e-3 := by interval_bound
            apply this
            simp
            linarith
      · simp
    · simp
  rw [this.1]
  tauto
end interest
