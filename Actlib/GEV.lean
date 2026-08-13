import Mathlib

open Set Filter
open scoped Topology


/-!
# Generalized extreme value distribution

The main result is that the definition of the PDF (see Wikipedia)
should use open intervals, rather than closed,
as that gives a simpler expression using `if-then-else` conditions
and makes `deriv CDF = PDF` with no side conditions besides `σ > 0`.
.
See `GEVPDF_eq_genExtremePDF` and `genExtremePDF_eq_GevPDF`.

The simplest expression we obtain has two versions:
1. (genExtremePDF, see genExtremePDF_simplify)
   `((1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)) *`
   `ite ((x - μ) * ξ + σ > 0) 1 0`

2. (GevPDF) `  {x | t x > 0}.indicator`
  `fun x => (1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)`

Among these (1) shows the linearity of the constraint whereas (2)
shows the simple dependence on `t` *and should be the official definition*.

The CDF: ...

-/
noncomputable section
namespace GEV
open Real

/-- Auxiliary function used to define the PDF of the generalized
extreme value distribution.
`t x` is interpreted as the normalized number of observations beyond the threshold `x`
in a limiting, Poisson sense. That's why the CDF is e^(-t x).
"t X ~ Exp(1)" t = exponentialRV_of_GEV?
-/
def t (ξ μ σ x : ℝ) := ite (ξ = 0)
    (exp (- (x - μ)/ σ)) ((1 + ξ * ((x - μ)/σ)) ^ (-1 / ξ))

open Finset

lemma hundred_percent_nonsquares : Tendsto (fun n : ℕ =>
  (# ({k | ∀ a : Fin n, k.1 ≠ a.1 ^ 2} : Finset (Fin n)) : ℝ) / n)
  atTop (nhds 1) := by
  sorry

def genExtremeCDF (ξ μ σ x : ℝ) :=
  let t := t ξ μ σ
  let p := exp (-t x)
  ite (ξ = 0) p (
    ite (ξ < 0) (ite (x < μ - σ/ξ) p 1) (
      (ite (x > μ - σ/ξ) p 0)
    )
  )


theorem tendsto_rpow_atTop_of_pos {f : ℝ → ℝ} (hf : Tendsto f atTop atTop)
  {α : ℝ} (hα : α < 0) : Tendsto (fun x ↦ f x ^ α) atTop (𝓝 0) := by
            have hf' : ∃ a, ∀ x > a, 0 < f x := by
              rw [tendsto_atTop] at hf
              specialize hf 1
              simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq] at hf
              choose a ha using hf
              use a
              intro b hb
              specialize ha b (by linarith)
              linarith
            suffices Tendsto (fun x ↦ 1 / f x ^ (-α)) atTop (𝓝 0) by
              rw [tendsto_congr']
              · exact this
              obtain ⟨a,ha⟩ := hf'
              simp only [EventuallyEq, one_div, eventually_atTop]
              use a + 1
              intro x hx
              ring_nf
              rw [rpow_neg]
              · exact Eq.symm (DivisionMonoid.inv_inv (f x ^ α))
              specialize ha x (by linarith)
              linarith
            have hβ : 0 < -α := by linarith
            simp only [one_div]
            exact tendsto_inv_atTop_zero.comp
              ((tendsto_rpow_atTop hβ).comp hf)

theorem GEV_CDF_behavior.extracted_1_1 (μ σ : ℝ) (hσ : 0 < σ) :
  Tendsto (fun x ↦ -rexp ((μ - x) / σ)) atTop (𝓝 (-0)) := by
      refine (Topology.IsInducing.tendsto_nhds_iff ?_).mp ?_
      · refine Topology.isInducing_iff_nhds.mpr ?_
        simp_rw [Filter.comap_neg, ← nhds_neg]
        simp
      refine tendsto_exp_comp_nhds_zero.mpr ?_
      have :  Tendsto (fun x ↦ (μ - x)) atTop atBot := by
        refine tendsto_atTop_atBot_of_antitone antitone_const_tsub ?_
        intro b; use μ - b;simp
      suffices Tendsto (fun x ↦ σ⁻¹ * (μ - x)) _ _ by
        convert this using 1
        ext x
        field_simp
      rw [tendsto_const_mul_atBot_iff]
      simp
      tauto

theorem tendsto_rpow_atBot_of_pos {f : ℝ → ℝ} (hf : Tendsto f atBot atTop)
  {α : ℝ} (hα : α < 0) : Tendsto (fun x ↦ f x ^ α) atBot (𝓝 0) := by
  have h₀ := @tendsto_rpow_atTop_of_pos (fun x => f (-x))
    (Tendsto.comp hf <| tendsto_neg_atTop_atBot) α hα
  have : Tendsto ((fun x ↦ f (x) ^ α) ∘ Neg.neg) atTop (𝓝 0) := by
    exact h₀
  suffices Tendsto (((fun x ↦ f x ^ α) ∘ Neg.neg) ∘ Neg.neg) atBot (𝓝 0) by
    convert this using 1
    ext x
    simp
  apply Tendsto.comp this tendsto_neg_atBot_atTop

theorem tendsto_rpow_atBot_of_pos' {f : ℝ → ℝ} (hf : Tendsto f atBot atTop)
  {α : ℝ} (hα : α > 0) : Tendsto (fun x ↦ f x ^ α) atBot atTop :=
  Tendsto.comp (tendsto_rpow_atTop hα) hf

/-- A filter version of "negative times negative infinity is infinity":
if `g` tends to a negative limit `ξ` and `f` tends to `atBot` along a filter `𝓕`,
then the pointwise product `g * f` tends to `atTop`. -/
lemma tendsto_mul_atBot_of_neg (ξ : ℝ)
  (𝓕 : Filter ℝ)
  (H₀ : ξ < 0) (f : ℝ → ℝ) (this : Tendsto f 𝓕 atBot) (g : ℝ → ℝ)
  (h₀ : Tendsto g 𝓕 (𝓝 ξ)) : Tendsto (g * f) 𝓕 atTop := by
  simpa [Pi.mul_def] using h₀.neg_mul_atBot H₀ this


lemma comap_neg_atBot_eq_atTop : (@Filter.comap ℝ ℝ Neg.neg Filter.atBot : Filter ℝ) =
    Filter.atTop := by
  ext s
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [Filter.mem_atBot_sets] at ht
    obtain ⟨b, hb⟩ := ht
    rw [Filter.mem_atTop_sets]
    exact ⟨-b, fun x hx => hts (hb _ (by linarith))⟩
  · intro hs
    rw [Filter.mem_atTop_sets] at hs
    obtain ⟨a, ha⟩ := hs
    refine ⟨Set.Iic (-a), Filter.Iic_mem_atBot _, fun x hx => ha _ ?_⟩
    simp only [Set.mem_preimage, Set.mem_Iic] at hx
    linarith

/-- August 9, 2026.
As a CDF should, GEV CDF has the property P(X=-∞)=0.
-/
lemma GEV_CDF_behavior₀ (ξ μ σ : ℝ) (hσ : 0 < σ) :
    Tendsto (genExtremeCDF ξ μ σ) atBot (nhds 0) := by
  unfold genExtremeCDF t
  by_cases H : ξ = 0
  · subst ξ
    simp only [↓reduceIte, neg_sub]
    change Tendsto (rexp ∘ _) _ _
    have : Tendsto (fun x ↦ -rexp ((μ - x) / σ)) atBot atBot := by
      change Tendsto (Neg.neg ∘ fun x ↦ rexp ((μ - x) / σ)) atBot atBot
      apply Tendsto.comp
      · exact tendsto_iff_comap.mpr fun ⦃U⦄ a ↦ a
      rw [comap_neg_atBot_eq_atTop]
      change Tendsto (rexp ∘ fun x ↦ ((μ - x) / σ)) atBot atTop
      apply Tendsto.comp
      · exact tendsto_iff_comap.mpr fun ⦃U⦄ a ↦ a
      simp only [comap_exp_atTop]
      rw [tendsto_div_const_atTop_iff]
      simp_all only [true_and]
      left
      refine tendsto_atBot_atTop_of_antitone antitone_const_tsub ?_
      intro b; use μ - b; simp
    generalize (fun x ↦ -rexp ((μ - x) / σ)) = f at *
    have : Tendsto rexp atBot (nhds 0) := by exact tendsto_exp_atBot
    apply Tendsto.comp this
    tauto
  · simp_rw [if_neg H]
    by_cases H₀ : ξ < 0
    · simp_rw [if_pos H₀]
      have : Tendsto (fun x ↦ rexp (-(1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ))) atBot (𝓝 0) := by
        simp only [tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff]
        apply tendsto_rpow_atBot_of_pos'
        · suffices Tendsto (fun x ↦ ξ * ((x - μ) / σ)) atBot atTop by
            exact tendsto_atTop_add_const_left atBot 1 this
          suffices Tendsto (fun x ↦ ((x - μ) / σ)) atBot atBot by
            change Tendsto ((fun x ↦ ξ) * fun x => ((x - μ) / σ)) atBot atTop
            generalize (fun x => ((x - μ) / σ)) = f at *
            have h₀ : Tendsto (fun x : ℝ => ξ) atBot (nhds ξ) := by
              simp
            apply tendsto_mul_atBot_of_neg _ _ H₀ _ this _ h₀
          rw [tendsto_div_const_atBot_iff]
          left
          simp_all only [true_and]
          exact tendsto_atBot_add_const_right atBot (-μ) fun ⦃U⦄ a ↦ a
        field_simp
        simp
        tauto
      rw [tendsto_congr']
      · exact this
      simp only [EventuallyEq]
      simp only [Filter.Eventually, ite_eq_left_iff, not_lt, tsub_le_iff_right, mem_atBot_sets,
        mem_setOf_eq]
      use μ - σ / ξ - 1
      intros
      linarith
    · simp_rw [if_neg H₀]
      have : Tendsto (fun x : ℝ ↦
         0) (atBot : Filter ℝ) (𝓝 (0 : ℝ)) := by
        simp
      rw [tendsto_congr']
      · exact this
      simp only [EventuallyEq, gt_iff_lt]
      simp only [Filter.Eventually, ite_eq_right_iff, exp_ne_zero, imp_false, not_lt,
        mem_atBot_sets, mem_setOf_eq]
      use μ - σ / ξ - 1 -- add 1 to make it absurd
      intros
      linarith

/-- August 9, 2026.
As a CDF should, GEV CDF has the property P(X<∞)=1.
-/
lemma GEV_CDF_behavior (ξ μ σ : ℝ) (hσ : 0 < σ) :
  Tendsto (genExtremeCDF ξ μ σ) atTop (nhds 1) := by
  unfold genExtremeCDF t
  by_cases H : ξ = 0
  · subst ξ
    simp only [↓reduceIte, neg_sub]
    rw [← exp_zero]
    rw [← neg_zero]
    change Tendsto (rexp ∘ _) _ _
    refine (Topology.IsOpenEmbedding.tendsto_nhds_iff ?_).mp
      <| GEV_CDF_behavior.extracted_1_1 μ σ hσ
    exact isOpenEmbedding_exp
  · simp_rw [if_neg H]
    by_cases H₀ : ξ < 0
    · simp_rw [if_pos H₀]
      have : Tendsto (fun x ↦ 1) (atTop : Filter ℝ) (𝓝 (1:ℝ)) := by simp
      rw [tendsto_congr']
      · exact this
      simp only [EventuallyEq, ite_eq_right_iff, exp_eq_one_iff, neg_eq_zero, eventually_atTop]
      use μ - σ / ξ
      intros
      linarith
    · simp_rw [if_neg H₀]
      have : Tendsto (fun x ↦
         rexp (-(1 + ξ * ((x - μ) / σ)) ^ (-1 / ξ))) atTop (𝓝 1) := by
        nth_rw 3 [← exp_zero]
        apply Tendsto.rexp
        rw [← neg_zero]
        apply Tendsto.neg
        apply tendsto_rpow_atTop_of_pos (hα := by
          --simp
          field_simp
          simp only [not_lt, one_div, Left.neg_neg_iff, inv_pos] at H₀ ⊢
          contrapose! H
          exact le_antisymm H H₀)
        refine Tendsto.zero_eventuallyLE_add_atTop ?_ ?_
        · simp [EventuallyLE]
        rw [tendsto_const_mul_atTop_iff]
        left
        constructor
        · simp only [not_lt] at H₀
          exact lt_of_le_of_ne H₀ fun a ↦ H ((a.symm))
        rw [tendsto_div_const_atTop_iff]
        left
        constructor
        · exact hσ
        exact tendsto_atTop_add_const_right atTop (-μ) fun ⦃U⦄ a ↦ a
      rw [tendsto_congr']
      · exact this
      simp only [EventuallyEq, gt_iff_lt, ite_eq_left_iff, not_lt, eventually_atTop]
      use μ - σ / ξ + 1 -- add 1 to make it absurd
      intros
      linarith


/-- The PDF of the generalized extreme value distribution,
as in Wikipedia.
ξ < 0 : Weibull; ξ = 0 : Gumbel; ξ > 0 : Frechét. -/
def GEVPDF (ξ μ σ x : ℝ) : ℝ :=
  let t := t ξ μ σ
  ((1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)) *
   ite (ξ < 0) (ite (x ≤ μ - σ/ξ) 1 0)
  (ite (ξ = 0) 1 (ite (x ≥ μ - σ/ξ) 1 0))

/- The PDF of the generalized extreme value distribution.
A variant using open support. -/
def genExtremePDF (ξ μ σ x : ℝ) : ℝ :=
  let t := t ξ μ σ
  ((1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)) *
   ite (ξ < 0) (ite (x < μ - σ/ξ) 1 0)
  (ite (ξ = 0) 1 (ite (x > μ - σ/ξ) 1 0))

theorem GEV_xi_neg {ξ μ σ x : ℝ} (hσ : 0 < σ)
    (g₀ : ξ < 0) (g₂ : x < μ - σ / ξ) :
  1 + ξ * ((x - μ) / σ) ≠ 0 := by
        field_simp
        suffices (σ + ξ * (x - μ)) ≠ 0 by
          contrapose! this
          rw [div_eq_zero_iff] at this
          cases this with
          | inl h => tauto
          | inr h => linarith
        have := ne_of_lt g₂
        have h₀ : ξ ≠ 0 := by linarith
        have :  x * ξ ≠ (μ - σ / ξ) * ξ := by
          contrapose! this
          apply mul_right_cancel₀ h₀ this
        contrapose! this
        rw [sub_mul]
        rw [div_mul]
        have : ξ / ξ = 1 := (div_eq_one_iff_eq h₀).mpr rfl
        rw [this]
        linarith

theorem GEV_xi_pos {ξ μ σ x : ℝ} (hσ : 0 < σ)
    (g₀ : ξ > 0) (g₂ : x > μ - σ / ξ) :
  1 + ξ * ((x - μ) / σ) ≠ 0 := by
        field_simp
        suffices (σ + ξ * (x - μ)) ≠ 0 by
          contrapose! this
          rw [div_eq_zero_iff] at this
          cases this with
          | inl h => tauto
          | inr h => linarith
        have := ne_of_lt g₂
        have h₀ : ξ ≠ 0 := by linarith
        have :  x * ξ ≠ (μ - σ / ξ) * ξ := by
          contrapose! this
          symm
          apply mul_right_cancel₀ h₀ this
        contrapose! this
        rw [sub_mul]
        rw [div_mul]
        have : ξ / ξ = 1 := (div_eq_one_iff_eq h₀).mpr rfl
        rw [this]
        linarith

lemma GEV_alternatives {ξ μ σ x : ℝ} (h : 0 < ξ * (x - μ + σ / ξ)) :
   (ξ > 0 ∧ x > μ - σ / ξ) ∨
   (ξ < 0 ∧ x < μ - σ / ξ) := by
   rw [mul_pos_iff] at h
   cases h with
   | inl h => left;simp_all;linarith
   | inr h => right;simp_all;linarith

lemma GEV_xi_either {ξ μ σ x : ℝ} (hσ : 0 < σ)
    (h : ξ * (x - μ + σ / ξ) > 0) :
  1 + ξ * ((x - μ) / σ) ≠ 0 := by
  cases GEV_alternatives h with
  | inl h => apply GEV_xi_pos <;> tauto
  | inr h => apply GEV_xi_neg <;> tauto

/-- August 10, 2026. -/
theorem GEV_deriv_xi_nonzero {ξ μ σ x : ℝ}
  (hσ : 0 < σ)
  (h : ξ * (x - μ + σ / ξ) > 0) :
  deriv (fun x ↦ rexp (-t ξ μ σ x)) x =
  σ⁻¹ * t ξ μ σ x ^ (ξ + 1) * rexp (-t ξ μ σ x) := by
    have hσ : σ * σ⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel _ (by linarith)
    have hξ : ξ * ξ⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel ξ (by contrapose! h;subst ξ;linarith)
    change deriv (rexp ∘ fun x ↦ (-t ξ μ σ x)) x = _
    rcases GEV_alternatives h with (h' | h')
    all_goals
      have g₀ := h'.1
      have g₂ := h'.2
      have H :  1 + ξ * ((x - μ) / σ) ≠ 0 := by
        apply GEV_xi_either
        all_goals try tauto
      rw [deriv_comp, Real.deriv_exp, mul_comm]
      congr
      unfold t
      rw [if_neg (by linarith)]
      simp_rw [if_neg (show ξ ≠ 0 by linarith)]
      change deriv (Neg.neg ∘ ((fun x => x ^ (-1 / ξ))
        ∘ (fun x ↦ (1 + ξ * ((x - μ) / σ))))) x = _
      rw [deriv_comp]
      all_goals try fun_prop
      swap
      · simp only [t, neg_sub, differentiableAt_fun_neg_iff]
        split_ifs
        all_goals fun_prop
      rw [deriv_neg]
      rw [deriv_comp]
      all_goals try fun_prop
      rw [Real.deriv_rpow_const, deriv_const_add, deriv_const_mul]
      all_goals try fun_prop
      rw [deriv_div_const]
      simp; field_simp; ring_nf
      rw [hσ, hξ, ← rpow_mul]
      all_goals try (field_simp; ring_nf)
      all_goals try (rw [hσ, hξ])
      field_simp at g₂ ⊢
      simp only [sub_nonneg]
      try linarith
    · rw [mul_add, mul_div, mul_comm ξ σ, ← mul_div,
        show ξ / ξ = 1 by exact hξ] at h
      linarith



theorem GEV_deriv_xi_zero (ξ μ σ x : ℝ) (g₀ : ξ = 0) :
  deriv (fun x ↦ rexp (-t ξ μ σ x)) x =
  σ⁻¹ * t ξ μ σ x ^ (ξ + 1) * rexp (-t ξ μ σ x) := by
    change deriv (rexp ∘ fun x ↦ (-t ξ μ σ x)) x = _
    rw [deriv_comp]
    · subst ξ
      rw [Real.deriv_exp]
      rw [mul_comm]
      congr
      unfold t
      simp only [↓reduceIte, neg_sub, deriv.fun_neg', zero_add, rpow_one]
      change -deriv (rexp ∘ fun i ↦ ((μ - i) / σ)) x = _
      rw [deriv_comp]
      · rw [Real.deriv_exp]
        rw [mul_comm]
        simp
        ring_nf
      · fun_prop
      · fun_prop
    · simp [t]
    · unfold t
      split_ifs
      fun_prop


/-- If `f` is truncated to zero on `Set.Iic a` (i.e. we consider
`fun x ↦ if a < x then f x else 0`), then its derivative vanishes at every point `x ≤ a`.
For `x < a` the function is identically zero near `x`; at `x = a` the function is either
not differentiable (so `deriv` is zero by convention) or its derivative agrees with the
left-hand derivative, which is zero. -/
lemma deriv_ite_Iio_of_le (a x : ℝ) (f : ℝ → ℝ)
    (h : x ≤ a) : deriv (fun x ↦ if a < x then f x else 0) x = 0 := by
  set g : ℝ → ℝ := fun x ↦ if a < x then f x else 0 with hg
  rcases lt_or_eq_of_le h with hx | hx
  · have he : g =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp only [hg, Set.mem_Iio] at hy ⊢
      rw [if_neg (not_lt.2 hy.le)]
    rw [he.deriv_eq, deriv_const]
  · subst hx
    by_cases hd : DifferentiableAt ℝ g x
    · have h1 : HasDerivWithinAt g (deriv g x) (Set.Iio x) x :=
        hd.hasDerivAt.hasDerivWithinAt
      have h2 : HasDerivWithinAt g 0 (Set.Iio x) x := by
        apply (hasDerivWithinAt_const x (Set.Iio x) (0:ℝ)).congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          simp only [hg, Set.mem_Iio] at hy ⊢
          rw [if_neg (not_lt.2 hy.le)]
        · simp [hg]
      exact (uniqueDiffWithinAt_Iio x).eq_deriv _ h1 h2
    · exact deriv_zero_of_not_differentiableAt hd

/-
ξ μ σ x : ℝ
hσ : 0 < σ
g₃ : ξ < 0
g₄ : ¬x < μ - σ / ξ
⊢ deriv (fun x ↦ if x < μ - σ / ξ then rexp (-t ξ μ σ x) else 1) x = 0
-/
lemma deriv_ite_Iio_of_le₂ (a x : ℝ) (f : ℝ → ℝ)
    (h : a ≤ x) : deriv (fun x ↦ if x < a then f x else 1) x = 0 := by
  set g : ℝ → ℝ := fun x ↦ if x < a then f x else 1 with hg
  rcases lt_or_eq_of_le h with hx | hx
  · have he : g =ᶠ[nhds x] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp only [hg] at hy ⊢
      rw [if_neg (not_lt.2 hy.le)]
    rw [he.deriv_eq, deriv_const]
  · symm at hx
    subst hx
    by_cases hd : DifferentiableAt ℝ g x
    · have h1 : HasDerivWithinAt g (deriv g x) (Set.Ioi x) x :=
        hd.hasDerivAt.hasDerivWithinAt
      have h2 : HasDerivWithinAt g 0 (Set.Ioi x) x := by
        apply (hasDerivWithinAt_const x (Set.Ioi x) (1:ℝ)).congr_of_eventuallyEq
        · filter_upwards [self_mem_nhdsWithin] with y hy
          simp only [hg] at hy ⊢
          rw [if_neg (not_lt.2 hy.le)]
        · simp [hg]
      exact (uniqueDiffWithinAt_Ioi x).eq_deriv _ h1 h2
    · exact deriv_zero_of_not_differentiableAt hd

theorem deriv_genExtremeCDF_eq_genExtremePDF_converse
  (ξ μ σ x : ℝ)
  (h : ξ = 0 ∧ x ≥ μ)
  : deriv (genExtremeCDF ξ μ σ) x =
    genExtremePDF ξ μ σ x := by
  unfold genExtremeCDF genExtremePDF
  have := @GEV_deriv_xi_zero
  simp at this ⊢
  split_ifs at * with g₀ g₁ g₂ g₃ g₄ g₅
  all_goals
    try linarith
    try tauto

/-- August 10, 2026.
This is remarkably clean. -/
theorem deriv_genExtremeCDF_eq_genExtremePDF (ξ μ σ x : ℝ)
  (hσ : 0 < σ) : deriv (genExtremeCDF ξ μ σ) x
                      = genExtremePDF ξ μ σ x := by
  by_cases h : ξ = 0 → x < μ
  swap
  · exact deriv_genExtremeCDF_eq_genExtremePDF_converse ξ μ σ x (by simp at h;tauto)
  unfold genExtremeCDF genExtremePDF
  simp only [gt_iff_lt, one_div, mul_ite, mul_one, mul_zero]
  split_ifs with g₀ g₁ g₂ g₃ g₄ g₅
  all_goals try apply GEV_deriv_xi_zero <;> tauto
  · simp [t]
    subst ξ
    simp at g₁
  · clear g₀ h
    set g := fun x ↦ if x < μ - σ / ξ then rexp (-t ξ μ σ x) else 1
    set f := fun x ↦ rexp (-t ξ μ σ x)
    have he : g =ᶠ[nhds x] f := by
      filter_upwards [Iio_mem_nhds g₄] with y hy
      rw [Set.mem_Iio] at hy
      unfold g f
      rw [if_pos hy]
    rw [he.deriv_eq] -- !!
    have := @GEV_deriv_xi_nonzero ξ μ σ x hσ (by
      apply mul_pos_of_neg_of_neg g₃
      linarith)
    rw [this]
  · clear g₀ h
    set g := fun x ↦ if x < μ - σ / ξ then rexp (-t ξ μ σ x) else 1
    set f := fun x : ℝ ↦ (1:ℝ)
    simp at g₄
    apply deriv_ite_Iio_of_le₂
    linarith
  · have := @GEV_deriv_xi_nonzero ξ μ σ x hσ (by
      apply mul_pos
      · contrapose! g₀
        linarith
      linarith)
    set g := fun x ↦ if μ - σ / ξ < x then rexp (-t ξ μ σ x) else 0
    set f := fun x ↦ rexp (-t ξ μ σ x)
    have he : g =ᶠ[nhds x] f := by
      filter_upwards [Ioi_mem_nhds g₅] with y hy
      rw [Set.mem_Ioi] at hy
      unfold g f
      rw [if_pos hy]
    rw [he.deriv_eq] -- !!
    rw [this]
  · clear h
    simp at g₅
    have : ξ > 0 := by contrapose! g₀;linarith
    unfold t
    apply deriv_ite_Iio_of_le; tauto

/-- As long as `ξ = 0` or `x ≠ μ - σ / ξ`, the two definitions
of the PDF of the generalized extreme value distribution agree. -/
lemma GEVPDF_eq_genExtremePDF (ξ μ σ : ℝ) :
    GEVPDF ξ μ σ =ᵐ[MeasureTheory.volume] genExtremePDF ξ μ σ := by
  by_cases hξ : ξ = 0
  · subst ξ
    apply EqOn.aeEq (s := Set.univ)
    · unfold GEVPDF genExtremePDF
      simp
    · simp
  apply EqOn.aeEq (s := {μ - σ / ξ}ᶜ)
  · unfold GEVPDF genExtremePDF t
    intro x hx
    simp only [one_div, neg_sub, ite_pow, mul_ite, ite_mul, ge_iff_le, tsub_le_iff_right,
      mul_one, mul_zero, gt_iff_lt]
    split_ifs
    all_goals try rfl
    all_goals
      apply False.elim ∘ hx
      rw [mem_singleton_iff]
      linarith
  · simp

/-- When ξ = -1, there is a problem at x=2.
The problem is that GEVPDF' uses 0^0 = 1. GevPDF is intended to fix that.
-/
def GevPDF (ξ μ σ : ℝ) :=
  let t := fun x => ite (ξ = 0)
    (exp (- (x - μ)/ σ))
    ((1 + ξ * ((x - μ)/σ))⁺ ^ (-1 / ξ))
  {x | t x > 0}.indicator
  fun x => (1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)

lemma GevPDF_ne_GEVPDF :
    GEVPDF (-1) 0 1 1 ≠ GevPDF (-1) 0 1 1 := by
  unfold GEVPDF GevPDF
  simp

/-- The open-interval version of the GEV PDF
agrees with the one defined more simply in terms of []⁺, GevPDF.
-/
lemma genExtremePDF_eq_GevPDF (ξ σ : ℝ) (hσ : 0 ≤ σ) :
     (fun μ => genExtremePDF ξ μ σ)
    = fun μ => GevPDF ξ μ σ := by
  by_cases H : σ = 0
  · subst σ
    unfold genExtremePDF
    simp [GevPDF]
  ext μ x
  simp only [genExtremePDF, one_div, t, neg_sub, ite_pow, mul_ite, ite_mul, gt_iff_lt, mul_one,
    mul_zero, GevPDF]
  split_ifs with g₀ g₁ g₂ g₃ g₄ g₅
  · linarith
  · simp only [indicator, mem_setOf_eq]
    have h₀ : ξ * μ ≤ σ + ξ * x := by
      have : ξ * x > ξ * (μ -(σ / ξ)) := mul_lt_mul_of_neg_left g₁ g₀
      simp at this
      field_simp at this
      nth_rw 1 [mul_comm] at this
      rw [mul_div_assoc] at this
      rw [(div_eq_one_iff_eq g₂).mpr rfl] at this
      simp at this
      linarith
    split_ifs with g₃
    · simp only [posPart]
      rw [max_eq_left]
      field_simp
      linarith
    · apply False.elim ∘ g₃
      simp only [posPart, not_lt] at g₃ ⊢
      rw [max_eq_left] at g₃ ⊢
      · apply rpow_pos_of_pos
        have : ξ * x > ξ * (μ -(σ / ξ)) := mul_lt_mul_of_neg_left g₁ g₀
        simp at this
        field_simp at this
        nth_rw 1 [mul_comm] at this
        rw [mul_div_assoc] at this
        rw [(div_eq_one_iff_eq g₂).mpr rfl] at this
        field_simp
        linarith
      all_goals field_simp; linarith
  · subst ξ
    simp at g₀
  · simp only [indicator, posPart, mem_setOf_eq, right_eq_ite_iff, zero_eq_mul, mul_eq_zero,
    inv_eq_zero, exp_ne_zero, or_false]
    intro h
    simp only [not_lt, tsub_le_iff_right] at g₁
    right
    have : σ + ξ * (x - μ) ≠ 0 := by
      intro hc
      have hc :  (σ + (ξ * (x - μ))) / σ = 0 := by rw [hc];exact zero_div σ
      rw [add_div] at hc
      have : σ ≠ 0 := H
      have : σ / σ = 1 := by exact (div_eq_one_iff_eq this).mpr rfl
      rw [this] at hc
      rw [mul_div_assoc] at hc
      rw [hc] at h
      revert h
      simp only [max_self, imp_false, not_lt]
      apply le_of_eq
      refine zero_rpow ?_
      field_simp
      contrapose! g₃
      simp only [one_div, neg_eq_zero, inv_eq_zero] at g₃
      exact g₃
    have hhh :  (σ + ξ * (x - μ)) / σ ≠ 0 := by
      contrapose! this
      rw [div_eq_zero_iff] at this
      cases this with
      | inl h => tauto
      | inr h => subst σ;simp at H
    have hh :  (σ + ξ * (x - μ)) / σ < 0 := by
      field_simp
      simp
      field_simp at g₁
      have g₁ :  μ * ξ ≥ (x * ξ + σ) / ξ * ξ := by
        exact (mul_le_mul_right_of_neg g₀).mpr g₁
      have g (r : ℝ) : r / ξ * ξ = r := by field_simp
      rw [g] at g₁
      contrapose! this
      apply le_antisymm
      · linarith
      · linarith
    rw [max_eq_right] at h
    · exfalso
      revert h
      simp only [imp_false, not_lt]
      apply le_of_eq
      refine zero_rpow ?_
      field_simp
      simp
      tauto
    field_simp at hh ⊢
    linarith
  · subst ξ
    simp only [zero_add, rpow_one, indicator, mem_setOf_eq, left_eq_ite_iff, not_lt, mul_eq_zero,
      inv_eq_zero, exp_ne_zero, or_false]
    intro h
    exfalso
    revert h
    simp only [imp_false, not_le]
    exact exp_pos _
  · simp only [indicator, mem_setOf_eq]
    have h₀ : 0 < ξ := by contrapose! g₄;linarith
    split_ifs with g
    · simp only [posPart]
      rw [max_eq_left]
      field_simp
      have :  (μ - σ / ξ) * ξ < x * ξ := by exact
        MulPosStrictMono.mul_lt_mul_of_pos_right h₀ g₅
      field_simp at this
      linarith
    · simp only [posPart, not_lt] at g
      rw [max_eq_left] at g
      · exfalso
        revert g
        simp only [imp_false, not_le]
        refine rpow_pos_of_pos ?_ (-1 / ξ)
        field_simp
        simp
        field_simp at g₅
        linarith
      rw [max_eq_left] at g
      all_goals
      · field_simp at g₅
        field_simp
        linarith
  · simp at g₅
    simp only [indicator, mem_setOf_eq, right_eq_ite_iff, zero_eq_mul, mul_eq_zero, inv_eq_zero,
      exp_ne_zero, or_false]
    intro h
    simp only [posPart]
    simp at g₀
    have : 0 < ξ := by contrapose! g₄;linarith
    right
    simp only [posPart] at h
    rw [max_eq_right] at h
    · field_simp at g₅
      exfalso
      revert h
      simp only [imp_false, not_lt]
      apply le_of_eq
      refine zero_rpow ?_
      simp
      tauto
    · field_simp at g₅ ⊢
      linarith


lemma GEVPDF_simplify.aux (ξ μ σ x : ℝ) (hσ : 0 < σ) :
  ite (ξ < 0) (ite (x ≤ μ - σ/ξ) 1 0)
    (ite (ξ = 0) 1 (ite (x ≥ μ - σ/ξ) 1 0))
  = ite ((x - μ) * ξ + σ ≥ 0) 1 0 := by
  split_ifs with g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₆ g₇
  all_goals try rfl
  · apply g₂
    clear g₂
    have : ξ ≠ 0 := by linarith
    field_simp at *
    have h₀ :  x * ξ ≥ ((μ * ξ - σ) / ξ) * ξ := by
      apply (mul_le_mul_right_of_neg g₀).mpr g₁
    have h₁ : (μ * ξ - σ) / ξ * ξ = (μ * ξ - σ) := by
      apply div_mul_cancel₀ _ this
    rw [h₁] at h₀
    field_simp at *
    linarith
  · simp at g₁
    field_simp at *
    have : ξ⁻¹ < 0 := inv_lt_zero.mpr g₀
    have h₀ : (μ - σ / ξ) * ξ > x * ξ := by
      exact mul_lt_mul_of_neg_right g₁ g₀
    ring_nf at h₀
    have : ξ * ξ⁻¹ = 1 := by refine CommGroupWithZero.mul_inv_cancel ξ ?_;linarith
    rw [mul_assoc,this] at h₀
    linarith
  · subst ξ; simp at g₅;linarith
  · apply g₆
    clear g₆
    have : ξ > 0 := by contrapose! g₄;linarith
    clear g₀ g₄
    have :  x * ξ ≥ (μ - σ / ξ) * ξ :=
      (mul_le_mul_iff_of_pos_right this).mpr g₆
    field_simp at this
    linarith
  · simp at g₆ g₀
    field_simp at *
    linarith

/-- The GEVPDF formula can be simplied when σ > 0. -/
theorem GEVPDF_simplify (ξ μ σ x : ℝ) (hσ : 0 < σ) :
 GEVPDF ξ μ σ x =
  let t := t ξ μ σ
  ((1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)) *
   ite ((x - μ) * ξ + σ ≥ 0) 1 0 := by
  unfold GEVPDF t
  have := GEVPDF_simplify.aux ξ μ σ x hσ
  split_ifs at *
  all_goals linarith

/-- Perhaps the simplest expression for the GEV PDF so far. -/
theorem genExtremePDF_simplify (ξ μ σ x : ℝ) (hσ : 0 < σ) :
 genExtremePDF ξ μ σ x =
  let t := t ξ μ σ
  ((1 / σ) * (t x) ^ (ξ + 1) * exp (-t x)) *
   ite ((x - μ) * ξ + σ > 0) 1 0 := by
  unfold genExtremePDF t
  have := GEVPDF_simplify.aux ξ μ σ x hσ
  by_cases H : ξ = -1
  · subst ξ
    simp
    split_ifs with g₀ g₁
    · rfl
    · simp
      linarith
    · simp
      linarith
    · rfl
  split_ifs at *
  all_goals try linarith
  all_goals try simp only [one_div, mul_zero, mul_one, zero_eq_mul, mul_eq_zero, inv_eq_zero,
    exp_ne_zero, or_false]
  all_goals right
  all_goals try subst ξ
  all_goals try simp_all only [zero_eq_neg, one_ne_zero, not_false_eq_true, lt_self_iff_false,
    mul_zero, zero_add, gt_iff_lt, not_true_eq_false]
  all_goals
    suffices 1 + ξ * ((x - μ) / σ) = 0 by
      rw [this]
      rw [rpow_eq_zero]
      rw [rpow_eq_zero]
      simp
      simp
      tauto
      apply le_of_eq
      symm
      rw [rpow_eq_zero]
      simp
      simp
      tauto
      contrapose! H
      linarith
  · field_simp
    linarith
  · field_simp
    simp
    have : μ = x + σ / ξ := by linarith
    subst μ
    simp_all
  · field_simp
    linarith
  · field_simp
    have : μ = x + σ / ξ := by linarith
    subst μ
    simp_all


/-- The cumulative distribution function of the generalized
extreme value distribution with ξ = 0 : the Gumbel distribution.
-/
def GumbelPDF := GEVPDF 0

/-- The "standard" Gumbel distribution. -/
def StandardGumbelPDF := GumbelPDF 0 1

def StandardFrechétPDF := GEVPDF 1 0 1

def StandardWeibullPDF := GEVPDF (-1) 0 1

theorem antitone_neg_exp : Antitone (Neg.neg ∘ rexp) := by
                refine Antitone.comp_monotone ?_ ?_
                · refine StrictAnti.antitone ?_
                  refine strictAnti_of_deriv_neg ?_
                  simp
                exact exp_monotone
open MeasureTheory
theorem integrable_exp_neg_sub_exp_neg :
  MeasureTheory.Integrable (fun x : ℝ ↦ rexp (-x + -rexp (-x))) volume := by
  let f : ℝ → ℝ := fun x ↦ rexp (-x + -rexp (-x))
  have hf_cont : Continuous f := by
    dsimp [f]
    fun_prop
  have hneg : IntegrableOn f (Set.Iic 0) volume := by
    apply Integrable.mono' (integrableOn_exp_Iic 0)
    · exact hf_cont.aestronglyMeasurable
    · filter_upwards with x
      dsimp [f]
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp_of_le
      have h := Real.two_mul_le_exp (x := -x)
      linarith
  have hpos : IntegrableOn f (Set.Ioi 0) volume := by
    apply Integrable.mono' (integrableOn_exp_neg_Ioi 0)
    · exact hf_cont.aestronglyMeasurable
    · filter_upwards with x
      dsimp [f]
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp_of_le
      exact add_le_of_nonpos_right (neg_nonpos.mpr (Real.exp_nonneg _))
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
  exact hneg.union hpos

lemma integral_StandardGumbelPDF_eq_one : ∫ x : ℝ, StandardGumbelPDF x = 1 := by
    simp only [StandardGumbelPDF, GumbelPDF, GEVPDF, t, one_div, ↓reduceIte, neg_sub, zero_add,
      rpow_one, lt_self_iff_false, mul_one]
    let t (x : ℝ) := rexp ((0 - x) / 1)
    change ∫ (x : ℝ), 1⁻¹ * t x * rexp (-t x) = 1
    · field_simp at *
      have h₀ : deriv (fun x => rexp (-t x)) =
        (fun x => rexp (-t x) * deriv (fun x => -t x) x) := by
        change deriv (rexp ∘ fun x => -t x) = _
        ext x
        rw [deriv_comp]
        · congr
          rw [Real.deriv_exp]
        · fun_prop
        · fun_prop
      simp only [deriv.fun_neg', mul_neg] at h₀
      have h₁ : deriv t = fun x => -t x := by
        simp only [div_one, t]
        change deriv (rexp ∘ fun x => 0 - x) = _
        ext x
        rw [deriv_comp]
        · rw [Real.deriv_exp]
          simp
        · fun_prop
        · fun_prop
      rw [h₁] at h₀
      clear h₁
      simp only [mul_neg, neg_neg] at h₀
      simp_rw [mul_comm] at h₀
      simp_rw [← h₀]
      change ∫ x : ℝ, (deriv fun x ↦ rexp (-t x)) x = 1
      · simp only [zero_sub, div_one, t]
        have {f : ℝ → ℝ} {a b : ℝ}
          (ha : Tendsto f atTop (nhds a)) (hb : Tendsto f atBot (nhds b))
          (hdiff : ∀ x, DifferentiableAt ℝ f x)
          (hint : MeasureTheory.Integrable (deriv f))
          : ∫ x : ℝ, deriv f x = a - b := by
            apply MeasureTheory.integral_of_hasDerivAt_of_tendsto
              (htop := ha) (hbot := hb) (hderiv := fun x => (hdiff x).hasDerivAt)
              (hf' := hint)
        rw [this]
        · change 1 - 0 = 1
          simp
        · change Tendsto (rexp ∘ fun x => (-rexp (-x))) atTop (𝓝 1)
          have h₁ : Tendsto (fun x ↦ -rexp (-x)) atTop (𝓝 0) := by
            change Tendsto (Neg.neg ∘ fun x ↦ rexp (-x)) atTop (𝓝 (0))
            suffices Tendsto (Neg.neg ∘ fun x ↦ rexp (-x)) atTop (𝓝 (Neg.neg 0)) by
              convert this
              simp
            refine (Topology.IsOpenEmbedding.tendsto_nhds_iff ?_).mp ?_
            · refine { toIsEmbedding := ?_, isOpen_range := ?_ }
              · refine Topology.IsEmbedding.mk' Neg.neg neg_injective ?_
                · simp only [Filter.comap_neg]
                  intro x
                  rw [← nhds_neg]
                  simp
              · have : IsOpen (Set.univ : Set ℝ) := by simp
                convert this
                refine range_eq_univ.mpr neg_surjective
            change Tendsto (rexp ∘ fun x ↦ -x) atTop (𝓝 0)
            suffices Tendsto (rexp ∘ fun x ↦ x) atBot (𝓝 0) by
              refine tendsto_comap_iff.mp ?_
              simp only [comap_exp_nhds_zero]
              exact tendsto_neg_atTop_atBot
            exact tendsto_exp_atBot
          suffices Tendsto (rexp ∘ fun x ↦ -rexp (-x)) atTop (𝓝 (rexp 0)) by
            convert this
            simp
          refine (Topology.IsOpenEmbedding.tendsto_nhds_iff ?_).mp h₁
          exact isOpenEmbedding_exp
        · have h₁ : Tendsto (fun x ↦ -rexp (-x)) atBot atBot := by
            suffices Tendsto (Neg.neg ∘ rexp) atTop atBot by
              apply tendsto_atBot_atBot_of_monotone
              · apply antitone_neg_exp.comp
                · apply StrictAnti.antitone
                  apply strictAnti_of_deriv_neg
                  simp
              · intro a
                by_cases H : a ≥ -1
                · use 0
                  simp
                  tauto
                simp at H
                suffices ∃ x, rexp (-x) ≥ -a by
                  contrapose! this
                  intro x
                  exact lt_neg_of_lt_neg <| this x
                suffices ∃ x, rexp x ≥ -a by
                  contrapose! this
                  intro x
                  specialize this (-x)
                  simp at this
                  tauto
                use log (-a)
                rw [exp_log]
                simp at H ⊢
                linarith
            apply tendsto_atTop_atBot_of_antitone
            · exact antitone_neg_exp
            · intro b
              suffices ∃ x, rexp x ≥ -b by
                contrapose! this
                intro x
                specialize this x
                simp at this
                linarith
              by_cases hb : 0 < b
              · use log b
                rw [exp_log]
                · linarith
                · tauto
              · by_cases H : b = 0
                · use 0
                  subst b
                  simp
                · use log (-b)
                  rw [exp_log]
                  contrapose! H;linarith
          exact tendsto_exp_atBot.comp h₁
        · fun_prop
        · simp only [zero_sub, div_one, t] at h₀
          simp_rw [h₀]
          simp_rw [← exp_add]
          apply integrable_exp_neg_sub_exp_neg


theorem GEVPDF_nonneg.extracted (μ σ ξ x : ℝ) (hσ : 0 ≤ σ) (h : ξ ≤ 0)
    (h₁ : x ≤ μ - σ / ξ) :
    0 ≤ 1 + ξ * ((x - μ) / σ) := by
  by_cases h_2 : ξ = 0
  · subst ξ
    simp
  by_cases hσ' : σ = 0
  · subst σ
    simp
  suffices  -ξ * ((x - μ) / σ) ≤ 1 by linarith
  have : (x - μ) / σ ≤ (- (σ / ξ)) / σ := by field_simp;linarith
  apply le_trans
  · change _ ≤ -ξ * ( -(σ / ξ) / σ)
    refine mul_le_mul_of_nonneg ?_ this ?_ ?_
    · simp
    · linarith
    · field_simp
      simp
      linarith
  field_simp
  simp

lemma GEVPDF_nonneg (μ σ ξ x : ℝ) (hσ : 0 ≤ σ) : GEVPDF ξ μ σ x ≥ 0 := by
  unfold GEVPDF t
  simp only [one_div, neg_sub, ite_pow, mul_ite, ite_mul, ge_iff_le, tsub_le_iff_right, mul_one,
    mul_zero]
  by_cases hσ' : σ = 0
  · clear hσ
    subst σ
    simp
  have hσ : 0 < σ := by contrapose! hσ';linarith
  split_ifs with g₀ g₁ g₂ g₃ g₄
  all_goals try positivity
  · have hσ : 0 ≤ σ := by linarith
    have := GEV.GEVPDF_nonneg.extracted μ σ ξ x hσ
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · repeat apply rpow_nonneg
        have : ξ ≤ 0 := by linarith
        tauto
    · positivity
  · have h₁ : μ * ξ ≤ ((ξ * x + σ) / ξ) * ξ := by
      apply mul_le_mul_of_mul_div_le
      · field_simp at *
        rw [mul_div_cancel_left₀ _ g₃]
        exact g₄
      contrapose! g₃
      apply le_antisymm g₃
      simp at g₀
      tauto
    have h₀ : μ * ξ ≤ (ξ * x + σ) := by
      field_simp at *
      apply le_trans h₁
      rw [mul_div_cancel_left₀ _ g₃]
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      repeat apply rpow_nonneg
      field_simp at *
      simp
      linarith
    positivity
end GEV
