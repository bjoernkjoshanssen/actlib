import Mathlib

noncomputable section

-- define g (x) = cos^2(x) + 5
def g (x : ℝ) := (Real.cos x) ^ 2 + 5

theorem easy_fact : g 0 = 6 := by
  unfold g
  simp
  norm_num

example : g 0 = 6 := by
  unfold g
  simp only [Real.cos_zero, one_pow]
  norm_num

-- define f (x)  = (1+x)^-2
def f (x : ℝ) := (1+x)^(-2:ℝ)
-- prove that f 0 = 1
example : f 0 = 1 := by
  unfold f
  simp

-- define F (x,y) = x^2 + y^2
def F (x y : ℝ) := x^2 + y^2
example (x y : ℝ) : F x y = F y x := by
  unfold F
  ring
-- define G(x,y) = cos^2(x) + sin^2(y) and prove G 0 0 = 1
def G (x y : ℝ) := (Real.cos x )^2 + (Real.sin y )^2

example : G 0 0 = 1 := by
  unfold G
  simp

def pareto (μ σ ξ : ℝ) := if ξ = 0 then μ / σ + Real.exp ξ else 5

-- homework: put definition of GPD probability density function

def xi_notzero (ξ μ σ x : ℝ) := (1 / σ) * Real.rpow (1 + ξ * ((x - μ)) / σ) (-1-(1/ξ))

def xi_zero (μ σ x : ℝ) := (1 / σ) * Real.exp ( -(x - μ) / σ)

def pdf (μ σ ξ x : ℝ) :=
  if ξ = 0 then
    if x ≥ μ then xi_zero μ σ x
    else 0
  else if ξ < 0 then
    if μ ≤ x ∧ x ≤ μ - σ / ξ then xi_notzero ξ μ σ x
    else 0
  else
    if ξ > 0 ∧ x ≥ μ then xi_notzero ξ μ σ x
    else 0

 lemma firstlemma (x : ℝ) (hx: 1 ≤ x)  : pdf 1 1 1 x = (x) ^ (-2:ℝ) := by
  unfold pdf
  norm_num
  unfold xi_notzero
  norm_num
  simp_all

lemma secondlemma (x : ℝ) : pdf 1 1 1 x = ite (1 ≤ x) ((x) ^ (-2:ℝ)) 0 := by
 split_ifs with h
 rw [firstlemma]
 exact h
 unfold pdf
 norm_num
 unfold xi_notzero
 norm_num
 simp_all

lemma thirdlemma {μ σ ξ x :ℝ } (hσ: 0 ≤ σ) : pdf μ σ ξ x ≥ 0 := by
  unfold pdf
  unfold xi_zero
  unfold xi_notzero
  split_ifs with h1 h2 h3 h4 h5
  apply mul_nonneg
  apply div_nonneg
  norm_num
  exact hσ
  apply Real.exp_nonneg
  norm_num
  apply mul_nonneg
  apply div_nonneg
  norm_num
  exact hσ
  apply Real.rpow_nonneg

  by_cases H : σ = 0
  · subst σ
    simp
  · suffices h : 0 ≤ σ + ξ * (x-μ) by
      have : 0 ≤ (σ + ξ * (x-μ)) / σ := by
        apply div_nonneg
        exact h
        exact hσ
      field_simp at this ⊢
      exact this


    have : ξ * x ≥ ξ * μ - σ := by
      /-
      x ≤ μ - σ / ξ
      ξ * x ≥ ξ * μ - σ
      -/
      have h6 : x * ξ  ≥ (μ - σ / ξ)* ξ := by
        exact (mul_le_mul_right_of_neg h3).mpr h4.2
      rw [sub_mul] at h6
      have h7 : σ / ξ * ξ = σ := by
        apply div_mul_cancel₀ σ h1
      linarith

    linarith


  norm_num

  apply mul_nonneg
  apply div_nonneg
  norm_num
  exact hσ
  apply Real.rpow_nonneg
  apply add_nonneg
  norm_num
  apply div_nonneg
  apply mul_nonneg
  linarith
  linarith
  exact hσ
  norm_num



-- Cumulative distribution function
def cdf_xi_notzero (ξ μ σ x : ℝ) :=
  1 - Real.rpow (1 + ξ * (x - μ) / σ) (-1 / ξ)

def cdf_xi_zero (μ σ x : ℝ) :=
  1 - Real.exp (-(x - μ) / σ)

def cdf (μ σ ξ x : ℝ) :=
  if ξ = 0 then
    if x ≥ μ then cdf_xi_zero μ σ x
    else 0
  else if ξ < 0 then
    if μ ≤ x ∧ x ≤ μ - σ / ξ then cdf_xi_notzero ξ μ σ x
    else 0
  else
    if ξ > 0 ∧ x ≥ μ then cdf_xi_notzero ξ μ σ x
    else 0


lemma cdf_firstlemma (x : ℝ) (hx : 1 ≤ x) : cdf 1 1 1 x = 1 - (x)^(-1 : ℝ) := by
  unfold cdf
  norm_num
  unfold cdf_xi_notzero
  norm_num
  simp_all

lemma cdf_secondlemma (x : ℝ) : cdf 1 1 1 x = ite (1 ≤ x) (1 - (x)^(-1 : ℝ)) 0 := by
  split_ifs with h
  rw [cdf_firstlemma]
  exact h
  unfold cdf
  norm_num
  unfold cdf_xi_notzero
  norm_num
  simp_all

lemma cdf_thirdlemma {σ μ ξ x} (hσ : 0 < σ) : cdf μ σ ξ x ≥ 0 := by
  unfold cdf cdf_xi_zero cdf_xi_notzero
  split_ifs with h1 h2 h3 h4 h5

  norm_num
  · rw [div_nonpos_iff]
    right
    constructor
    linarith
    linarith
  · norm_num
  · have this1 : (1 + ξ * (x - μ) / σ) ≥ 0 := by
      have hξ : ξ ≠ 0 := ne_of_lt h3
      have hb := mul_le_mul_of_nonpos_left h4.2 (le_of_lt h3)
      have hd : ξ * (σ / ξ) = σ := by
        field_simp
      have hn : 0 ≤ σ + ξ * (x - μ) := by
        nlinarith
      have hf : 1 + ξ * (x - μ) / σ =
          (σ + ξ * (x - μ)) / σ := by
        field_simp
      rw [hf]
      exact div_nonneg hn (le_of_lt hσ)
    have this2 : 1 ≥ 1 + ξ * (x - μ) / σ := by
      apply add_le_of_nonpos_right
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · linarith
        · linarith [h4.1]
      · exact le_of_lt hσ
    -- Real.rpow_le_one
    suffices 1 ≥ (1 + ξ * (x - μ) / σ).rpow (-1 / ξ) by linarith
    apply Real.rpow_le_one
    exact this1
    exact this2
    suffices 0 ≤ -(1 / ξ) by
      rw [div_nonneg_iff]
      right
      norm_num
      linarith
    simp
    linarith
  · norm_num
  · have hb : 1 ≤ 1 + ξ * (x - μ) / σ := by
      apply le_add_of_nonneg_right
      apply div_nonneg
      · apply mul_nonneg
        · exact le_of_lt h5.1
        · linarith [h5.2]
      · exact le_of_lt hσ
    have he : -(1 / ξ) ≤ 0 := by
      apply neg_nonpos.mpr
      apply div_nonneg
      · norm_num
      · exact le_of_lt h5.1
    have hp : (1 + ξ * (x - μ) / σ).rpow (-1 / ξ) ≤ 1 := by
      have hpos : 0 < 1 + ξ * (x - μ) / σ := by
        linarith
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact hb
      · rw [neg_div]
        exact he
    linarith
  · norm_num


-- derivative of F is f

lemma helpful (f : ℝ → ℝ) : deriv (fun x => 1 - f x) =
  deriv (fun _ => 1) - deriv f := by
    ext z
    simp [deriv_const_sub']

--DifferentiableAt: fun_prop

-- ξ = 0
lemma deriv_cdf_gpd_xi_zero (μ σ x : ℝ) :
  deriv (fun x : ℝ => cdf_xi_zero μ σ x) x = xi_zero μ σ x := by

  unfold xi_zero cdf_xi_zero
  rw [helpful]
  simp only [deriv_const', neg_sub, Pi.sub_apply, zero_sub, one_div]
  rw [deriv_exp]
  simp
  ring
  apply DifferentiableAt.div_const
  fun_prop

-- ξ ≠ 0
lemma deriv_cdf_gpd_xi_notzero_hb_ge_zero(ξ μ σ x : ℝ) (hb : 0 < 1 + ξ * (x - μ) / σ) (hξ : ξ ≠ 0) :
  deriv (fun x : ℝ => cdf_xi_notzero ξ μ σ x) x = xi_notzero ξ μ σ x := by

  unfold cdf_xi_notzero xi_notzero
  simp_all
  rw [deriv_rpow_const]
  simp_all
  ring_nf
  fun_prop
  left
  exact ne_of_gt hb



-- deriv
lemma deriv_cdf_gpd_eq_gpf
  (μ σ ξ x : ℝ)
  (hσ : 0 < σ)
  (hx : μ < x)
  (hb : 0 < 1 + ξ * (x - μ) / σ) :
  deriv (fun y : ℝ => cdf μ σ ξ y) x = pdf μ σ ξ x := by
  by_cases hξ : ξ = 0
  · -- ξ = 0
    subst ξ
    unfold pdf
    simp_all
    rw [ite_eq_left (le_of_lt hx)]
    rw [← deriv_cdf_gpd_xi_zero μ σ x] 
      -- lemma deriv_cdf_gpd_xi_zero (μ σ x : ℝ) :
      -- deriv (fun x : ℝ => cdf_xi_zero μ σ x) x = xi_zero μ σ x
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp [cdf, hy.le]
  · by_cases hξ_neg : ξ < 0
    · -- ξ < 0
      have hupper : x < μ - σ / ξ := by
        rw [lt_sub_iff_add_lt]
        rw [add_div_eq_mul_add_div x σ hξ]
        rw [div_lt_iff_of_neg hξ_neg]
        field_simp at hb
        nlinarith
      unfold pdf
      simp [hξ, hξ_neg, le_of_lt hx, le_of_lt hupper]
      rw [← deriv_cdf_gpd_xi_notzero_hb_ge_zero ξ μ σ x hb hξ]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hupper] with y hy1 hy2
      simp [cdf, hξ, hξ_neg, le_of_lt hy1, le_of_lt hy2]
    · -- ξ > 0
      have hpos : 0 < ξ := by
        apply lt_of_le_of_ne
        · exact le_of_not_gt hξ_neg
        · exact Ne.symm hξ --flip the not equal
      unfold pdf
      simp [hξ, hξ_neg, hpos, le_of_lt hx]
      rw [← deriv_cdf_gpd_xi_notzero_hb_ge_zero ξ μ σ x hb hξ]
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [cdf, hξ, hξ_neg, hpos, le_of_lt hy]


lemma deriv_cdf_gpd_xi_notzero_hb_zero (ξ μ σ x : ℝ) (hb : 1 + ξ * (x - μ) / σ = 0) (hξ : ξ ≠ 0) (h_exp : 1 ≤ -1 / ξ):
  deriv (fun x : ℝ => cdf_xi_notzero ξ μ σ x) x = xi_notzero ξ μ σ x := by
  unfold cdf_xi_notzero xi_notzero
  simp_all
  rw [deriv_rpow_const]
  simp [hb]
  ring_nf
  field_simp [hξ]
  fun_prop
  right
  exact h_exp




/-
mode: μ
for all x, pdf (x) ≤ pdf (μ)
-/

lemma mode_gpd (μ σ ξ x : ℝ) (hσ : 0 < σ) (hξ : -1 ≤ ξ) : -- pdf increasing
  pdf μ σ ξ x ≤ pdf μ σ ξ μ := by
  by_cases hx : x ≥ μ
  · -- x ≥ μ
    unfold pdf
    simp_all
    by_cases hzero : ξ = 0
    · -- ξ = 0
      simp [hzero]
      unfold xi_zero
      simp
      have he : Real.exp ((μ - x) / σ) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        linarith
      suffices h : σ⁻¹ * Real.exp ((μ - x) / σ) ≤ σ⁻¹ * 1 by 
      -- σ⁻¹ * 1 : mul_of_nonneg
        simp_all
      apply mul_le_mul_of_nonneg_left
      exact he
      apply inv_nonneg.mpr
      linarith

    · by_cases hneg : ξ < 0
      · -- ξ < 0
        have ha : σ / ξ ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · linarith
          · linarith
        simp_all
        by_cases hupper : x ≤ μ - σ / ξ
        · simp [hupper]
          unfold xi_notzero
          simp
          have hb : 0 ≤ 1 + ξ * (x - μ) / σ := by
            have h : x - μ ≤ -σ / ξ := by
              rw [neg_div]
              linarith
            have hc := (le_div_iff_of_neg hneg).mp h
            have hd : -1 ≤ ξ * (x - μ) / σ := by
              apply (le_div_iff₀ hσ).2
              nlinarith
            linarith

          have hc : 1 + ξ * (x - μ) / σ ≤ 1 := by
            have h : ξ * (x - μ) ≤ 0 := by
              apply mul_nonpos_of_nonpos_of_nonneg
              · linarith
              · linarith
            have hd : ξ * (x - μ) / σ ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              · exact h
              · linarith
            linarith

          have hd : 0 ≤ -1 - ξ⁻¹ := by
            have h : 1 / ξ ≤ -1 := by
              apply (div_le_iff_of_neg hneg).2
              linarith
            rw [one_div] at h
            linarith

          have he : (1 + ξ * (x - μ) / σ) ^
              (-1 - ξ⁻¹) ≤ 1 := by
            apply Real.rpow_le_one
            · exact hb
            · exact hc
            · exact hd

          suffices h : σ⁻¹ * (1 + ξ * (x - μ) / σ) ^
              (-1 - ξ⁻¹) ≤ σ⁻¹ * 1 by
            simp_all
          apply mul_le_mul_of_nonneg_left
          · exact he
          · apply inv_nonneg.mpr
            linarith

        · -- x is above the upper bound
          simp [hupper]
          unfold xi_notzero
          simp [le_of_lt hσ]

      · -- ξ > 0
        have hpos : 0 < ξ := by
          apply lt_of_le_of_ne
          · exact le_of_not_gt hneg
          · exact Ne.symm hzero
        simp [hzero, hneg, hpos]
        unfold xi_notzero
        simp

        have hb : 1 ≤ 1 + ξ * (x - μ) / σ := by
          have h : 0 ≤ ξ * (x - μ) / σ := by
            apply div_nonneg
            · apply mul_nonneg
              · linarith
              · linarith
            · linarith
          linarith

        have hc : -1 - ξ⁻¹ ≤ 0 := by
          have h : 0 ≤ ξ⁻¹ := by
            apply inv_nonneg.mpr
            linarith
          linarith

        have he : (1 + ξ * (x - μ) / σ) ^
            (-1 - ξ⁻¹) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos
          · exact hb
          · exact hc

        suffices h : σ⁻¹ * (1 + ξ * (x - μ) / σ) ^
            (-1 - ξ⁻¹) ≤ σ⁻¹ * 1 by
          simp_all
        apply mul_le_mul_of_nonneg_left
        · exact he
        · apply inv_nonneg.mpr
          linarith

  · -- x < μ
    have h : pdf μ σ ξ x = 0 := by
      simp [pdf, hx]
    rw [h]
    exact thirdlemma (le_of_lt hσ)
    


--median
-- cdf (median) = 1/2

def median (μ σ ξ : ℝ) : ℝ :=
  if ξ = 0 then μ + σ * Real.log (2)
  /- 
  F = 1 - e ^ (-(x - μ) / σ)
  e ^ (-(x - μ) / σ) = 1/2
  -(x - μ) / σ = log (1/2)
  -(x - μ) / σ = -log (2)
  x - μ = σ log (2)
  x = μ + σ log (2)
  -/
  else μ + (σ / ξ) * (Real.rpow (2) (ξ - 1))
  /-
  F = 1 - (1 + ξ(x - μ)/σ)^(-1/ξ)
  1 - (1 + ξ(x - μ)/σ)^(-1/ξ) = 1/2
  (1 + ξ(x - μ)/σ)^(-1/ξ) = 1/2
  1 + ξ(x - μ)/σ = (1/2)^(-ξ)
  1 + ξ(x - μ)/σ = 2 ^ ξ
  ξ(x - μ)/σ = 2^ξ - 1
  x - μ = (σ/ξ)(2^ξ - 1)
  x = μ + (σ/ξ)(2^ξ - 1)
  -/

lemma median_gpd (μ σ ξ : ℝ) (hσ : 0 < σ) : 
  cdf μ σ ξ (median μ σ ξ) = 1/2 := by
  have hσ_ze_zero : σ ≠ 0 := by
    linarith
  
  by_cases hzero : ξ = 0
  · -- ξ = 0
    sorry
  · -- ξ ≠ 0
    sorry
