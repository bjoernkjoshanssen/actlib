import Mathlib
import Actlib.Laplace.MainTheorem
import Actlib.Tweedie.ExponentialDispersion
import Mathlib.Probability.Distributions.Gamma

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
set_option maxRecDepth 4000

set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Real MeasureTheory Set Filter Topology

noncomputable section

-- def wright_generalized_bessel (Λ μ : ℝ) (z : ℝ) :=
--     ∑' k : ℕ, z ^ k / (Nat.factorial k * Gamma (Λ * k + μ))

local notation "𝓦" => wright_generalized_bessel

/- Tweedie PDF for `2 < p < 3`, expressed using Wright's generalized Bessel function. -/
-- def tweediePDF₂₃ (p μ phi : ℝ) (y : ℝ) : ℝ :=
--     let α := (2 - p) / (1 - p)
--     Set.indicator {y : ℝ | 0 < y} (
--     fun y => 1 / y * 𝓦 (-α) 0 (
--         - y^(-α) / ((p - 1) * phi ^ (1 / (p - 1)))
--     ) * exp (
--         1 / phi * (y * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p) )
--     )) y

def standardTweediePDF₂₃ := tweediePDF₂₃ (5 / 2) 1 1

example : standardTweediePDF₂₃ 1 = 𝓦 (-1 / 3) 0 (-2 / 3) * rexp (4 / 3) := by
  unfold standardTweediePDF₂₃ tweediePDF₂₃ --wright_generalized_bessel
  simp [Set.indicator]
  ring_nf


/-- The coefficient required for normalization by the positive-stable
Laplace-transform identity, where `α = (p - 2) / (p - 1)`. -/
noncomputable def tweedieNormalizedScale (p phi : ℝ) : ℝ :=
  (p - 1) ^ ((p - 2) / (p - 1)) /
    ((p - 2) * phi ^ (1 / (p - 1)))

/-- The exponential tilt rate in the density. -/
noncomputable def tweedieTiltRate (p μ phi : ℝ) : ℝ :=
  μ ^ (1 - p) / ((p - 1) * phi)

/-- The positive constant outside the exponentially tilted stable density. -/
noncomputable def tweedieTiltConstant (p μ phi : ℝ) : ℝ :=
  μ ^ (2 - p) / ((p - 2) * phi)
/-- The corrected scale exactly cancels the outer exponential constant under
Laplace transformation of the positive-stable density. -/
theorem tweedieNormalizedScale_mul_rpow_tiltRate
    (p μ phi : ℝ) (hp : 2 < p) (hμ : 0 < μ) (hphi : 0 < phi) :
    tweedieNormalizedScale p phi *
        (tweedieTiltRate p μ phi) ^ ((p - 2) / (p - 1)) =
      tweedieTiltConstant p μ phi := by
  unfold tweedieNormalizedScale tweedieTiltRate tweedieTiltConstant
  have hp1_pos : p - 1 > 0 := by linarith
  have hp2_pos : p - 2 > 0 := by linarith
  have hp1_ne : p - 1 ≠ 0 := ne_of_gt hp1_pos
  have hphi_pos : phi > 0 := hphi
  have h_exp : (1 - p) * ((p - 2) / (p - 1)) = 2 - p := by field_simp; ring
  have hmu_rpow : μ ^ (1 - p) > 0 := Real.rpow_pos_of_pos hμ _
  have hp1_phi_pos : (p - 1) * phi > 0 := mul_pos hp1_pos hphi_pos
  rw [Real.div_rpow (le_of_lt hmu_rpow) (le_of_lt hp1_phi_pos)]
  rw [← Real.rpow_mul (le_of_lt hμ)]
  rw [h_exp]
  rw [Real.mul_rpow (le_of_lt hp1_pos) (le_of_lt hphi_pos)]
  rw [div_mul_div_comm]
  have h_denom_eq : (p - 2) * phi ^ (1 / (p - 1)) * ((p - 1) ^ ((p - 2) / (p - 1))
    * phi ^ ((p - 2) / (p - 1))) =
                    (p - 1) ^ ((p - 2) / (p - 1)) * (p - 2) * phi := by
    have h1 : phi ^ (1 / (p - 1)) * phi ^ ((p - 2) / (p - 1)) = phi := by
      rw [← Real.rpow_add hphi_pos]
      have h_phi_exp : 1 / (p - 1) + (p - 2) / (p - 1) = 1 := by field_simp; linarith
      rw [h_phi_exp, Real.rpow_one]
    calc (p - 2) * phi ^ (1 / (p - 1)) * ((p - 1) ^ ((p - 2) / (p - 1)) * phi ^ ((p - 2) / (p - 1)))
        = (p - 2) * ((p - 1) ^ ((p - 2) / (p - 1)) * (phi ^ (1 / (p - 1))
          * phi ^ ((p - 2) / (p - 1)))) := by ring
      _ = (p - 2) * ((p - 1) ^ ((p - 2) / (p - 1)) * phi) := by rw [h1]
      _ = (p - 1) ^ ((p - 2) / (p - 1)) * (p - 2) * phi := by ring
  rw [h_denom_eq]
  have hdenom_ne : (p - 1) ^ ((p - 2) / (p - 1)) * (p - 2) * phi ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact ne_of_gt (Real.rpow_pos_of_pos hp1_pos _)
      · exact ne_of_gt hp2_pos
    · exact ne_of_gt hphi_pos
  have hdenom2_ne : (p - 2) * phi ≠ 0 := by
    apply mul_ne_zero (ne_of_gt hp2_pos) (ne_of_gt hphi_pos)
  rw [div_eq_div_iff hdenom_ne hdenom2_ne]
  ring

/-- Tweedie density with the corrected positive-stable scale coefficient. -/
noncomputable def tweediePDF₂₃_corrected (p μ phi : ℝ) (y : ℝ) : ℝ :=
  let α := (2 - p) / (1 - p)
  Set.indicator {y : ℝ | 0 < y} (fun y =>
    1 / y * wright_generalized_bessel (-α) 0
      (-tweedieNormalizedScale p phi * y ^ (-α)) *
    exp (1 / phi *
      (y * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)))) y

/-- The unit-scale positive-stable Laplace-transform identity.  The general
scale identity below is obtained from this by dilation. -/
lemma integral_wright_positive_stable_unit (a t : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    ∫ y in Set.Ioi (0 : ℝ),
      (1 / y) * wright_generalized_bessel (-a) 0 (-y ^ (-a)) *
        Real.exp (-t * y) =
      Real.exp (-(t ^ a)) := by
  exact WrightLaplace.integral_wright_positive_stable_unit ha0 ha1 ht

/-- Laplace-transform identity for the positive stable density represented by the
Wright function.  This is the analytic identity underlying the normalization. -/
lemma integral_wright_positive_stable (a c t : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) (ht : 0 < t) :
    ∫ y in Set.Ioi (0 : ℝ),
      (1 / y) * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) *
        Real.exp (-t * y) =
      Real.exp (-c * t ^ a) := by
  -- Use scaling substitution y = c^(1/a) * u to reduce to unit case
  have hca : c ^ (1 / a) > 0 := Real.rpow_pos_of_pos hc _
  have hca_ne : c ^ (1 / a) ≠ 0 := ne_of_gt hca
  -- After substitution y = c^(1/a) * u:
  -- - c * y^(-a) = c * c^(-1) * u^(-a) = u^(-a)
  -- - 1/y = c^(-1/a) * (1/u)
  -- - dy = c^(1/a) * du
  -- The c^(1/a) from Jacobian cancels c^(-1/a) from 1/y
  -- The exponent becomes -(t * c^(1/a)) * u
  have key : ∫ y in Set.Ioi (0 : ℝ),
      (1 / y) * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) *
        Real.exp (-t * y) =
      ∫ u in Set.Ioi (0 : ℝ),
      (1 / u) * wright_generalized_bessel (-a) 0 (-u ^ (-a)) *
        Real.exp (-(t * c ^ (1 / a)) * u) := by
    let k := c ^ (1 / a)
    have hk_pos : k > 0 := hca
    have hk_a : k ^ a = c := by
      rw [← Real.rpow_mul (le_of_lt hc), one_div_mul_cancel ha0.ne', Real.rpow_one]
    -- Define the integrands
    let f := fun y => (1 / y) * wright_generalized_bessel (-a) 0 (-c * y ^ (-a)) * Real.exp (-t * y)
    let g := fun u =>
      (1 / u) * wright_generalized_bessel (-a) 0 (-u ^ (-a)) * Real.exp (-(t * k) * u)
    -- Key relation: f(k * u) = k⁻¹ * g(u) for u > 0
    have hfkg : ∀ u > 0, f (k * u) = k⁻¹ * g u := by
      intro u hu
      simp only [f, g]
      have hk_mul_u_pos : k * u > 0 := mul_pos hk_pos hu
      rw [Real.mul_rpow (le_of_lt hk_pos) (le_of_lt hu)]
      rw [Real.rpow_neg (le_of_lt hk_pos)]
      rw [Real.rpow_neg (le_of_lt hu)]
      rw [hk_a]
      field_simp
    -- Now use the change of variables y = k * u
    -- First, work with full integrals
    have hsub := MeasureTheory.Measure.integral_comp_mul_left (fun y => f y) k
    -- hsub : ∫ x, f(k*x) = |k|⁻¹ • ∫ y, f(y)
    -- So: ∫ y, f(y) = k * ∫ x, f(k*x)  (since k > 0)
    have hk_eq : |k⁻¹| = k⁻¹ := abs_of_pos (inv_pos.mpr hk_pos)
    rw [hk_eq] at hsub
    have hsub' : ∫ y, f y = k * ∫ x, f (k * x) := by
      rw [smul_eq_mul] at hsub
      rw [hsub]
      ring_nf
      simp [hk_pos.ne']
    -- Use indicator functions and the substitution lemma
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    have hind := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun y => (Set.Ioi 0).indicator f y) (a := k)
    simp only [smul_eq_mul] at hind
    -- hind : ∫ x, (Ioi 0).indicator f (k * x) = k⁻¹ * ∫ y, (Ioi 0).indicator f y
    -- So: k * ∫ x, (Ioi 0).indicator f (k * x) = ∫ y, (Ioi 0).indicator f y
    have hind' : ∫ y, (Set.Ioi 0).indicator f y = k * ∫ x, (Set.Ioi 0).indicator f (k * x) := by
      rw [abs_of_pos (inv_pos.mpr hk_pos)] at hind
      field_simp at hind ⊢
      linarith [hind]
    rw [hind']
    -- Now show: k * ∫ x, (Ioi 0).indicator f (k * x) = ∫ x, (Ioi 0).indicator g x
    -- First, show the integrands are equal:
    -- (Ioi 0).indicator f (k * x) = k⁻¹ * (Ioi 0).indicator g x
    have hineq : ∀ x, (Set.Ioi 0).indicator (fun y => f (k * y)) x
        = k⁻¹ * (Set.Ioi 0).indicator g x := by
      intro x
      simp only [Set.indicator_apply]
      split_ifs with hx
      · exact hfkg x hx
      · ring
    have heq1 : ∀ x, (Set.Ioi 0).indicator f (k * x)
        = (Set.Ioi 0).indicator (fun y => f (k * y)) x := by
      intro x
      simp only [Set.indicator_apply]
      have hkx : k * x > 0 ↔ x > 0 := by
        constructor <;> intro h <;> nlinarith
      simp [hkx]
    simp_rw [heq1, hineq]
    rw [MeasureTheory.integral_const_mul]
    field_simp
    -- Need to show g = the RHS function
    have hg_eq_rhs : g = fun u =>
        wright_generalized_bessel (-a) 0 (-u ^ (-a)) * Real.exp (-(u * t * c ^ (1 / a))) / u := by
      ext u
      simp only [g, k]
      ring_nf
    rw [hg_eq_rhs]
  rw [key]
  rw [integral_wright_positive_stable_unit (a := a) (ha0 := ha0) (ha1 := ha1)
      (t := t * c ^ (1 / a)) (by positivity : 0 < t * c ^ (1 / a))]
  congr 1
  rw [mul_rpow (le_of_lt ht) (le_of_lt hca)]
  rw [← Real.rpow_mul (le_of_lt hc), one_div_mul_cancel ha0.ne', Real.rpow_one]
  ring


lemma for_aristotle (p μ phi : ℝ)
    (hp₂ : 2 < p) (hphi : 0 < phi) (hμ : 0 < μ) :
    ∫ y : ℝ, y * tweediePDF₂₃_corrected p μ phi y = μ := by
  sorry

/-- Surprisingly, `p < 3` is not needed here. -/
lemma tweediePDF₂₃_normalized (p μ phi : ℝ)
    (hp₂ : 2 < p) (hphi : 0 < phi) (hμ : 0 < μ) :
    ∫ y : ℝ, tweediePDF₂₃_corrected p μ phi y = 1 := by
  have hp1_neg : 1 - p < 0 := by linarith
  have hp2_neg : 2 - p < 0 := by linarith
  -- Key: α = (2-p)/(1-p) = (p-2)/(p-1), and 0 < α < 1 when 2 < p < 3
  set α := (2 - p) / (1 - p) with hα_def
  have ha0 : 0 < α := div_pos_of_neg_of_neg hp2_neg hp1_neg
  have ha1 : α < 1 := by
    rw [div_lt_one_of_neg hp1_neg]
    linarith
  -- tweedieNormalizedScale p phi > 0
  have hc_pos : tweedieNormalizedScale p phi > 0 := by
    unfold tweedieNormalizedScale
    apply div_pos
    · exact Real.rpow_pos_of_pos (by linarith : p - 1 > 0) _
    · exact mul_pos (by linarith : p - 2 > 0) (Real.rpow_pos_of_pos hphi _)
  -- Define t for the exponential
  set t := μ ^ (1 - p) / ((p - 1) * phi) with ht_def
  have ht_pos : t > 0 := by
    apply div_pos _ (mul_pos (by linarith : p - 1 > 0) hphi)
    exact Real.rpow_pos_of_pos hμ _
  -- Rewrite the integral using the indicator
  unfold tweediePDF₂₃_corrected
  simp only
  have hset : {y : ℝ | 0 < y} = Set.Ioi 0 := by ext; simp [Set.mem_Ioi]
  rw [hset, MeasureTheory.integral_indicator measurableSet_Ioi]
  -- Rewrite the exponent: 1/phi * (x * μ^(1-p) / (1-p) - μ^(2-p) / (2-p)) = -t*x + const
  have hexp_eq : ∀ x : ℝ, 1 / phi * (x * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p)) =
      -t * x + (-μ ^ (2 - p) / ((2 - p) * phi)) := by
    intro x
    rw [ht_def]
    have hp1_ne : p - 1 ≠ 0 := by linarith
    have hp2_ne : 2 - p ≠ 0 := by linarith
    have hphi_ne : phi ≠ 0 := by linarith
    have h1p : 1 - p = -(p - 1) := by ring
    rw [h1p]
    field_simp
    ring
  -- Rewrite the integral with the separated exponent
  have hexp_factor : ∀ x : ℝ,
      Real.exp (1 / phi * (x * μ ^ (1 - p) / (1 - p) - μ ^ (2 - p) / (2 - p))) =
      Real.exp (-t * x) * Real.exp (-μ ^ (2 - p) / ((2 - p) * phi)) := by
    intro x
    rw [hexp_eq x, Real.exp_add]
  -- Rewrite the integral
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [hexp_factor x])]
  -- Factor out the constant
  -- First rewrite the integrand to move the constant to the left
  have hrearrange : ∀ x : ℝ, 1 / x * wright_generalized_bessel (-α) 0
      (-tweedieNormalizedScale p phi * x ^ (-α)) *
      (Real.exp (-t * x) * Real.exp (-μ ^ (2 - p) / ((2 - p) * phi))) =
      Real.exp (-μ ^ (2 - p) / ((2 - p) * phi)) *
      (1 / x * wright_generalized_bessel (-α) 0
        (-tweedieNormalizedScale p phi * x ^ (-α)) * Real.exp (-t * x)) := by
    intro x; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => hrearrange x)]
  rw [MeasureTheory.integral_const_mul]
  -- Apply the integral_wright_positive_stable lemma
  rw [integral_wright_positive_stable α (tweedieNormalizedScale p phi) t ha0 ha1 hc_pos ht_pos]
  -- Now we need: exp(-μ^(2-p) / ((2-p)*phi)) * exp(-tweedieNormalizedScale * t^α) = 1
  rw [← Real.exp_add]
  -- Show α = (p - 2) / (p - 1)
  have hp1_ne : p - 1 ≠ 0 := by linarith
  have hp1_neg_ne : 1 - p ≠ 0 := by linarith
  have hα_eq : α = (p - 2) / (p - 1) := by
    rw [hα_def]
    have : (2 - p) / (1 - p) = (p - 2) / (p - 1) := by
      field_simp [hp1_ne, hp1_neg_ne]
      ring
    exact this
  -- Use the identity tweedieNormalizedScale * t^α = tweedieTiltConstant
  have hnors : tweedieNormalizedScale p phi * t ^ α = tweedieTiltConstant p μ phi := by
    rw [hα_eq]
    exact tweedieNormalizedScale_mul_rpow_tiltRate p μ phi hp₂ hμ hphi
  rw [neg_mul, hnors]
  -- Now: exp(-μ^(2-p) / ((2-p)*phi) + -tweedieTiltConstant) = exp(0) = 1
  have hp2_ne : p - 2 ≠ 0 := by linarith
  have h2p_ne : 2 - p ≠ 0 := by linarith
  have htconst_eq : -μ ^ (2 - p) / ((2 - p) * phi) = tweedieTiltConstant p μ phi := by
    unfold tweedieTiltConstant
    have h2p : 2 - p = -(p - 2) := by ring
    rw [h2p]
    field_simp [hp2_ne, h2p_ne]
  rw [htconst_eq]
  have : tweedieTiltConstant p μ phi + -tweedieTiltConstant p μ phi = 0 := by ring
  rw [this, Real.exp_zero]


/-- Whereas `tweediePDF₂₃_corrected` for `p=3` is the inverse Gaussian,
for `p=2` (and `p=1`) [and `p=0`] it collapses to zero rather than the gamma distribution
(and the Poisson distribution) [and the normal distribution]. -/
lemma tweedie_degenerate₂ (μ phi y : ℝ) :
    tweediePDF₂₃_corrected 2 μ phi y = 0 := by
  unfold tweediePDF₂₃_corrected wright_generalized_bessel
  simp
lemma tweedie_degenerate₁ (μ phi y : ℝ) :
    tweediePDF₂₃_corrected 1 μ phi y = 0 := by
  unfold tweediePDF₂₃_corrected wright_generalized_bessel
  simp
lemma tweedie_degenerate₀ (μ phi y : ℝ) :
    tweediePDF₂₃_corrected 0 μ phi y = 0 := by
  unfold tweediePDF₂₃_corrected wright_generalized_bessel
    tweedieNormalizedScale
  simp only [one_div, zero_sub, neg_div_neg_eq, div_one, rpow_ofNat, even_two, Even.neg_pow,
    one_pow, ne_eq, one_ne_zero, not_false_eq_true, div_neg_self, neg_mul, inv_neg, mul_inv_rev,
    neg_neg, sub_zero, rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, add_zero, rpow_one,
    indicator_apply_eq_zero, mem_ofPred_eq, mul_eq_zero, inv_eq_zero, exp_ne_zero, or_false]
  intro h
  right
  have (k : ℕ) : Gamma (-(2 * (k : ℝ))) = 0 := by
    apply (Gamma_eq_zero_iff (-(2 * ↑k))).mpr
    use 2 * k
    simp
  simp_rw [this]
  simp


namespace WrightSpecial

open Real

/-- `Γ(1/2 - n) = (-4)^n · n! · √π / (2n)!` for every natural number `n`. -/
lemma gamma_half_sub_nat (n : ℕ) :
    Real.Gamma (1 / 2 - (n : ℝ))
      = (-4) ^ n * (n).factorial * Real.sqrt Real.pi / (2 * n).factorial := by
  induction n with
  | zero =>
    rw [show (1 / 2 - ((0 : ℕ) : ℝ)) = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
    norm_num
  | succ n ih =>
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : (1 / 2 - ((n : ℝ) + 1)) ≠ 0 := by intro h; linarith
    have key : Real.Gamma ((1 / 2 - ((n : ℝ) + 1)) + 1)
        = (1 / 2 - ((n : ℝ) + 1)) * Real.Gamma (1 / 2 - ((n : ℝ) + 1)) := Real.Gamma_add_one hs
    rw [show (1 / 2 - ((n : ℝ) + 1)) + 1 = 1 / 2 - (n : ℝ) by ring] at key
    have h2 : Real.Gamma (1 / 2 - ((n : ℝ) + 1))
        = Real.Gamma (1 / 2 - (n : ℝ)) / (1 / 2 - ((n : ℝ) + 1)) := by
      rw [key, mul_div_cancel_left₀ _ hs]
    have hfac : ((2 * (n + 1)).factorial : ℝ)
        = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hfac2 : (((n + 1)).factorial : ℝ) = ((n : ℝ) + 1) * (n).factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpos : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    push_cast [hfac, hfac2]
    rw [h2, ih, div_div, div_eq_div_iff (mul_ne_zero hpos hs) (by positivity)]
    ring

/-- The even-index terms of the series vanish: `Γ` has poles at the non-positive integers,
which Mathlib's `Real.Gamma` represents by the value `0`. -/
lemma even_term_eq_zero (z : ℝ) (m : ℕ) :
    z ^ (2 * m) / ((2 * m).factorial * Real.Gamma (-(2⁻¹ * ((2 * m : ℕ) : ℝ)))) = 0 := by
  have h : (-(2⁻¹ * ((2 * m : ℕ) : ℝ))) = -(m : ℝ) := by push_cast; ring
  rw [h, Real.Gamma_neg_nat_eq_zero, mul_zero, div_zero]

/-- Closed form for the odd-index terms of the series. -/
lemma odd_term_eq (z : ℝ) (m : ℕ) :
    z ^ (2 * m + 1) / ((2 * m + 1).factorial * Real.Gamma (-(2⁻¹ * ((2 * m + 1 : ℕ) : ℝ))))
      = (-z / (2 * Real.sqrt Real.pi)) * ((-z ^ 2 / 4) ^ m / (m).factorial) := by
  have harg : (-(2⁻¹ * ((2 * m + 1 : ℕ) : ℝ))) = 1 / 2 - (((m + 1 : ℕ)) : ℝ) := by
    push_cast; ring
  rw [harg, gamma_half_sub_nat (m + 1)]
  have hpi : Real.sqrt Real.pi ≠ 0 := by
    simp [Real.sqrt_eq_zero', Real.pi_pos]
  have h4 : ((-4 : ℝ)) ^ m ≠ 0 := by positivity
  have hm : ((m).factorial : ℝ) ≠ 0 := by positivity
  have hfacA : ((2 * (m + 1)).factorial : ℝ)
      = (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 1) * (2 * m).factorial := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hfacB : (((2 * m + 1)).factorial : ℝ) = (2 * (m : ℝ) + 1) * (2 * m).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfacC : (((m + 1)).factorial : ℝ) = ((m : ℝ) + 1) * (m).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpow : ((-z ^ 2 / 4 : ℝ)) ^ m = (z ^ 2) ^ m / (-4) ^ m := by
    rw [← div_pow]; ring_nf
  have hz : z ^ (2 * m + 1) = (z ^ 2) ^ m * z := by rw [← pow_mul]; ring
  have h2m : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
  rw [hfacA, hfacB, hfacC, hpow, hz]
  field_simp
  ring

/-- The Wright function `W(-1/2, 0; z) = ∑ₖ zᵏ / (k! · Γ(-k/2))` equals
`-z/(2√π) · exp(-z²/4)`.  This holds for every real `z`; no positivity assumption is needed. -/
theorem wright_neg_half_zero (z : ℝ) :
    ∑' (k : ℕ), z ^ k / ((k).factorial * Real.Gamma (-(2⁻¹ * (k : ℝ))))
      = -z / (2 * Real.sqrt Real.pi) * Real.exp (-z ^ 2 / 4) := by
  set f : ℕ → ℝ := fun k => z ^ k / ((k).factorial * Real.Gamma (-(2⁻¹ * (k : ℝ)))) with hf
  have hEven : ∀ m : ℕ, f (2 * m) = 0 := fun m => even_term_eq_zero z m
  have hOdd : ∀ m : ℕ, f (2 * m + 1)
      = (-z / (2 * Real.sqrt Real.pi)) * ((-z ^ 2 / 4) ^ m / (m).factorial) :=
    fun m => odd_term_eq z m
  have hse : Summable (fun m : ℕ => f (2 * m)) := by
    simp only [hEven]
    exact summable_zero
  have hso : Summable (fun m : ℕ => f (2 * m + 1)) := by
    simp only [hOdd]
    exact (Real.summable_pow_div_factorial (-z ^ 2 / 4)).mul_left _
  have hsplit := tsum_even_add_odd hse hso
  rw [← hsplit]
  have h1 : ∑' (m : ℕ), f (2 * m) = 0 := by simp [hEven]
  have h2 : ∑' (m : ℕ), f (2 * m + 1)
      = (-z / (2 * Real.sqrt Real.pi)) * Real.exp (-z ^ 2 / 4) := by
    simp only [hOdd]
    rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [h1, h2, zero_add]

/-- The statement in the notation of the original question:
`∑' (k : ℕ), z ^ k / (↑k ! * Gamma (-(2⁻¹ * ↑k))) = -z / (2 * √π) * rexp (-z ^ 2 / 4)`. -/
theorem wright_neg_half_zero' (z : ℝ) :
    ∑' (k : ℕ), z ^ k / (k ! * Real.Gamma (-(2⁻¹ * (k : ℝ))))
      = -z / (2 * √π) * rexp (-z ^ 2 / 4) :=
  wright_neg_half_zero z

end WrightSpecial

lemma h𝓦 : 𝓦 (-(1 / 2)) 0 = fun z => -z / (2 * √π) * rexp (-z ^ 2 / 4) := by
  unfold wright_generalized_bessel
  ext z
  convert WrightSpecial.wright_neg_half_zero' z
  simp

/--
August 13, 2026.
-/
lemma tweedie₃_eq_inverseGaussian (y : ℝ) (hy : 0 < y) :
    tweediePDF₂₃_corrected 3 1 1 y = (inverseGaussianPDF 1 1 y).toReal := by
        unfold tweediePDF₂₃_corrected inverseGaussianPDF tweedieNormalizedScale
        simp [Set.indicator]
        ring_nf
        rw [if_pos hy]
        field_simp
        rw [max_eq_left (by positivity)]
        have : rexp ((y * (2 + -y) + -1) / (y * 2))
              = rexp ((2 + -y) / 2) * rexp (( -1) / (y * 2)) := by
          rw [← exp_add]
          field_simp
        rw [this]
        field_simp
        rw [h𝓦]
        rw [← sqrt_eq_rpow]
        apply congrArg₂
        · field_simp
          rw [sqrt_div (by simp), sqrt_mul (by positivity)]
          have : √π ≠ 0 := by
            rw [sqrt_ne_zero (by positivity)]
            simp
          field_simp
          simp only [one_div, Nat.ofNat_nonneg, sqrt_mul, sqrt_one, mul_one]
          rw [← mul_assoc, mul_comm _ (√2), ← mul_assoc]
          rw [← sqrt_mul (by positivity), sqrt_mul_self_eq_abs]
          rw [Nat.abs_ofNat, mul_assoc, sqrt_eq_rpow, ← rpow_ofNat]
          rw [← rpow_mul (le_of_lt hy), ← rpow_add hy]
          ring_nf
          simp
        field_simp
        norm_num
        rw [← rpow_two, ← rpow_mul (le_of_lt hy)]
        simp
        field_simp
        rw [rpow_neg_one]
        ring_nf
        field_simp
