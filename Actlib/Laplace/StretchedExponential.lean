import Mathlib

/-!
# A stretched-exponential integral

This file formalizes the lemma labelled `lem:stretched` and titled
**A stretched-exponential integral** in `wright_laplace.tex` ("A contour-free proof of the
unit-scale positive-stable Laplace-transform identity"):

> For every `c > 0`,
> `∫_0^∞ e^{-c v^a} dv = Γ(1 + 1/a) / c^{1/a} < ∞`.

Here `a` is the standing datum of the paper, subject to `0 < a < 1`.  The proofs below only use
`0 < a`, so the hypothesis `a < 1` is omitted from the statements.  The assertion `< ∞` of the
source is formalized as Lebesgue integrability of the integrand on `(0, ∞)`
(`WrightLaplace.integrableOn_exp_neg_mul_rpow`), and the displayed evaluation as
`WrightLaplace.integral_exp_neg_mul_rpow`.

As in the source, both are obtained from the substitution `u = c v^a`, i.e. from the
change-of-variables lemma `MeasureTheory.integral_comp_rpow_Ioi` (and its integrability
counterpart), together with the evaluation of `∫_0^∞ u^{1/a - 1} e^{-c u} du` in terms of the
Gamma function and the functional equation `(1/a) Γ(1/a) = Γ(1 + 1/a)`.
-/

namespace WrightLaplace

open MeasureTheory Set

/-- Integrability of `x ↦ x^{s-1} e^{-b x}` on `(0, ∞)`, for `b > 0` and `s > 0`: the
convergence of the Gamma integral with an arbitrary positive scale.  This is the auxiliary
integrability fact used for the lemmas `lem:stretched` ("A stretched-exponential integral")
and `lem:cgamma` ("Complex-scale Gamma integral") of `wright_laplace.tex`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x ^ (s - 1) * Real.exp (-(b * x))) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x) * x ^ (s - 1)) 0 hb).2
    (by rw [mul_zero]; exact Real.GammaIntegral_convergent hs)
  have h2 : IntegrableOn
      (fun x : ℝ => (b ^ (s - 1))⁻¹ * (Real.exp (-(b * x)) * (b * x) ^ (s - 1))) (Ioi 0) :=
    h.const_mul _
  refine h2.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [mem_Ioi] at hx
  change (b ^ (s - 1))⁻¹ * (Real.exp (-(b * x)) * (b * x) ^ (s - 1))
    = x ^ (s - 1) * Real.exp (-(b * x))
  rw [Real.mul_rpow hb.le hx.le]
  have hb' : (b : ℝ) ^ (s - 1) ≠ 0 := by positivity
  field_simp

/-- The integrand of the substituted integral in the lemma `lem:stretched`
("A stretched-exponential integral") of `wright_laplace.tex`: on `(0, ∞)` the function
`x ↦ (1/a) x^{1/a - 1} e^{-c x}` obtained from `e^{-c v^a}` by the substitution `u = c v^a`. -/
private theorem substituted_integrand {a c : ℝ} (ha : 0 < a) (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    (|1 / a| * x ^ (1 / a - 1)) • Real.exp (-(c * (x ^ (1 / a)) ^ a))
      = (1 / a) * (x ^ (1 / a - 1) * Real.exp (-(c * x))) := by
  simp only [mem_Ioi] at hx
  rw [← Real.rpow_mul hx.le, one_div_mul_cancel (ne_of_gt ha), Real.rpow_one,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / a), smul_eq_mul, mul_assoc]

/-- The finiteness assertion `< ∞` of the lemma `lem:stretched`
("A stretched-exponential integral") of `wright_laplace.tex`: for `a > 0` and `c > 0`, the
stretched exponential `v ↦ e^{-c v^a}` is Lebesgue integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun v : ℝ => Real.exp (-(c * v ^ a))) (Ioi 0) := by
  have hp : (1 / a) ≠ 0 := by positivity
  refine (integrableOn_Ioi_comp_rpow_iff (fun v : ℝ => Real.exp (-(c * v ^ a))) hp).1 ?_
  have hbase : IntegrableOn
      (fun x : ℝ => (1 / a) * (x ^ (1 / a - 1) * Real.exp (-(c * x)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi hc (by positivity : (0 : ℝ) < 1 / a)).const_mul _
  exact hbase.congr_fun (fun x hx => (substituted_integrand ha x hx).symm) measurableSet_Ioi

/-- The lemma `lem:stretched` ("A stretched-exponential integral") of `wright_laplace.tex`:
for `a > 0` and `c > 0`,
`∫_0^∞ e^{-c v^a} dv = Γ(1 + 1/a) / c^{1/a}`. -/
theorem integral_exp_neg_mul_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫ v in Ioi (0 : ℝ), Real.exp (-(c * v ^ a)) = Real.Gamma (1 + 1 / a) / c ^ (1 / a) := by
  have hp : (1 / a) ≠ 0 := by positivity
  rw [← integral_comp_rpow_Ioi (fun v : ℝ => Real.exp (-(c * v ^ a))) hp,
    setIntegral_congr_fun measurableSet_Ioi (substituted_integrand ha), integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hc,
    show (1 : ℝ) + 1 / a = 1 / a + 1 by ring, Real.Gamma_add_one hp,
    one_div c, Real.inv_rpow hc.le]
  field_simp

/-- A power times a stretched exponential is integrable on `(0,∞)`: for `a > 0`, `b > 0` and
`s > -1`, `v ↦ v^s e^{-b v^a}` is Lebesgue integrable on `(0,∞)`.  This is the integrability of
the dominating function `β` in the proof of the lemma `lem:rotation` ("Rotation invariance") of
`wright_laplace.tex`, where the source refers to
`integrableOn_rpow_mul_exp_neg_mul_rpow`; the latter Mathlib lemma requires the exponent of the
stretched exponential to be `≥ 1`, which fails for the standing datum `a ∈ (0,1)`, so the
statement is proved here by the same substitution `u = v^a` as in `lem:stretched`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_Ioi {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : -1 < s) :
    IntegrableOn (fun v : ℝ => v ^ s * Real.exp (-(b * v ^ a))) (Ioi 0) := by
  have hp : (1 / a) ≠ 0 := by positivity
  refine (integrableOn_Ioi_comp_rpow_iff (fun v : ℝ => v ^ s * Real.exp (-(b * v ^ a))) hp).1 ?_
  have hbase : IntegrableOn
      (fun x : ℝ => (1 / a) * (x ^ ((s + 1) / a - 1) * Real.exp (-(b * x)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi hb (div_pos (by linarith) ha)).const_mul _
  refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [mem_Ioi] at hx
  have hsplit : x ^ ((s + 1) / a - 1) = x ^ (1 / a - 1) * x ^ (1 / a * s) := by
    rw [← Real.rpow_add hx]
    ring_nf
  beta_reduce
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / a), smul_eq_mul,
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, one_div_mul_cancel (ne_of_gt ha), Real.rpow_one,
    hsplit]
  ring

/-- The decay `v e^{-b v^k} → 0` as `v → ∞`, for `b > 0` and `k > 0`.  This is the vanishing of
the boundary term at `+∞` in the proof of the lemma `lem:rotation` ("Rotation invariance") of
`wright_laplace.tex`. -/
theorem tendsto_mul_exp_neg_mul_rpow_atTop {b k : ℝ} (hb : 0 < b) (hk : 0 < k) :
    Filter.Tendsto (fun v : ℝ => v * Real.exp (-(b * v ^ k))) Filter.atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / k) b hb
  refine (h.comp (tendsto_rpow_atTop hk)).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with v hv
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hv.le, mul_one_div, div_self (ne_of_gt hk), Real.rpow_one]
  ring_nf

end WrightLaplace
