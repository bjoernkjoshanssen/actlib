import Mathlib

/-!
# The log-convexity bound

This file formalizes the lemma labelled `lem:gammabound` and titled **Log-convexity bound**
in `wright_laplace.tex` ("A contour-free proof of the unit-scale positive-stable
Laplace-transform identity"):

> For every `k ∈ ℕ`, `Γ(a k + 1) ≤ (k!)^a`.  Consequently, for every `x ≥ 0`,
> `∑_{k=0}^{∞} Γ(a k + 1)/k! · x^k ≤ ∑_{k=0}^{∞} x^k/(k!)^{1-a} < ∞`  (equation `eq:entire`).

Here `a` is the standing datum of the paper, a real number with `0 < a < 1`.
-/

namespace WrightLaplace

open Real Filter

/-- **Log-convexity bound**, first claim of the lemma `lem:gammabound`
("Log-convexity bound") in `wright_laplace.tex`.

For the standing datum `a ∈ (0,1)` and every `k ∈ ℕ` one has `Γ(a k + 1) ≤ (k!)^a`.

This is the inequality obtained in the source by writing `a k + 1 = (1-a)·1 + a·(k+1)` as a
convex combination and applying log-convexity of `Γ` on `(0, ∞)`. -/
theorem Gamma_mul_natCast_add_one_le_factorial_rpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℕ) :
    Real.Gamma (a * k + 1) ≤ (k.factorial : ℝ) ^ a := by
  have hb : 0 < 1 - a := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := (k : ℝ) + 1) (t := 1)
    (a := a) (b := 1 - a) hk1 one_pos ha0 hb (by ring)
  have harg : a * ((k : ℝ) + 1) + (1 - a) * 1 = a * k + 1 := by ring
  rw [harg, Real.Gamma_one, Real.one_rpow, mul_one] at h
  have hfac : Real.Gamma ((k : ℝ) + 1) = (k.factorial : ℝ) := by
    simpa using Real.Gamma_nat_eq_factorial k
  rwa [hfac] at h

/-- Convergence of the majorant series appearing in equation `eq:entire` of the lemma
`lem:gammabound` ("Log-convexity bound") in `wright_laplace.tex`: for `a < 1` and any real `x`,
the series `∑_k x^k/(k!)^{1-a}` converges.  As in the source, this is the ratio test: the
ratio of consecutive terms is `x/(k+1)^{1-a} → 0` because `1 - a > 0`. -/
theorem summable_pow_div_factorial_rpow {a : ℝ} (ha1 : a < 1) (x : ℝ) :
    Summable fun k : ℕ => x ^ k / (k.factorial : ℝ) ^ (1 - a) := by
  set b : ℝ := 1 - a with hb_def
  have hb : 0 < b := by rw [hb_def]; linarith
  have hfacpos : ∀ m : ℕ, (0 : ℝ) < (m.factorial : ℝ) := fun m => by
    exact_mod_cast m.factorial_pos
  have habs : ∀ m : ℕ, ‖x ^ m / (m.factorial : ℝ) ^ b‖ = |x| ^ m / (m.factorial : ℝ) ^ b := by
    intro m
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (Real.rpow_pos_of_pos (hfacpos m) b)]
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 * |x|) ^ (1 / b))
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the key numeric estimate `|x| ≤ (1/2) * (n+1)^b`
  have hkey : |x| ≤ 1 / 2 * ((n : ℝ) + 1) ^ b := by
    rcases eq_or_lt_of_le (abs_nonneg x) with h | h
    · rw [← h]; positivity
    · have hpos : (0 : ℝ) < 2 * |x| := by linarith
      have h1 : (2 * |x|) ^ (1 / b) ≤ (n : ℝ) + 1 := by
        have hNn : ((N : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have h2 : ((2 * |x|) ^ (1 / b)) ^ b ≤ ((n : ℝ) + 1) ^ b :=
        Real.rpow_le_rpow (Real.rpow_nonneg hpos.le _) h1 hb.le
      rw [← Real.rpow_mul hpos.le, one_div_mul_cancel hb.ne', Real.rpow_one] at h2
      linarith
  have hfacsucc : ((n + 1).factorial : ℝ) ^ b = ((n : ℝ) + 1) ^ b * (n.factorial : ℝ) ^ b := by
    have : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this, Real.mul_rpow hn1.le (hfacpos n).le]
  rw [habs, habs, hfacsucc]
  have hp1 : (0 : ℝ) < ((n : ℝ) + 1) ^ b := Real.rpow_pos_of_pos hn1 b
  have hp2 : (0 : ℝ) < (n.factorial : ℝ) ^ b := Real.rpow_pos_of_pos (hfacpos n) b
  have hsplit : |x| ^ (n + 1) / (((n : ℝ) + 1) ^ b * (n.factorial : ℝ) ^ b)
      = |x| / ((n : ℝ) + 1) ^ b * (|x| ^ n / (n.factorial : ℝ) ^ b) := by
    rw [pow_succ]
    field_simp
  rw [hsplit]
  have hratio : |x| / ((n : ℝ) + 1) ^ b ≤ 1 / 2 := by
    rw [div_le_iff₀ hp1]
    linarith
  have hnn : (0 : ℝ) ≤ |x| ^ n / (n.factorial : ℝ) ^ b := by positivity
  exact mul_le_mul_of_nonneg_right hratio hnn

/-- Termwise form of the comparison in equation `eq:entire` of the lemma `lem:gammabound`
("Log-convexity bound") in `wright_laplace.tex`: for `x ≥ 0` and every `k`,
`Γ(a k + 1)/k! · x^k ≤ x^k/(k!)^{1-a}`. -/
theorem gamma_div_factorial_mul_pow_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ} (hx : 0 ≤ x)
    (k : ℕ) :
    Real.Gamma (a * k + 1) / (k.factorial : ℝ) * x ^ k ≤ x ^ k / (k.factorial : ℝ) ^ (1 - a) := by
  have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hbound := Gamma_mul_natCast_add_one_le_factorial_rpow ha0 ha1 k
  have hrhs : x ^ k / (k.factorial : ℝ) ^ (1 - a)
      = (k.factorial : ℝ) ^ a / (k.factorial : ℝ) * x ^ k := by
    rw [Real.rpow_sub hF, Real.rpow_one, div_div_eq_mul_div]
    ring
  rw [hrhs]
  have hxk : (0 : ℝ) ≤ x ^ k := pow_nonneg hx k
  gcongr

/-- Summability of the left-hand series in equation `eq:entire` of the lemma `lem:gammabound`
("Log-convexity bound") in `wright_laplace.tex`: for the standing datum `a ∈ (0,1)` and every
`x ≥ 0`, the series `∑_k Γ(a k + 1)/k! · x^k` converges. -/
theorem summable_gamma_div_factorial_mul_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ}
    (hx : 0 ≤ x) :
    Summable fun k : ℕ => Real.Gamma (a * k + 1) / (k.factorial : ℝ) * x ^ k := by
  refine Summable.of_nonneg_of_le (fun k => ?_)
    (fun k => gamma_div_factorial_mul_pow_le ha0 ha1 hx k)
    (summable_pow_div_factorial_rpow ha1 x)
  have hF : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hG : (0 : ℝ) < Real.Gamma (a * k + 1) := by
    refine Real.Gamma_pos_of_pos ?_
    have : (0 : ℝ) ≤ a * k := by positivity
    linarith
  have hxk : (0 : ℝ) ≤ x ^ k := pow_nonneg hx k
  positivity

/-- **Equation `eq:entire`** of the lemma `lem:gammabound` ("Log-convexity bound") in
`wright_laplace.tex`: for the standing datum `a ∈ (0,1)` and every `x ≥ 0`,
`∑_{k=0}^{∞} Γ(a k + 1)/k! · x^k ≤ ∑_{k=0}^{∞} x^k/(k!)^{1-a} < ∞`, both series being
convergent. -/
theorem tsum_gamma_div_factorial_mul_pow_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ}
    (hx : 0 ≤ x) :
    (∑' k : ℕ, Real.Gamma (a * k + 1) / (k.factorial : ℝ) * x ^ k)
      ≤ ∑' k : ℕ, x ^ k / (k.factorial : ℝ) ^ (1 - a) :=
  (summable_gamma_div_factorial_mul_pow ha0 ha1 hx).tsum_le_tsum
    (fun k => gamma_div_factorial_mul_pow_le ha0 ha1 hx k)
    (summable_pow_div_factorial_rpow ha1 x)

end WrightLaplace
