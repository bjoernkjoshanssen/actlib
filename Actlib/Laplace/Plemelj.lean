import Mathlib
import Actlib.Laplace.ContourIntegral

/-!
# The boundary limit (Sokhotski–Plemelj by hand)

This file formalizes the lemma labelled `lem:plemelj` and titled
**Boundary limit; Sokhotski--Plemelj by hand** in `wright_laplace.tex` ("A contour-free proof of
the unit-scale positive-stable Laplace-transform identity"):

> `lim_{ψ → 0⁺} Im D(ψ) = π e^{-t^a}`.

The proof is the one of the source.  Writing `h_ψ(v) = e^{iψ}E(ψ,v)`, so that
`D(ψ) = ∫_0^∞ h_ψ(v)/(t - v e^{iψ}) dv`, one splits `D(ψ) = A(ψ) + B(ψ) + C(ψ)` with

* `A(ψ) = ∫_0^{2t} (h_ψ(v) - h_ψ(t))/(t - v e^{iψ}) dv`,
* `B(ψ) = h_ψ(t) ∫_0^{2t} dv/(t - v e^{iψ})`,
* `C(ψ) = ∫_{2t}^∞ h_ψ(v)/(t - v e^{iψ}) dv`,

and shows that `A` and `C` converge to *real* limits (two dominated-convergence arguments, with
the constant dominating function `K` of the source for `A` and with `e^{-c₂v^a}/t` for `C`), while
`B(ψ) → iπe^{-t^a}` by the explicit computation
`∫_0^{2t} dv/(t - v e^{iψ}) = -e^{-iψ} Log(1 - 2e^{iψ}) → -1 · (-iπ)`, the limit of the principal
logarithm being taken from the lower half-plane.
-/

namespace WrightLaplace

open MeasureTheory Set Complex Filter Topology

/-- The function `h_ψ(v) = e^{iψ}E(ψ,v) = e^{iψ}exp(-v^a e^{iaψ})` of the proof of the lemma
`lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
noncomputable def hfun (a psi v : ℝ) : ℂ :=
  Complex.exp ((psi : ℂ) * Complex.I) * E a psi v

/-- The integrand of equation `eq:D` of `wright_laplace.tex` written as `h_ψ(v)/(t - v e^{iψ})`,
as in the proof of the lemma `lem:plemelj`. -/
theorem Dintegrand_eq_hfun_div (a t psi v : ℝ) :
    Dintegrand a t psi v =
      hfun a psi v / ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) := rfl

/-- The modulus `|h_ψ(v)| = e^{-v^a cos(aψ)}` of the function `h_ψ` of the proof of the lemma
`lem:plemelj` of `wright_laplace.tex`. -/
theorem norm_hfun (a psi v : ℝ) :
    ‖hfun a psi v‖ = Real.exp (-(v ^ a * Real.cos (a * psi))) := by
  rw [hfun, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_E]

/-- The mean value inequality for `exp` on the closed left half-plane, used for the uniform
difference bound `eq:diffbound` in the proof of the lemma `lem:plemelj` of
`wright_laplace.tex`: `|e^{z} - e^{w}| ≤ |z - w|` whenever `Re z ≤ 0` and `Re w ≤ 0`. -/
theorem norm_cexp_sub_cexp_le_of_re_nonpos {z w : ℂ} (hz : z.re ≤ 0) (hw : w.re ≤ 0) :
    ‖Complex.exp z - Complex.exp w‖ ≤ ‖z - w‖ := by
  have hconv : Convex ℝ {u : ℂ | u.re ≤ 0} := convex_halfSpace_re_le 0
  have hdiff : ∀ u ∈ {u : ℂ | u.re ≤ 0}, DifferentiableAt ℂ Complex.exp u :=
    fun u _ => Complex.differentiable_exp u
  have hbound : ∀ u ∈ {u : ℂ | u.re ≤ 0}, ‖deriv Complex.exp u‖ ≤ 1 := by
    intro u hu
    rw [Complex.deriv_exp, Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hu
  have := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hw hz
  simpa using this

/-- The uniform difference bound `eq:diffbound` of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`:
`|h_ψ(v) - h_ψ(t)| ≤ |v^a - t^a|`, valid whenever `cos(aψ) ≥ 0`. -/
theorem norm_hfun_sub_le {a psi v t : ℝ} (hcos : 0 ≤ Real.cos (a * psi)) (hv : 0 ≤ v)
    (ht : 0 ≤ t) : ‖hfun a psi v - hfun a psi t‖ ≤ |v ^ a - t ^ a| := by
  have hre : ∀ s : ℝ, 0 ≤ s →
      (-((s : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I)).re ≤ 0 := by
    intro s hs
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    nlinarith
  have h1 : (0 : ℝ) ≤ v ^ a := Real.rpow_nonneg hv a
  have h2 : (0 : ℝ) ≤ t ^ a := Real.rpow_nonneg ht a
  have hkey := norm_cexp_sub_cexp_le_of_re_nonpos (hre _ h1) (hre _ h2)
  have hnorm : ‖(-((v ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I))
      - (-((t ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I))‖ = |v ^ a - t ^ a| := by
    rw [show (-((v ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I))
        - (-((t ^ a : ℝ) : ℂ) * Complex.exp ((a * psi : ℝ) * Complex.I))
        = (-(((v ^ a - t ^ a : ℝ)) : ℂ)) * Complex.exp ((a * psi : ℝ) * Complex.I) by
      push_cast; ring]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_neg, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hfun, hfun, ← mul_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, E, E]
  rw [hnorm] at hkey
  exact hkey

/-- The constant `K := 2t^{a-1} + a(t/2)^{a-1}` of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
noncomputable def Kconst (a t : ℝ) : ℝ := 2 * t ^ (a - 1) + a * (t / 2) ^ (a - 1)

/-- Positivity of the constant `K` of the proof of the lemma `lem:plemelj` of
`wright_laplace.tex`. -/
theorem Kconst_pos {a t : ℝ} (ha0 : 0 < a) (ht : 0 < t) : 0 < Kconst a t := by
  have h1 : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  have h2 : (0 : ℝ) < (t / 2) ^ (a - 1) := Real.rpow_pos_of_pos (by linarith) _
  unfold Kconst; positivity

/-- The uniform quotient bound of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`:
`|v^a - t^a| ≤ K|t - v|` for `0 ≤ v ≤ 2t`, obtained from the mean value theorem for
`s ↦ s^a` when `v ≥ t/2` and from the crude bound `t^a/(t/2)` when `v < t/2`. -/
theorem abs_rpow_sub_le_Kconst_mul {a t v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hv : 0 ≤ v) (hv2 : v ≤ 2 * t) : |v ^ a - t ^ a| ≤ Kconst a t * |t - v| := by
  have h1 : (0 : ℝ) < t ^ (a - 1) := Real.rpow_pos_of_pos ht _
  have h2 : (0 : ℝ) < (t / 2) ^ (a - 1) := Real.rpow_pos_of_pos (by linarith) _
  rcases le_or_gt (t / 2) v with hcase | hcase
  · -- mean value theorem on `[t/2, 2t]`
    have hsub : ∀ x ∈ Icc (t / 2) (2 * t), HasDerivWithinAt (fun s : ℝ => s ^ a)
        (a * x ^ (a - 1)) (Icc (t / 2) (2 * t)) x := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith) hx.1)
      exact (Real.hasDerivAt_rpow_const (Or.inl hx0)).hasDerivWithinAt
    have hbound : ∀ x ∈ Icc (t / 2) (2 * t), ‖a * x ^ (a - 1)‖ ≤ a * (t / 2) ^ (a - 1) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hx.1
      have : x ^ (a - 1) ≤ (t / 2) ^ (a - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [Real.rpow_pos_of_pos hx0 (a - 1)]
    have hmem1 : v ∈ Icc (t / 2) (2 * t) := ⟨hcase, hv2⟩
    have hmem2 : t ∈ Icc (t / 2) (2 * t) := ⟨by linarith, by linarith⟩
    have := (convex_Icc (t / 2) (2 * t)).norm_image_sub_le_of_norm_hasDerivWithin_le
      hsub hbound hmem2 hmem1
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    calc |v ^ a - t ^ a| ≤ a * (t / 2) ^ (a - 1) * |v - t| := this
      _ = a * (t / 2) ^ (a - 1) * |t - v| := by rw [abs_sub_comm]
      _ ≤ Kconst a t * |t - v| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          unfold Kconst; nlinarith
  · -- crude bound
    have hva : v ^ a ≤ t ^ a := Real.rpow_le_rpow hv (by linarith) ha0.le
    have hva0 : (0 : ℝ) ≤ v ^ a := Real.rpow_nonneg hv a
    have habs : |v ^ a - t ^ a| = t ^ a - v ^ a := by rw [abs_of_nonpos (by linarith)]; ring
    have habs2 : |t - v| = t - v := abs_of_pos (by linarith)
    have hta : t ^ (a - 1) * t = t ^ a := by
      rw [Real.rpow_sub ht, Real.rpow_one]
      field_simp
    rw [habs, habs2]
    have h3 : t ^ a ≤ 2 * t ^ (a - 1) * (t - v) := by
      have hb : t / 2 ≤ t - v := by linarith
      calc t ^ a = 2 * t ^ (a - 1) * (t / 2) := by rw [← hta]; ring
        _ ≤ 2 * t ^ (a - 1) * (t - v) := by nlinarith
    have h4 : 0 ≤ a * (t / 2) ^ (a - 1) * (t - v) := by
      have : 0 < t - v := by linarith
      positivity
    unfold Kconst
    nlinarith

/-- The bound `|t - v e^{iψ}| ≥ |t - v|`, the square root of the inequality of equation
`eq:quad2` of the lemma `lem:quad` of `wright_laplace.tex`, as used in the proof of the lemma
`lem:plemelj`. -/
theorem abs_sub_le_norm_sub_mul_exp {t v : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v) (psi : ℝ) :
    |t - v| ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ := by
  have h := sq_sub_le_normSq_sub_mul_exp ht hv psi
  have hn := norm_nonneg ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))
  nlinarith [sq_abs (t - v), abs_nonneg (t - v)]

/-- The term `A(ψ) = ∫_0^{2t} (h_ψ(v) - h_ψ(t))/(t - v e^{iψ}) dv` of the proof of the lemma
`lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
noncomputable def Aterm (a t psi : ℝ) : ℂ :=
  ∫ v in Ioo 0 (2 * t), (hfun a psi v - hfun a psi t) /
    ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))

/-- The term `B(ψ) = h_ψ(t) ∫_0^{2t} dv/(t - v e^{iψ})` of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
noncomputable def Bterm (a t psi : ℝ) : ℂ :=
  hfun a psi t * ∫ v in Ioo 0 (2 * t),
    ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹

/-- The term `C(ψ) = ∫_{2t}^∞ h_ψ(v)/(t - v e^{iψ}) dv` of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
noncomputable def Cterm (a t psi : ℝ) : ℂ := ∫ v in Ioi (2 * t), Dintegrand a t psi v

/-- The uniform bound `|(h_ψ(v) - h_ψ(t))/(t - v e^{iψ})| ≤ K` on `[0,2t]` of the part (a) of the
proof of the lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of
`wright_laplace.tex`. -/
theorem norm_Aintegrand_le {a t psi v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hsin : 0 < Real.sin psi) (hcos : 0 ≤ Real.cos (a * psi)) (hv : 0 ≤ v) (hv2 : v ≤ 2 * t) :
    ‖(hfun a psi v - hfun a psi t) /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))‖ ≤ Kconst a t := by
  have hden : ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) ≠ 0 :=
    sub_mul_exp_ne_zero ht hsin v
  have hdenpos : 0 < ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hden
  rw [norm_div, div_le_iff₀ hdenpos]
  calc ‖hfun a psi v - hfun a psi t‖ ≤ |v ^ a - t ^ a| := norm_hfun_sub_le hcos hv ht.le
    _ ≤ Kconst a t * |t - v| := abs_rpow_sub_le_Kconst_mul ha0 ha1 ht hv hv2
    _ ≤ Kconst a t * ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ := by
        exact mul_le_mul_of_nonneg_left (abs_sub_le_norm_sub_mul_exp ht.le hv psi)
          (Kconst_pos ha0 ht).le

/-- Continuity in `v` of `h_ψ` on `(0,∞)`, where `h_ψ(v) = e^{iψ}E(ψ,v)` is the function of the
proof of the lemma `lem:plemelj` of `wright_laplace.tex`. -/
theorem continuousOn_hfun (a psi : ℝ) : ContinuousOn (hfun a psi) (Ioi 0) :=
  continuousOn_const.mul (continuousOn_E a psi)

/-- Continuity in `v` of `v ↦ (t - v e^{iψ})⁻¹`, used in the proof of the lemma `lem:plemelj`
of `wright_laplace.tex`. -/
theorem continuous_inv_sub_mul_exp {t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) :
    Continuous fun v : ℝ => ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun v => sub_mul_exp_ne_zero ht hsin v

/-- Integrability of the integrand of `A(ψ)` in the proof of the lemma `lem:plemelj` of
`wright_laplace.tex`, from the constant dominating function `K`. -/
theorem integrableOn_Aintegrand {a t psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hsin : 0 < Real.sin psi) (hcos : 0 ≤ Real.cos (a * psi)) :
    IntegrableOn (fun v : ℝ => (hfun a psi v - hfun a psi t) /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))) (Ioo 0 (2 * t)) := by
  have hmeas : AEStronglyMeasurable (fun v : ℝ => (hfun a psi v - hfun a psi t) /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)))
      (volume.restrict (Ioo 0 (2 * t))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.div (((continuousOn_hfun a psi).mono ?_).sub continuousOn_const)
      (Continuous.continuousOn (by fun_prop)) fun v _ => sub_mul_exp_ne_zero ht hsin v
    exact fun v hv => hv.1
  have hconst : IntegrableOn (fun _ : ℝ => Kconst a t) (Ioo 0 (2 * t)) :=
    integrableOn_const measure_Ioo_lt_top.ne
  refine Integrable.mono' hconst hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  exact norm_Aintegrand_le ha0 ha1 ht hsin hcos hv.1.le hv.2.le

/-- Integrability of the integrand of `B(ψ)` in the proof of the lemma `lem:plemelj` of
`wright_laplace.tex`. -/
theorem integrableOn_inv_sub_mul_exp {t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) :
    IntegrableOn (fun v : ℝ => ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹)
      (Ioo 0 (2 * t)) :=
  ((continuous_inv_sub_mul_exp ht hsin).continuousOn.integrableOn_Icc
    (a := 0) (b := 2 * t)).mono_set Ioo_subset_Icc_self

/-- The splitting `D(ψ) = A(ψ) + B(ψ) + C(ψ)` of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
theorem D_eq_Aterm_add_Bterm_add_Cterm {a t psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hsin : 0 < Real.sin psi) (hcos : 0 < Real.cos (a * psi)) :
    D a t psi = Aterm a t psi + Bterm a t psi + Cterm a t psi := by
  have hint : IntegrableOn (Dintegrand a t psi) (Ioi 0) :=
    integrableOn_Dintegrand' ha0 ht hsin hcos
  have hsplit : Ioc (0 : ℝ) (2 * t) ∪ Ioi (2 * t) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by linarith)
  have h1 : D a t psi = (∫ v in Ioc (0 : ℝ) (2 * t), Dintegrand a t psi v)
      + ∫ v in Ioi (2 * t), Dintegrand a t psi v := by
    rw [D, ← hsplit]
    exact setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hint.mono_set (by rw [← hsplit]; exact subset_union_left))
      (hint.mono_set (by rw [← hsplit]; exact subset_union_right))
  have h2 : (∫ v in Ioo (0 : ℝ) (2 * t), Dintegrand a t psi v)
      = Aterm a t psi + Bterm a t psi := by
    rw [Aterm, Bterm, ← integral_const_mul,
      ← integral_add (integrableOn_Aintegrand ha0 ha1 ht hsin hcos.le)
        ((integrableOn_inv_sub_mul_exp ht hsin).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
    have hden : ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) ≠ 0 :=
      sub_mul_exp_ne_zero ht hsin v
    rw [Dintegrand_eq_hfun_div]
    field_simp
    ring
  rw [h1, integral_Ioc_eq_integral_Ioo, h2, Cterm]

/-- The value `h_0(v) = e^{-v^a}` at `ψ = 0` of the function `h_ψ` of the proof of the lemma
`lem:plemelj` of `wright_laplace.tex`. -/
theorem hfun_zero (a v : ℝ) : hfun a 0 v = ((Real.exp (-(v ^ a)) : ℝ) : ℂ) := by
  simp [hfun, E, Complex.ofReal_exp]

/-- Continuity in `ψ` of `h_ψ(v)`, used for the pointwise limits in the proof of the lemma
`lem:plemelj` of `wright_laplace.tex`. -/
theorem continuous_hfun_psi (a v : ℝ) : Continuous fun psi : ℝ => hfun a psi v := by
  unfold hfun E
  fun_prop

/-- On `(0, θ]` the sine is positive, as needed throughout the proof of the lemma `lem:plemelj`
of `wright_laplace.tex`. -/
theorem sin_pos_of_mem_Ioc_theta {a psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h : psi ∈ Ioc 0 (theta a)) : 0 < Real.sin psi :=
  Real.sin_pos_of_pos_of_lt_pi h.1 (lt_of_le_of_lt h.2 (theta_lt_pi ha0 ha1))

/-- On `(0, θ]` one has `cos(aψ) ≥ c₂ > 0`, as recorded in the proof of the lemma `lem:plemelj`
of `wright_laplace.tex`. -/
theorem cos_mul_pos_of_mem_Ioc_theta {a psi : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h : psi ∈ Ioc 0 (theta a)) : 0 < Real.cos (a * psi) :=
  lt_of_lt_of_le (c₂_pos ha0 ha1) (c₂_le_cos ha0 ha1 h.1.le h.2)

/-- The set `(0, θ]` is a neighbourhood of `0` within `(0,∞)`; the limits `ψ → 0⁺` of the proof
of the lemma `lem:plemelj` of `wright_laplace.tex` are all taken there. -/
theorem eventually_mem_Ioc_theta {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ psi in 𝓝[>] (0 : ℝ), psi ∈ Ioc 0 (theta a) :=
  Ioc_mem_nhdsGT (theta_pos ha0 ha1)

/-- The limit `(e^{-v^a} - e^{-t^a})/(t - v)` of the integrand of `A(ψ)` as `ψ → 0⁺`, in part (a)
of the proof of the lemma `lem:plemelj` of `wright_laplace.tex`. -/
noncomputable def Alimit (a t v : ℝ) : ℝ :=
  (Real.exp (-(v ^ a)) - Real.exp (-(t ^ a))) / (t - v)

/-- The pointwise convergence of the integrand of `A(ψ)` in part (a) of the proof of the lemma
`lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
theorem tendsto_Aintegrand {a t : ℝ} (v : ℝ) :
    Tendsto (fun psi : ℝ => (hfun a psi v - hfun a psi t) /
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))) (𝓝[>] (0 : ℝ))
      (𝓝 ((Alimit a t v : ℝ) : ℂ)) := by
  rcases eq_or_ne v t with rfl | hvt
  · have h0 : ((Alimit a v v : ℝ) : ℂ) = 0 := by simp [Alimit]
    rw [h0]
    simp
  · have hden : ((t : ℂ) - (v : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
      exact fun h => hvt (by exact_mod_cast (sub_eq_zero.mp h).symm)
    have hcont : ContinuousAt (fun psi : ℝ => (hfun a psi v - hfun a psi t) /
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))) 0 := by
      exact (((continuous_hfun_psi a v).sub (continuous_hfun_psi a t)).continuousAt).div
        (Continuous.continuousAt (by fun_prop)) hden
    have hval : (hfun a 0 v - hfun a 0 t) /
        ((t : ℂ) - (v : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))
        = ((Alimit a t v : ℝ) : ℂ) := by
      rw [hfun_zero, hfun_zero, Alimit]
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
      push_cast
      ring
    rw [← hval]
    exact hcont.continuousWithinAt.tendsto

/-- Part (a) of the proof of the lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by
hand") of `wright_laplace.tex`: `A(ψ)` converges, as `ψ → 0⁺`, to the *real* number
`∫_0^{2t} (e^{-v^a} - e^{-t^a})/(t - v) dv`. -/
theorem tendsto_Aterm {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    Tendsto (fun psi : ℝ => Aterm a t psi) (𝓝[>] (0 : ℝ))
      (𝓝 (((∫ v in Ioo 0 (2 * t), Alimit a t v : ℝ) : ℂ))) := by
  have hmem := eventually_mem_Ioc_theta ha0 ha1
  have hmeas : ∀ᶠ psi in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun v : ℝ => (hfun a psi v - hfun a psi t) /
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)))
      (volume.restrict (Ioo 0 (2 * t))) := by
    filter_upwards [hmem] with psi hpsi
    exact (integrableOn_Aintegrand ha0 ha1 ht (sin_pos_of_mem_Ioc_theta ha0 ha1 hpsi)
      (cos_mul_pos_of_mem_Ioc_theta ha0 ha1 hpsi).le).aestronglyMeasurable
  have hbound : ∀ᶠ psi in 𝓝[>] (0 : ℝ), ∀ᵐ v ∂(volume.restrict (Ioo 0 (2 * t))),
      ‖(hfun a psi v - hfun a psi t) /
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))‖ ≤ Kconst a t := by
    filter_upwards [hmem] with psi hpsi
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact norm_Aintegrand_le ha0 ha1 ht (sin_pos_of_mem_Ioc_theta ha0 ha1 hpsi)
      (cos_mul_pos_of_mem_Ioc_theta ha0 ha1 hpsi).le hv.1.le hv.2.le
  have hlim : ∀ᵐ v ∂(volume.restrict (Ioo 0 (2 * t))),
      Tendsto (fun psi : ℝ => (hfun a psi v - hfun a psi t) /
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))) (𝓝[>] (0 : ℝ))
        (𝓝 ((Alimit a t v : ℝ) : ℂ)) :=
    Filter.Eventually.of_forall fun v => tendsto_Aintegrand v
  have := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => Kconst a t) hmeas hbound
    (integrableOn_const measure_Ioo_lt_top.ne) hlim
  rw [integral_complex_ofReal] at this
  exact this

/-- The limit `e^{-v^a}/(t - v)` of the integrand of `C(ψ)` as `ψ → 0⁺`, in part (c) of the proof
of the lemma `lem:plemelj` of `wright_laplace.tex`. -/
noncomputable def Climit (a t v : ℝ) : ℝ := Real.exp (-(v ^ a)) / (t - v)

/-- The domination of part (c) of the proof of the lemma `lem:plemelj` of `wright_laplace.tex`:
for `v ≥ 2t` one has `|t - v e^{iψ}| ≥ v - t ≥ t`, hence
`|h_ψ(v)/(t - v e^{iψ})| ≤ e^{-c₂v^a}/t`. -/
theorem norm_Dintegrand_le_of_two_mul_le {a t psi v : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hcos : c₂ a ≤ Real.cos (a * psi)) (hv : 2 * t ≤ v) :
    ‖Dintegrand a t psi v‖ ≤ Real.exp (-(c₂ a * v ^ a)) / t := by
  have hv0 : (0 : ℝ) ≤ v := by linarith
  have hden : t ≤ ‖(t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ := by
    have h := abs_sub_le_norm_sub_mul_exp ht.le hv0 psi
    have : t ≤ |t - v| := by rw [abs_of_nonpos (by linarith)]; linarith
    linarith
  have hnum : Real.exp (-(v ^ a * Real.cos (a * psi))) ≤ Real.exp (-(c₂ a * v ^ a)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.rpow_nonneg hv0 a]
  rw [norm_Dintegrand]
  gcongr

/-- The pointwise convergence of the integrand of `C(ψ)` in part (c) of the proof of the lemma
`lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`. -/
theorem tendsto_Cintegrand {a t v : ℝ} (ht : 0 < t) (hv : 2 * t < v) :
    Tendsto (fun psi : ℝ => Dintegrand a t psi v) (𝓝[>] (0 : ℝ))
      (𝓝 ((Climit a t v : ℝ) : ℂ)) := by
  have hden : ((t : ℂ) - (v : ℂ) * Complex.exp (((0 : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    intro h
    have : (t : ℝ) = v := by exact_mod_cast (sub_eq_zero.mp h)
    linarith
  have hcont : ContinuousAt (fun psi : ℝ => Dintegrand a t psi v) 0 := by
    simp only [Dintegrand_eq_hfun_div]
    exact ContinuousAt.div ((continuous_hfun_psi a v).continuousAt)
      (Continuous.continuousAt (by fun_prop)) hden
  have hval : Dintegrand a t 0 v = ((Climit a t v : ℝ) : ℂ) := by
    rw [Dintegrand_eq_hfun_div, hfun_zero, Climit]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    push_cast
    ring
  rw [← hval]
  exact hcont.continuousWithinAt.tendsto

/-- Part (c) of the proof of the lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by
hand") of `wright_laplace.tex`: `C(ψ)` converges, as `ψ → 0⁺`, to the *real* number
`∫_{2t}^∞ e^{-v^a}/(t - v) dv`. -/
theorem tendsto_Cterm {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    Tendsto (fun psi : ℝ => Cterm a t psi) (𝓝[>] (0 : ℝ))
      (𝓝 (((∫ v in Ioi (2 * t), Climit a t v : ℝ) : ℂ))) := by
  have hmem := eventually_mem_Ioc_theta ha0 ha1
  have hbdint : IntegrableOn (fun v : ℝ => Real.exp (-(c₂ a * v ^ a)) / t) (Ioi (2 * t)) :=
    IntegrableOn.mono_set ((integrableOn_exp_neg_mul_rpow ha0 (c₂_pos ha0 ha1)).div_const t)
      (Ioi_subset_Ioi (by linarith))
  have hmeas : ∀ᶠ psi in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (Dintegrand a t psi)
      (volume.restrict (Ioi (2 * t))) := by
    filter_upwards [hmem] with psi hpsi
    exact (IntegrableOn.mono_set (integrableOn_Dintegrand' ha0 ht
      (sin_pos_of_mem_Ioc_theta ha0 ha1 hpsi) (cos_mul_pos_of_mem_Ioc_theta ha0 ha1 hpsi))
      (Ioi_subset_Ioi (by linarith))).aestronglyMeasurable
  have hbound : ∀ᶠ psi in 𝓝[>] (0 : ℝ), ∀ᵐ v ∂(volume.restrict (Ioi (2 * t))),
      ‖Dintegrand a t psi v‖ ≤ Real.exp (-(c₂ a * v ^ a)) / t := by
    filter_upwards [hmem] with psi hpsi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact norm_Dintegrand_le_of_two_mul_le ha0 ha1 ht (c₂_le_cos ha0 ha1 hpsi.1.le hpsi.2)
      (le_of_lt hv)
  have hlim : ∀ᵐ v ∂(volume.restrict (Ioi (2 * t))),
      Tendsto (fun psi : ℝ => Dintegrand a t psi v) (𝓝[>] (0 : ℝ))
        (𝓝 ((Climit a t v : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact tendsto_Cintegrand ht hv
  have := tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => Real.exp (-(c₂ a * v ^ a)) / t) hmeas hbound hbdint hlim
  rw [integral_complex_ofReal] at this
  exact this

/-- Membership of `t - v e^{iψ}` in the domain of the principal logarithm, as observed in part
(b) of the proof of the lemma `lem:plemelj` of `wright_laplace.tex`: for `v ≥ 0` the imaginary
part `-v sin ψ` is `≤ 0`, and vanishes only at `v = 0`, where the point is `t > 0`. -/
theorem mem_slitPlane_sub_mul_exp {t psi v : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi)
    (hv : 0 ≤ v) : ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) ∈ slitPlane := by
  rcases eq_or_lt_of_le hv with rfl | hv'
  · left
    simpa using ht
  · right
    have him : ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)).im
        = -(v * Real.sin psi) := by
      simp [Complex.exp_ofReal_mul_I_im]
    rw [him]
    have : 0 < v * Real.sin psi := mul_pos hv' hsin
    linarith

/-- The primitive `v ↦ -e^{-iψ} Log(t - v e^{iψ})` used in part (b) of the proof of the lemma
`lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`:
its derivative is `1/(t - v e^{iψ})`. -/
theorem hasDerivAt_primitive {t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) {v : ℝ}
    (hv : 0 ≤ v) :
    HasDerivAt (fun w : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I) *
        Complex.log ((t : ℂ) - (w : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)))
      (((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹) v := by
  have hg : HasDerivAt (fun w : ℝ => (t : ℂ) - (w : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))
      (-Complex.exp ((psi : ℂ) * Complex.I)) v := by
    have h1 : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.mul_const (Complex.exp ((psi : ℂ) * Complex.I))).const_sub (t : ℂ)
  have hlog := HasDerivAt.scomp v
    (Complex.hasDerivAt_log (mem_slitPlane_sub_mul_exp ht hsin hv)) hg
  have hfin := hlog.const_mul (-Complex.exp (-(psi : ℂ) * Complex.I))
  have hone : Complex.exp (-(psi : ℂ) * Complex.I) * Complex.exp ((psi : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show -(psi : ℂ) * Complex.I + (psi : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  refine hfin.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [show (-Complex.exp (-(psi : ℂ) * Complex.I)) * (-Complex.exp ((psi : ℂ) * Complex.I) *
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹)
      = (Complex.exp (-(psi : ℂ) * Complex.I) * Complex.exp ((psi : ℂ) * Complex.I)) *
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹ from by ring, hone, one_mul]

/-- The explicit evaluation of the integral of part (b) of the proof of the lemma `lem:plemelj`
("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`:
`∫_0^{2t} dv/(t - v e^{iψ}) = -e^{-iψ} Log(1 - 2e^{iψ})`. -/
theorem integral_inv_sub_mul_exp {t psi : ℝ} (ht : 0 < t) (hsin : 0 < Real.sin psi) :
    (∫ v in Ioo (0 : ℝ) (2 * t),
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹)
      = -Complex.exp (-(psi : ℂ) * Complex.I) *
          Complex.log (1 - 2 * Complex.exp ((psi : ℂ) * Complex.I)) := by
  have hne : (1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h2 : (2 : ℂ) * Complex.exp ((psi : ℂ) * Complex.I) = 1 := by
      linear_combination -h
    have hnorm : ‖(2 : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)‖ = ‖(1 : ℂ)‖ := by rw [h2]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I] at hnorm
    norm_num at hnorm
  have hFTC : (∫ v in (0 : ℝ)..(2 * t),
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹)
      = (-Complex.exp (-(psi : ℂ) * Complex.I) *
          Complex.log ((t : ℂ) - ((2 * t : ℝ) : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)))
        - (-Complex.exp (-(psi : ℂ) * Complex.I) *
          Complex.log ((t : ℂ) - ((0 : ℝ) : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun w : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I) *
        Complex.log ((t : ℂ) - (w : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)))
      (fun v hv => ?_) ?_
    · rw [uIcc_of_le (by linarith)] at hv
      exact hasDerivAt_primitive ht hsin hv.1
    · exact (continuous_inv_sub_mul_exp ht hsin).intervalIntegrable _ _
  rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 2 * t),
    integral_Ioc_eq_integral_Ioo] at hFTC
  rw [hFTC]
  have h2t : ((t : ℂ) - ((2 * t : ℝ) : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))
      = (t : ℂ) * (1 - 2 * Complex.exp ((psi : ℂ) * Complex.I)) := by
    push_cast; ring
  have h0 : ((t : ℂ) - ((0 : ℝ) : ℂ) * Complex.exp ((psi : ℂ) * Complex.I)) = (t : ℂ) := by
    simp
  rw [h2t, h0, Complex.log_ofReal_mul ht hne, ← Complex.ofReal_log ht.le]
  ring

/-- The one-sided limit `Log(1 - 2e^{iψ}) → -iπ` as `ψ → 0⁺`, computed in part (b) of the proof of
the lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of `wright_laplace.tex`.
The limit is genuinely one-sided: the path approaches `-1` from the lower half-plane, where the
principal logarithm has boundary value `-iπ`. -/
theorem tendsto_log_one_sub_two_mul_exp :
    Tendsto (fun psi : ℝ => Complex.log (1 - 2 * Complex.exp ((psi : ℂ) * Complex.I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have hpath : Tendsto (fun psi : ℝ => (1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝[{z : ℂ | z.im < 0}] (-1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun psi : ℝ => (1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I) := by
        fun_prop
      have h2 : Tendsto (fun psi : ℝ => (1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I))
          (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℂ) - 2 * Complex.exp (((0 : ℝ) : ℂ) * Complex.I))) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have h3 : (1 : ℂ) - 2 * Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = -1 := by norm_num
      rwa [h3] at h2
    · filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with psi hpsi
      have him : ((1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I)).im
          = -(2 * Real.sin psi) := by
        simp [Complex.exp_ofReal_mul_I_im]
      have : 0 < Real.sin psi := Real.sin_pos_of_pos_of_lt_pi hpsi.1 hpsi.2
      change ((1 : ℂ) - 2 * Complex.exp ((psi : ℂ) * Complex.I)).im < 0
      rw [him]
      linarith
  have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)
  have := hlog.comp hpath
  simpa [Function.comp_def, Complex.log_neg_one] using this

/-- Part (b) of the proof of the lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by
hand") of `wright_laplace.tex`: `B(ψ) → iπe^{-t^a}` as `ψ → 0⁺`. -/
theorem tendsto_Bterm {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    Tendsto (fun psi : ℝ => Bterm a t psi) (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.exp (-(t ^ a)) : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by
  have hJ : Tendsto (fun psi : ℝ => ∫ v in Ioo (0 : ℝ) (2 * t),
      ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹) (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
    have hcong : ∀ᶠ psi : ℝ in 𝓝[>] (0 : ℝ), (∫ v in Ioo (0 : ℝ) (2 * t),
        ((t : ℂ) - (v : ℂ) * Complex.exp ((psi : ℂ) * Complex.I))⁻¹)
        = -Complex.exp (-(psi : ℂ) * Complex.I) *
            Complex.log (1 - 2 * Complex.exp ((psi : ℂ) * Complex.I)) := by
      filter_upwards [eventually_mem_Ioc_theta ha0 ha1] with psi hpsi
      exact integral_inv_sub_mul_exp ht (sin_pos_of_mem_Ioc_theta ha0 ha1 hpsi)
    have hexp : Tendsto (fun psi : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
      have hc : Continuous fun psi : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I) := by fun_prop
      have h2 : Tendsto (fun psi : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I))
          (𝓝[>] (0 : ℝ)) (𝓝 (-Complex.exp (-((0 : ℝ) : ℂ) * Complex.I))) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h2
    have hmain : Tendsto (fun psi : ℝ => -Complex.exp (-(psi : ℂ) * Complex.I) *
        Complex.log (1 - 2 * Complex.exp ((psi : ℂ) * Complex.I))) (𝓝[>] (0 : ℝ))
        (𝓝 ((Real.pi : ℂ) * Complex.I)) := by
      have hmul := hexp.mul tendsto_log_one_sub_two_mul_exp
      convert hmul using 2
      ring
    exact Tendsto.congr' (by filter_upwards [hcong] with psi h using h.symm) hmain
  have hh : Tendsto (fun psi : ℝ => hfun a psi t) (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.exp (-(t ^ a)) : ℝ) : ℂ))) := by
    have h2 : Tendsto (fun psi : ℝ => hfun a psi t) (𝓝[>] (0 : ℝ)) (𝓝 (hfun a 0 t)) :=
      ((continuous_hfun_psi a t).tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [hfun_zero] at h2
  exact hh.mul hJ

/-- The lemma `lem:plemelj` ("Boundary limit; Sokhotski--Plemelj by hand") of
`wright_laplace.tex`: for `0 < a < 1` and `t > 0`,
`lim_{ψ → 0⁺} Im D(ψ) = π e^{-t^a}`. -/
theorem tendsto_im_D {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    Tendsto (fun psi : ℝ => (D a t psi).im) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi * Real.exp (-(t ^ a)))) := by
  set L : ℂ := ((∫ v in Ioo 0 (2 * t), Alimit a t v : ℝ) : ℂ)
    + ((Real.exp (-(t ^ a)) : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)
    + ((∫ v in Ioi (2 * t), Climit a t v : ℝ) : ℂ) with hL
  have hsum : Tendsto (fun psi : ℝ => Aterm a t psi + Bterm a t psi + Cterm a t psi)
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    ((tendsto_Aterm ha0 ha1 ht).add (tendsto_Bterm ha0 ha1 ht)).add (tendsto_Cterm ha0 ha1 ht)
  have hD : Tendsto (fun psi : ℝ => D a t psi) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    refine Tendsto.congr' ?_ hsum
    filter_upwards [eventually_mem_Ioc_theta ha0 ha1] with psi hpsi
    exact (D_eq_Aterm_add_Bterm_add_Cterm ha0 ha1 ht (sin_pos_of_mem_Ioc_theta ha0 ha1 hpsi)
      (cos_mul_pos_of_mem_Ioc_theta ha0 ha1 hpsi)).symm
  have him : L.im = Real.pi * Real.exp (-(t ^ a)) := by
    have hkey : ((Real.exp (-(t ^ a)) : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)
        = ((Real.exp (-(t ^ a)) * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hL, hkey, Complex.add_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [← him]
  exact (Complex.continuous_im.tendsto L).comp hD

end WrightLaplace
