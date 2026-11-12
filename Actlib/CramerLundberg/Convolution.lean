import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential convolution on the nonnegative half-line

The weighted-primitive representation makes the derivative of this convolution
an application of the fundamental theorem of calculus.
-/

open MeasureTheory Real Set Filter
open scoped Topology

namespace CramerLundberg

/-- Convolution with an exponential kernel, written as a weighted primitive. -/
noncomputable def expConvolution (β : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (-β * u) * ∫ y in (0 : ℝ)..u, Real.exp (β * y) * φ y

@[simp] theorem expConvolution_zero (β : ℝ) (φ : ℝ → ℝ) :
    expConvolution β φ 0 = 0 := by
  simp [expConvolution]

theorem continuous_expConvolution (β : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Continuous (expConvolution β φ) := by
  have hF : Continuous (fun y : ℝ => Real.exp (β * y) * φ y) := by fun_prop
  exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-β * u))).mul
    (intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 0)

/-- Local integrability of the weighted input is enough for continuity of the
exponential convolution; no continuity of the input is required. -/
theorem continuousOn_expConvolution_of_intervalIntegrable (β : ℝ) (φ : ℝ → ℝ)
    (hint : ∀ R ≥ 0,
      IntervalIntegrable (fun y => Real.exp (β * y) * φ y) volume 0 R) :
    ContinuousOn (expConvolution β φ) (Ici 0) := by
  intro u hu
  have hR : 0 ≤ u + 1 := add_nonneg hu zero_le_one
  have hp : ContinuousWithinAt
      (fun v => ∫ y in (0 : ℝ)..v, Real.exp (β * y) * φ y) (Icc 0 (u + 1)) u := by
    apply intervalIntegral.continuousWithinAt_primitive (measure_singleton u)
    simpa only [min_self, max_eq_right hR] using hint (u + 1) hR
  have hn : Icc (0 : ℝ) (u + 1) ∈ nhdsWithin u (Ici 0) := by
    simpa only [Ici_inter_Iic] using
      inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iic_mem_nhds (lt_add_one u))
  have he : ContinuousWithinAt (fun v : ℝ => Real.exp (-β * v)) (Ici 0) u := by
    fun_prop
  exact he.mul (hp.mono_of_mem_nhdsWithin hn)

theorem hasDerivAt_expConvolution (β : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (u : ℝ) :
    HasDerivAt (expConvolution β φ) (φ u - β * expConvolution β φ u) u := by
  have hF : Continuous (fun y : ℝ => Real.exp (β * y) * φ y) := by fun_prop
  have he : HasDerivAt (fun x : ℝ => Real.exp (-β * x))
      (-β * Real.exp (-β * u)) u := by
    simpa only [id_eq, mul_one, mul_comm] using
      ((hasDerivAt_id u).const_mul (-β)).exp
  have hi := (hF.integral_hasStrictDerivAt (0 : ℝ) u).hasDerivAt
  have hexp : Real.exp (-β * u) * Real.exp (β * u) = 1 := by
    rw [← Real.exp_add]
    simp
  refine (he.mul hi).congr_deriv ?_
  unfold expConvolution
  rw [← mul_assoc (Real.exp (-β * u)) (Real.exp (β * u)) (φ u), hexp, one_mul]
  ring

theorem expConvolution_eq_intervalIntegral (β : ℝ) (φ : ℝ → ℝ) (u : ℝ) :
    expConvolution β φ u =
      ∫ x in (0 : ℝ)..u, φ (u - x) * Real.exp (-β * x) := by
  unfold expConvolution
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ y in (0 : ℝ)..u, Real.exp (-β * u) * (Real.exp (β * y) * φ y)) =
        ∫ y in (0 : ℝ)..u,
          (fun x => φ (u - x) * Real.exp (-β * x)) (u - y) := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp
      rw [sub_sub_cancel, ← mul_assoc, ← Real.exp_add]
      rw [mul_comm]
      congr 2
      ring
    _ = ∫ x in (0 : ℝ)..u, φ (u - x) * Real.exp (-β * x) := by
      simpa using intervalIntegral.integral_comp_sub_left
        (fun x => φ (u - x) * Real.exp (-β * x)) (a := 0) (b := u) u

theorem expConvolution_eq_setIntegral (β : ℝ) (φ : ℝ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    expConvolution β φ u =
      ∫ x in Set.Icc 0 u, φ (u - x) * Real.exp (-β * x) := by
  rw [expConvolution_eq_intervalIntegral, intervalIntegral.integral_of_le hu,
    integral_Icc_eq_integral_Ioc]

theorem expConvolution_congr (β : ℝ) {φ ψ : ℝ → ℝ}
    (h : Set.EqOn φ ψ (Ici 0)) {u : ℝ} (hu : 0 ≤ u) :
    expConvolution β φ u = expConvolution β ψ u := by
  unfold expConvolution
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hu] at hy
  change Real.exp (β * y) * φ y = Real.exp (β * y) * ψ y
  rw [h hy.1]

/-- Exponential convolution preserves a limit at infinity, with the mass `1 / β`
of the exponential kernel as its normalization. -/
theorem tendsto_expConvolution {β : ℝ} (hβ : 0 < β) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlim : Tendsto φ atTop (nhds 1))
    (hbound : ∃ M : ℝ, ∀ u ≥ 0, ‖φ u‖ ≤ M) :
    Tendsto (expConvolution β φ) atTop (nhds (1 / β)) := by
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0 le_rfl)
  let F : ℝ → ℝ → ℝ := fun u => (Set.Iic u).indicator
    (fun x => φ (u - x) * Real.exp (-β * x))
  have hFmeas (u : ℝ) : AEStronglyMeasurable (F u) (volume.restrict (Ici 0)) := by
    exact (by fun_prop : Continuous
      (fun x : ℝ => φ (u - x) * Real.exp (-β * x))).aestronglyMeasurable.indicator
      measurableSet_Iic
  have hFbound (u : ℝ) : ∀ᵐ x ∂volume.restrict (Ici (0 : ℝ)),
      ‖F u x‖ ≤ M * Real.exp (-β * x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    by_cases hxu : x ≤ u
    · simp only [F, Set.indicator_apply, Set.mem_Iic, hxu, ↓reduceIte,
        norm_mul, Real.norm_eq_abs, Real.abs_exp]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using hM (u - x) (sub_nonneg.mpr hxu))
        (Real.exp_pos _).le
    · simp only [F, Set.indicator_apply, Set.mem_Iic, hxu, ↓reduceIte, norm_zero]
      exact mul_nonneg hM0 (Real.exp_pos _).le
  have hkernel : IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ici 0) := by
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (exp_neg_integrableOn_Ioi 0 hβ)
  have hFlim (x : ℝ) : Tendsto (fun u => F u x) atTop (nhds (Real.exp (-β * x))) := by
    have hshift : Tendsto (fun u : ℝ => u - x) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        tendsto_atTop_add_const_right atTop (-x) tendsto_id
    have ht := (hlim.comp hshift).mul_const (Real.exp (-β * x))
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop x] with u hu
    simp [F, hu]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ici (0 : ℝ)))
    (fun x => M * Real.exp (-β * x))
    (Eventually.of_forall hFmeas) (Eventually.of_forall hFbound)
    (hkernel.const_mul M) (Eventually.of_forall hFlim)
  have hmass : (∫ x in Ici (0 : ℝ), Real.exp (-β * x)) = 1 / β := by
    rw [integral_Ici_eq_integral_Ioi]
    have h := integral_exp_neg_mul_rpow (p := 1) zero_lt_one hβ
    norm_num [Real.rpow_neg_one] at h
    simpa only [one_div, neg_mul] using h
  rw [hmass] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [expConvolution_eq_setIntegral β φ hu]
  simp only [F, setIntegral_indicator measurableSet_Iic, Ici_inter_Iic]

end CramerLundberg
