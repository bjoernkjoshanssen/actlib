import Mathlib
import Actlib.Laplace.Bounds
import Actlib.Laplace.Fubini
import Actlib.Laplace.Rotation
import Actlib.Laplace.Plemelj

/-!
# The main theorem

This file formalizes the theorem labelled `thm:main` of `wright_laplace.tex` ("A contour-free
proof of the unit-scale positive-stable Laplace-transform identity"), that is, the Lean statement
`integral_wright_positive_stable_unit` displayed in the introduction of the source:

> for `a ∈ (0,1)` and `t > 0`, the function `y ↦ (1/y) W_{-a,0}(-y^{-a}) e^{-ty}` is Lebesgue
> integrable on `(0,∞)` and `∫_0^∞ (1/y) W_{-a,0}(-y^{-a}) e^{-ty} dy = e^{-t^a}`.

The proof is the one of the source: integrability is the corollary `cor:bounds` (iii), and the
value of the integral follows from the lemma `lem:fubini`
(`∫_0^∞ g(y)e^{-ty}dy = (1/π) Im D(θ)`), the lemma `lem:rotation` (`D` is constant on `(0,θ]`,
so `Im D(θ) = lim_{ψ→0⁺} Im D(ψ)`) and the lemma `lem:plemelj`
(`lim_{ψ→0⁺} Im D(ψ) = π e^{-t^a}`), in that order.
-/

namespace WrightLaplace

open MeasureTheory Set Complex Filter Topology

/-- The middle equality of the proof of the theorem `thm:main` of `wright_laplace.tex`:
`Im D(θ) = lim_{ψ→0⁺} Im D(ψ) = π e^{-t^a}`.  Indeed `D` is constant on `(0,θ]` by the lemma
`lem:rotation`, so the limit of `Im D` at `0⁺` is `Im D(θ)`, and that limit is `π e^{-t^a}` by
the lemma `lem:plemelj`. -/
theorem im_D_theta {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    (D a t (theta a)).im = Real.pi * Real.exp (-(t ^ a)) := by
  have hconst : Tendsto (fun psi : ℝ => (D a t psi).im) (𝓝[>] (0 : ℝ))
      (𝓝 ((D a t (theta a)).im)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_mem_Ioc_theta ha0 ha1] with psi hpsi
    exact congrArg Complex.im (D_eq_D_theta ha0 ha1 ht hpsi).symm
  exact tendsto_nhds_unique hconst (tendsto_im_D ha0 ha1 ht)

/-- The integrability assertion of the theorem `thm:main` of `wright_laplace.tex`: for
`a ∈ (0,1)` and `t > 0` the function `y ↦ (1/y) W_{-a,0}(-y^{-a}) e^{-ty}` is Lebesgue integrable
on `(0,∞)`.  This is the corollary `cor:bounds` (iii), the integrand being `g(y)e^{-ty}` by the
definition `eq:gdef` of `g`. -/
theorem integrableOn_wright_positive_stable_unit {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht : 0 < t) :
    IntegrableOn
      (fun y : ℝ => 1 / y * wrightBessel (-a) 0 (-(y ^ (-a))) * Real.exp (-t * y)) (Ioi 0) :=
  integrableOn_g_mul_exp_neg ha0 ha1 ht

/-- The theorem `thm:main` of `wright_laplace.tex` ("A contour-free proof of the unit-scale
positive-stable Laplace-transform identity"), i.e. the Lean statement
`integral_wright_positive_stable_unit` displayed in the introduction of the source: for
`a ∈ (0,1)` and `t > 0`,
`∫_0^∞ (1/y) W_{-a,0}(-y^{-a}) e^{-ty} dy = e^{-t^a}`. -/
theorem integral_wright_positive_stable_unit {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ht : 0 < t) :
    (∫ y in Ioi (0 : ℝ), 1 / y * wrightBessel (-a) 0 (-(y ^ (-a))) * Real.exp (-t * y))
      = Real.exp (-(t ^ a)) := by
  have hg : (∫ y in Ioi (0 : ℝ), 1 / y * wrightBessel (-a) 0 (-(y ^ (-a))) * Real.exp (-t * y))
      = ∫ y in Ioi (0 : ℝ), g a y * Real.exp (-t * y) := rfl
  rw [hg, integral_g_mul_exp_neg_eq_im_D ha0 ha1 ht, im_D_theta ha0 ha1 ht]
  field_simp

end WrightLaplace
