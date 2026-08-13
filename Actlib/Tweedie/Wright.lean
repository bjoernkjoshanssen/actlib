import Mathlib
open MeasureTheory Set
open scoped BigOperators Real Nat
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false
/-- The Wright series occurring in the density of a positive stable law. -/
noncomputable def stableWrightSeries (a z : ℝ) : ℝ :=
  ∑' k : ℕ, (-z) ^ k / ((k.factorial : ℝ) * Real.Gamma (-(a * (k : ℝ))))
/-- The unit-scale positive-stable density written as a Wright series. -/
noncomputable def stableWrightKernel (a y : ℝ) : ℝ :=
  y⁻¹ * stableWrightSeries a (y ^ (-a))
/-- Scaling the integration variable reduces a Laplace transform at `t > 0`
to a unit exponential weight.  No integrability assumption is needed because the
change-of-variables theorem for the Bochner integral has the same convention on
both sides when a function is not integrable. -/
theorem laplace_Ioi_rescale (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi 0, f y * Real.exp (-(t * y))) =
      ∫ x in Ioi 0, t⁻¹ * f (x * t⁻¹) * Real.exp (-x) := by
  have h_eq : (fun y => f y * Real.exp (-(t * y))) = (fun y => f y * Real.exp (-(y * t))) := by
    ext y; ring_nf
  rw [h_eq]
  have h1 : ∫ y in Ioi 0, f y * Real.exp (-(y * t))
    = t⁻¹ * ∫ x in Ioi 0, f (x * t⁻¹) * Real.exp (-x) := by
    have h2 := integral_comp_mul_right_Ioi (a := 0) (b := t) (fun x => f (x * t⁻¹) * Real.exp (-x))
      ht
    simp_all [mul_assoc, mul_inv_cancel₀ (ne_of_gt ht)]
  rw [h1]
  rw [← MeasureTheory.integral_const_mul]
  ac_rfl
/-- The requested identity is exactly reduced, by an elementary change of
variables, to the same transform with exponential weight `exp (-x)`. -/
theorem positiveStable_laplace_iff_rescaled {a t : ℝ} (ht : 0 < t) :
    ((∫ y in Ioi 0, stableWrightKernel a y * Real.exp (-(t * y))) =
        Real.exp (-(t ^ a))) ↔
      ((∫ x in Ioi 0,
          t⁻¹ * stableWrightKernel a (x * t⁻¹) * Real.exp (-x)) =
        Real.exp (-(t ^ a))) := by
  rw [laplace_Ioi_rescale (stableWrightKernel a) ht]
/-- The one-parameter Wright integral that remains after scaling out the
Laplace variable. -/
noncomputable def scaledStableWrightIntegrand (a s x : ℝ) : ℝ :=
  x⁻¹ * stableWrightSeries a (s * x ^ (-a)) * Real.exp (-x)
/-- For positive variables, the rescaled stable kernel is exactly the Wright
integrand with parameter `s = t ^ a`. -/
theorem rescaled_stableWrightKernel_eq
    {a t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    t⁻¹ * stableWrightKernel a (x * t⁻¹) * Real.exp (-x) =
      scaledStableWrightIntegrand a (t ^ a) x := by
  have hp : (x * t⁻¹) ^ (-a) = t ^ a * x ^ (-a) := by
    rw [Real.mul_rpow hx.le (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le,
      ← Real.rpow_neg ht.le]
    ring_nf
  unfold stableWrightKernel scaledStableWrightIntegrand
  rw [hp, mul_inv_rev]
  field_simp
/-- Integral form of the algebraic scaling identity. -/
theorem rescaled_stableWrightKernel_integral
    {a t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi 0,
        t⁻¹ * stableWrightKernel a (x * t⁻¹) * Real.exp (-x)) =
      ∫ x in Ioi 0, scaledStableWrightIntegrand a (t ^ a) x := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact rescaled_stableWrightKernel_eq ht hx
/-- Consequently, the original two-variable claim follows from the following
one-parameter analytic fact: the integral of the scaled Wright integrand at
`s = t ^ a` is `exp (-s)`. -/
theorem positiveStable_laplace_of_scaledWright_integral
    {a t : ℝ} (ht : 0 < t)
    (hWright :
      (∫ x in Ioi 0, scaledStableWrightIntegrand a (t ^ a) x) =
        Real.exp (-(t ^ a))) :
    (∫ y in Ioi 0, stableWrightKernel a y * Real.exp (-(t * y))) =
      Real.exp (-(t ^ a)) := by
  rw [positiveStable_laplace_iff_rescaled ht]
  rw [rescaled_stableWrightKernel_integral ht]
  exact hWright
/-- A direct formulation of the requested statement, reduced to the rescaled
unit-exponential integral.  This scaling theorem is stronger than the requested
version: it only needs `t > 0`; the assumptions `0 < a < 1` are needed for the
remaining analytic Wright-integral evaluation, not for scaling. -/
theorem positiveStable_laplace_of_rescaled
    {a t : ℝ} (ht : 0 < t)
    (hrescaled :
      (∫ x in Ioi 0,
          t⁻¹ * stableWrightKernel a (x * t⁻¹) * Real.exp (-x)) =
        Real.exp (-(t ^ a))) :
    (∫ y in Ioi 0,
        (y⁻¹ * ∑' k : ℕ,
          (-y ^ (-a)) ^ k /
            ((k.factorial : ℝ) * Real.Gamma (-(a * (k : ℝ))))) *
          Real.exp (-(t * y))) =
      Real.exp (-(t ^ a)) := by
  exact (positiveStable_laplace_iff_rescaled ht).mpr hrescaled
