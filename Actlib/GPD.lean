import Mathlib

open Set Filter
open scoped Topology

set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generalized Pareto distribution

-/
noncomputable section
namespace GEV
open Real

def t (ξ μ σ x : ℝ) := ite (ξ = 0)
    (exp (- (x - μ)/ σ)) ((1 + ξ * ((x - μ)/σ)) ^ (-1 / ξ))

/-- The PDF of the generalized
Pareto distribution.
-/
def GPDPDF (ξ μ σ x : ℝ) : ℝ :=
  (ite (ξ = 0) ((1/σ) * exp (- ((x-μ)/σ)))
              ((1/σ) * (1 + ξ * (x-μ)/σ)^(-1-1/ξ)))
  * (ite ((ξ ≥ 0 ∧ x ≥ μ) ∨ (ξ < 0 ∧ μ ≤ x ∧ x ≤ μ - σ / ξ)) 1 0)

example : ∫ x, GPDPDF 0 0 1 x = 1 := by
  unfold GPDPDF
  simp
  -- certainly true
  sorry

/-- Pareto distribution has `xₘ` the minimum value
and `α` the Pareto index. -/
def ParetoPDF (xₘ α : ℝ) := GPDPDF α⁻¹ xₘ (xₘ * α⁻¹)

def StandardParetoPDF := ParetoPDF 1 1

example : ∫ x, StandardParetoPDF x = 1 := by
  simp [StandardParetoPDF, ParetoPDF, GPDPDF]
  field_simp
  suffices  (∫ (x : ℝ), if 1 ≤ x ∨ False ∧ 1 ≤ x ∧ x ≤ 0 then x ^ (-(1:ℝ) - 1) else 0) = 1 by
    convert this
    all_goals
      simp
  simp
  field_simp
  -- true!
  ring_nf
  sorry

example : ∫ x, GPDPDF (-1) 0 1 x = 1 := by
  unfold GPDPDF
  simp
  suffices (∫ (x : ℝ),
    if False ∧ 0 ≤ x ∨ 0 ≤ x ∧ x ≤ 1
    then (1:ℝ) else 0) = 1 by
    convert this
    simp
  simp
  -- certainly true
  sorry

example : ∫ x, GPDPDF (1) 0 1 x = 1 := by
  unfold GPDPDF
  simp
  suffices  (∫ (x : ℝ), if 0 ≤ x ∨ False ∧ 0 ≤ x ∧ x ≤ -1 then (1 + x) ^ (-(1:ℝ) - 1) else 0) = 1 by
    convert this
    simp
  simp
  -- certainly true
  sorry
