import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Real

/-!
# Elementary analytic lemmas for the Cramér–Lundberg integral equation

A limit at infinity determines a function with zero derivative on the positive half-line.
We also record boundedness on the nonnegative half-line from continuity and a finite limit.
-/

open Set Filter
open scoped Topology

namespace CramerLundberg

lemma eq_of_hasDerivAt_zero_of_tendsto
    {f : ℝ → ℝ} {L : ℝ}
    (hcont : ContinuousOn f (Ici 0))
    (hderiv : ∀ u > 0, HasDerivAt f 0 u)
    (hlim : Tendsto f atTop (𝓝 L)) :
    ∀ u ≥ 0, f u = L := by
  have hconst : ∀ u > 0, f u = f 1 := by
    intro u hu
    apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (f := f) (x := u) (y := 1)
    · intro x hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hderiv x hx).deriv
    · exact hu
    · norm_num
  have hlim' : Tendsto f atTop (𝓝 (f 1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (hconst u hu).symm
  have h1 : f 1 = L := tendsto_nhds_unique hlim' hlim
  have hclosed : IsClosed {u ∈ Ici (0 : ℝ) | f u = L} :=
    isClosed_Ici.isClosed_eq hcont continuousOn_const
  have hsub : Ioi (0 : ℝ) ⊆ {u ∈ Ici (0 : ℝ) | f u = L} := by
    intro u hu
    exact ⟨show (0 : ℝ) ≤ u from le_of_lt (show (0 : ℝ) < u from hu),
      (hconst u hu).trans h1⟩
  have hclosure := closure_minimal hsub hclosed
  rw [closure_Ioi] at hclosure
  intro u hu
  exact (hclosure hu).2

lemma bounded_Ici_of_continuousOn_tendsto
    {f : ℝ → ℝ} {L : ℝ}
    (hcont : ContinuousOn f (Ici 0))
    (hlim : Tendsto f atTop (𝓝 L)) :
    ∃ M : ℝ, ∀ u ≥ 0, ‖f u‖ ≤ M := by
  have htail : ∀ᶠ u in atTop, ‖f u‖ < ‖L‖ + 1 :=
    hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖))
  obtain ⟨R, hR⟩ := eventually_atTop.1 htail
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) R ⊆ Ici 0))
  refine ⟨max M (‖L‖ + 1), ?_⟩
  intro u hu
  by_cases huR : u ≤ R
  · exact (hM u ⟨hu, huR⟩).trans (le_max_left _ _)
  · exact (hR u (le_of_not_ge huR)).le.trans (le_max_right _ _)

end CramerLundberg
