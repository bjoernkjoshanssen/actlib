import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Process.Stopping

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal BigOperators

open MeasureTheory

noncomputable section


def Int.ofFin2 (i : Fin 2) : ℤ := 2 * Int.ofNat i.1 - 1

def u : Fin 3 → (Fin 3 → Fin 2) → ℤ :=
    fun t ω => ∑ i < t, Int.ofFin2 (ω i)

open Real
def 𝓕 := Filtration.natural u fun _ => StronglyMeasurable.of_discrete

def τ₀ (ω : Fin 3 → Fin 2) : WithTop (Fin 3) :=
    if u 2 ω = 2 then WithTop.some 2 else ⊤

example : IsStoppingTime 𝓕 τ₀ := by
  intro i
  fin_cases i
  · -- i = 0: the set {ω | τ ω ≤ 0} is empty, since τ is either ↑2 or ⊤
    convert MeasurableSet.empty
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, τ₀]
    split <;> simp
  · -- i = 1: the set {ω | τ ω ≤ 1} is empty, since τ is either ↑2 or ⊤
    convert MeasurableSet.empty
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, τ₀]
    split <;> simp
  · -- i = 2: the set {ω | τ ω ≤ 2} = {ω | u 2 ω = 2}, which is measurable
    -- because u 2 is measurable w.r.t. the natural filtration at time 2
    have hm : StronglyMeasurable[𝓕 2] (u 2) :=
      Filtration.stronglyAdapted_natural (fun _ => StronglyMeasurable.of_discrete) 2
    have hm' : @Measurable _ _ (𝓕 2) _ (u 2) := hm.measurable
    convert hm' (MeasurableSet.singleton 2) using 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, τ₀]
    constructor
    · intro h; split at h <;> [assumption; simp at h]
    · intro h; rw [if_pos h]; simp

-- END

def T (ω : ℕ → ℕ) : WithTop ℕ :=
  if ω 0 = 1 then 1 else ⊤

example : IsStoppingTime Filtration.piLE T := by
  unfold T
  intro i
  constructor
  swap
  · exact if i = 0 then ∅ else {ω : Set.Iic i → ℕ | ω ⟨0, by simp⟩ = 1}
  rcases i with ( _ | i )
  · aesop;
  · constructor
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, measurableSet_setOf]
      apply MeasurableSet.mem
      apply measurableSet_eq_fun
      · apply measurable_pi_apply
      · exact measurable_const
    · ext ω
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Set.preimage_setOf_eq,
        Preorder.restrictLe_apply, Set.mem_setOf_eq, WithTop.coe_add, ENat.some_eq_coe,
        WithTop.coe_one]
      split_ifs <;> (simp; tauto)

def T' (ω : Fin 5 → Fin 2) : WithTop (Fin 5) :=
         (if ω 0 = 1 ∧ ω 1 = 1 then
            WithTop.some 2 else
          if ω 0 = 0 ∧ ω 1 = 1 ∧ ω 2 = 1 ∧ ω 3 = 1 then
            WithTop.some 4 else
          if ω 0 = 1 ∧ ω 1 = 0 ∧ ω 2 = 1 ∧ ω 3 = 1 then
            WithTop.some 4 else ⊤)

def T₀ (ω : Fin 5 → Fin 2) : WithTop (Fin 5) :=
         (if ω 0 = 1 ∧ ω 1 = 1 then
            WithTop.some 1 else
          if ω 0 = 0 ∧ ω 1 = 1 ∧ ω 2 = 1 ∧ ω 3 = 1 then
            WithTop.some 3 else
          if ω 0 = 1 ∧ ω 1 = 0 ∧ ω 2 = 1 ∧ ω 3 = 1 then
            WithTop.some 3 else ⊤)

example : IsStoppingTime Filtration.piLE T₀ := by
  unfold T₀
  intro i
  fin_cases i
  · constructor
    swap
    · simp only [Fin.zero_eta, Fin.isValue]
      exact ∅
    · simp
      ext ω
      simp
      split_ifs
      · exact sign_eq_one_iff.mp rfl
      · exact sign_eq_one_iff.mp rfl
      · exact sign_eq_one_iff.mp rfl
      · exact WithTop.top_pos
  · sorry
  · sorry
  · sorry
  · sorry



def τ (ω : Fin 1 → Fin 2) : WithTop (Fin 1) :=
         (if ω 0 = 1 then
            WithTop.some 0 else ⊤)

example : IsStoppingTime Filtration.piLE T' := by
  unfold T'
  intro i
  fin_cases i
  · constructor
    swap
    · simp only [Fin.zero_eta, Fin.isValue]
      exact ∅
    · constructor
      · simp
      · ext ω
        simp
        split_ifs <;> simp
  · constructor
    swap
    · simp only [Fin.mk_one, Fin.isValue]
      exact ∅
    · constructor
      · simp
      · ext ω
        simp
        split_ifs <;> simp
  · constructor
    swap
    · exact {ω | ω ⟨0, by simp⟩ = 1 ∧ ω ⟨1, by simp⟩ = 1}
    · constructor
      · simp only [Fin.reduceFinMk, Fin.isValue, measurableSet_setOf]
        apply ((measurable_pi_apply _).eq_const _).and ((measurable_pi_apply _).eq_const _)
      · ext ω
        simp
        split_ifs <;>
        · simp;tauto
  · constructor
    swap
    · exact {ω | ω ⟨0, by simp⟩ = 1 ∧ ω ⟨1, by simp⟩ = 1}
    · constructor
      · simp only [Fin.reduceFinMk, Fin.isValue, measurableSet_setOf]
        apply ((measurable_pi_apply _).eq_const _).and ((measurable_pi_apply _).eq_const _)
      · ext ω
        simp
        split_ifs <;>
        · simp;tauto
  · constructor
    swap
    · exact {ω |
        (ω ⟨0, by simp⟩ = 1 ∧ ω ⟨1, by simp⟩ = 1) ∨
        (ω ⟨0, by simp⟩ = 0 ∧ ω ⟨1, by simp⟩ = 1 ∧ ω ⟨2, by simp⟩ = 1 ∧ ω ⟨3, by simp⟩ = 1)
        ∨
        (ω ⟨0, by simp⟩ = 1 ∧ ω ⟨1, by simp⟩ = 0 ∧ ω ⟨2, by simp⟩ = 1 ∧ ω ⟨3, by simp⟩ = 1)
        }
    · constructor
      · simp only [Fin.reduceFinMk, Fin.isValue, measurableSet_setOf]
        refine Measurable.or ?_ ?_
        · apply Measurable.and <;> exact Measurable.eq_const (measurable_pi_apply _) _
        · refine Measurable.or ?_ ?_ <;>
          · exact measurable_pi_apply _|>.eq_const _|>.and
               <| measurable_pi_apply _|>.eq_const _|>.and
               <| measurable_pi_apply _|>.eq_const _|>.and
               <| measurable_pi_apply _|>.eq_const _
      · ext ω
        simp
        split_ifs <;>
        · simp;tauto



open MeasureTheory MeasurableSpace

set_option maxHeartbeats 800000

/-!
# Stopping Times: Examples and Non-Examples

## Why the original `S` IS a stopping time

The original definition used `Fin 1 → Fin 2` (a single time step with binary outcomes).
Since `Fin 1 = {0}`, the filtration `piLE 0` sees ALL coordinates (there's only one!),
making it the full σ-algebra. Every set is measurable, so every random time is a stopping time.

## A genuine non-stopping-time example

To get a non-stopping-time, we need at least two time steps (`Fin 2 → Fin 2`) so that
the filtration at time 0 genuinely doesn't see the future (coordinate 1).

We define `T ω = 0` if `ω 1 = 1`, else `⊤`. This "peeks into the future" at time 0:
the event `{ω | T ω ≤ 0}` depends on `ω 1`, which is not measurable w.r.t. `piLE 0`.
-/

/-! ### Part 1: The original S IS a stopping time -/

def S (ω : Fin 1 → Fin 2) : WithTop (Fin 1) :=
  if ω 0 = 1 then WithTop.some 0 else ⊤

/-- The filtration `piLE 0` on `Fin 1 → Fin 2` is the full σ-algebra,
because `restrictLe 0` is injective (every index in `Fin 1` is `≤ 0`). -/
lemma piLE_fin1_eq_top : Filtration.piLE (X := fun _ : Fin 1 => Fin 2) 0 = ⊤ := by
  ext s
  simp only [MeasurableSpace.measurableSet_top, iff_true]
  show @MeasurableSet _ (MeasurableSpace.pi.comap (Preorder.restrictLe (0 : Fin 1))) s
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Preorder.restrictLe 0 '' s, MeasurableSet.of_discrete, ?_⟩
  have hinj : Function.Injective (Preorder.restrictLe (0 : Fin 1) : (Fin 1 → Fin 2) → _) := by
    intro a b hab; funext i; exact congr_fun hab ⟨i, Fin.le_last i⟩
  exact Set.preimage_image_eq s hinj

/-- The original `S` is actually a stopping time (the negation was false). -/
theorem S_isStoppingTime : IsStoppingTime Filtration.piLE S := by
  intro i
  fin_cases i
  change @MeasurableSet _ (Filtration.piLE 0) _
  rw [piLE_fin1_eq_top]
  trivial

/- The original claim was:
  example : ¬ IsStoppingTime Filtration.piLE S := by sorry
This is FALSE because S is a stopping time, as proved above.
With only one time step, piLE 0 = ⊤ (the full σ-algebra), so every
random variable is trivially a stopping time. -/

/-! ### Part 2: A genuine non-stopping-time example -/

/-- A random time that peeks into the future: it returns 0 when `ω 1 = 1`,
but at time 0 we can only observe `ω 0`, not `ω 1`. -/
def T'' (ω : Fin 2 → Fin 2) : WithTop (Fin 2) :=
  if ω 1 = 1 then WithTop.some 0 else ⊤

/-- Two functions that agree on coordinates ≤ 0 but differ on coordinate 1.
This witnesses that `restrictLe 0` cannot distinguish them. -/
private def ω₀ : Fin 2 → Fin 2 := ![0, 0]
private def ω₁ : Fin 2 → Fin 2 := ![0, 1]

private lemma restrict_eq : Preorder.restrictLe (0 : Fin 2) ω₀ = Preorder.restrictLe 0 ω₁ := by
  funext ⟨i, hi⟩
  simp only [Preorder.restrictLe]
  fin_cases i
  · simp [ω₀, ω₁]
  · exact absurd hi (by decide)

private lemma T_diff : T'' ω₀ ≠ T'' ω₁ := by decide

/-
`T` is NOT a stopping time w.r.t. `piLE`: the event `{ω | T ω ≤ 0}` depends on
the future coordinate `ω 1`, which is not visible in `piLE 0`.
-/
-- theorem T_not_isStoppingTime : ¬ IsStoppingTime Filtration.piLE T'' := by
--   intro h;
--   have := h 0;
--   obtain ⟨ s, hs, h ⟩ := this;
--   simp_all +decide [ Set.ext_iff ];
--   have := h ω₀; have := h ω₁; simp_all +decide [ restrict_eq ] ;
