import Mathlib

open Set Filter
open scoped Topology

set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Kumaraswamy distribution

For positive shape parameters `a` and `b`, the Kumaraswamy distribution is supported
on `[0,1]`.  This file defines its cumulative distribution function and density,
and proves elementary properties including endpoint values, bounds, monotonicity,
nonnegativity of the density, and the derivative relation between the CDF and PDF.
-/

namespace Kumaraswamy

/-- The cumulative distribution function of the Kumaraswamy distribution. -/
noncomputable def kumaraswarmyCDF (a b x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if 1 ≤ x then 1 else 1 - (1 - x ^ a) ^ b


/-- The probability density of the Kumaraswamy distribution. -/
noncomputable def kumaraswamyPDF (a b x : ℝ) : ℝ :=
  if x ≤ 0 ∨ 1 ≤ x then 0
  else a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)

noncomputable def kumaraswamyPDF' (a b x : ℝ) : ℝ :=
  Set.indicator (Set.Ioo 0 1) (fun x =>
       a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1)) x

lemma kumaraswamyPDF_eq_kumaraswamyPDF (a b x : ℝ) :
  kumaraswamyPDF a b x = kumaraswamyPDF' a b x := by
    unfold kumaraswamyPDF kumaraswamyPDF' Set.indicator
    simp only [mem_Ioo]
    generalize a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1) = y
    split_ifs with g₀ g₁ g₂
    · cases g₀ <;> linarith;
    · cases g₀ <;> linarith;
    · rfl
    · push Not at g₀ g₂
      specialize g₂ g₀.1
      linarith

@[simp] theorem kumaraswarmyCDF_of_nonpos (a b x : ℝ) (hx : x ≤ 0) : kumaraswarmyCDF a b x = 0 := by
  simp [kumaraswarmyCDF, hx]

@[simp] theorem kumaraswarmyCDF_of_one_le (a b x : ℝ) (hx : 1 ≤ x) : kumaraswarmyCDF a b x = 1 := by
  exact if_neg (by linarith) |> fun h => h.trans (if_pos hx)

@[simp] theorem kumaraswarmyCDF_zero (a b : ℝ) : kumaraswarmyCDF a b 0 = 0 := by
  simp

@[simp] theorem kumaraswarmyCDF_one (a b : ℝ) : kumaraswarmyCDF a b 1 = 1 := by
  simp

/-
Formula for the CDF in the interior of its support.
-/
theorem kumaraswarmyCDF_of_mem_Ioo (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kumaraswarmyCDF a b x = 1 - (1 - x ^ a) ^ b := by
  exact if_neg hx.1.not_ge |> fun h => h.trans <| if_neg hx.2.not_ge

@[simp] theorem pdf_of_nonpos (a b x : ℝ) (hx : x ≤ 0) : kumaraswamyPDF a b x = 0 := by
  simp [kumaraswamyPDF, hx]

@[simp] theorem pdf_of_one_le (a b x : ℝ) (hx : 1 ≤ x) : kumaraswamyPDF a b x = 0 := by
  simp [kumaraswamyPDF, hx]

/-
Formula for the density in the interior of its support.
-/
theorem pdf_of_mem_Ioo (a b x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    kumaraswamyPDF a b x = a * b * x ^ (a - 1) * (1 - x ^ a) ^ (b - 1) := by
  exact if_neg (by aesop)

/-
The CDF always takes values in `[0,1]` when the shape parameters are positive.
-/
theorem kumaraswarmyCDF_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    kumaraswarmyCDF a b x ∈ Icc (0 : ℝ) 1 := by
  by_cases hx : x ≤ 0 <;> by_cases hx' : 1 ≤ x <;> simp [ *, kumaraswarmyCDF ];
  exact ⟨ Real.rpow_le_one (sub_nonneg.2 <| Real.rpow_le_one (by linarith) (by linarith)
    <| by linarith) (sub_le_self _ <| Real.rpow_nonneg (by linarith) _) <| by linarith,
      Real.rpow_nonneg (sub_nonneg.2 <| Real.rpow_le_one (by linarith) (by linarith)
      <| by linarith) _⟩

/-
The Kumaraswamy CDF is monotone.
-/
theorem kumaraswarmyCDF_monotone {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Monotone (kumaraswarmyCDF a b) := by
  intro x y hxy
  by_cases hx : x ≤ 0;
  · exact le_trans (by norm_num [ kumaraswarmyCDF_of_nonpos _ _ _ hx ]) (kumaraswarmyCDF_mem_Icc ha hb y |>.1);
  · by_cases hy : y ≤ 1;
    · by_cases hx' : x ≤ 1 <;> by_cases hy' : y ≤ 1 <;> simp_all +decide [ kumaraswarmyCDF ];
      · split_ifs <;> try linarith;
        · exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.2
            <| Real.rpow_le_one hx.le hx' ha.le) _)
        · exact sub_le_sub_left (Real.rpow_le_rpow (sub_nonneg.2 <| Real.rpow_le_one (by linarith)
            (by linarith) <| by linarith) (sub_le_sub_left (Real.rpow_le_rpow (by linarith) hxy
            <| by linarith) _) <| by linarith) _;
      · linarith;
    · simp_all +decide [ kumaraswarmyCDF ];
      split_ifs <;> try linarith;
      exact sub_le_self _ (Real.rpow_nonneg (sub_nonneg.2
        <| Real.rpow_le_one hx.le (by linarith) ha.le) _)

/-
The Kumaraswamy density is nonnegative.
-/
theorem pdf_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ kumaraswamyPDF a b x := by
  by_cases hx : x ≤ 0 ∨ 1 ≤ x;
  · cases hx <;> simp +decide [ *, kumaraswamyPDF ];
  · simp +zetaDelta at *;
    exact pdf_of_mem_Ioo a b x hx ▸ mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) (Real.rpow_nonneg hx.1.le _)) (Real.rpow_nonneg (sub_nonneg.2 <| Real.rpow_le_one hx.1.le hx.2.le ha.le) _)

/-
On `(0,1)`, the derivative of the CDF is the density.
-/
theorem hasDerivAt_kumaraswarmyCDF {a b x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (kumaraswarmyCDF a b) (kumaraswamyPDF a b x) x := by
  convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
  exact fun t => 1 - (1 - t ^ a) ^ b;
  · convert HasDerivAt.const_sub _ (HasDerivAt.rpow_const (HasDerivAt.const_sub _ (Real.hasDerivAt_rpow_const _)) _) using 1 <;> norm_num [ hx.1.ne', hx.2.ne', ha.ne' ];
    · rw [ pdf_of_mem_Ioo a b x hx ] ; ring;
    · exact Or.inl <| ne_of_gt <| sub_pos_of_lt <| Real.rpow_lt_one hx.1.le hx.2 ha;
  · filter_upwards [ Ioo_mem_nhds hx.1 hx.2 ] with t ht using by rw [ kumaraswarmyCDF_of_mem_Ioo _ _ _ ht ] ;

/-
Consequently, the CDF is strictly increasing on `(0,1)`.
-/
theorem strictMonoOn_kumaraswarmyCDF {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (kumaraswarmyCDF a b) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy;
  rw [ kumaraswarmyCDF_of_mem_Ioo, kumaraswarmyCDF_of_mem_Ioo ] <;> norm_num at *;
  · exact Real.rpow_lt_rpow (sub_nonneg.2 <| Real.rpow_le_one hy.1.le hy.2.le ha.le)
      (sub_lt_sub_left (Real.rpow_lt_rpow hx.1.le hxy ha) _) hb;
  · tauto;
  · tauto

end Kumaraswamy
