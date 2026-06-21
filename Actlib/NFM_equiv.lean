import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Real.log
import Actlib.NFM

/-!

## Annuity present value as an equivalence

-/

open Finset Real Filter


theorem yield_exists.x
    {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : ε ≤ ↑m) ⦃x : ℝ⦄ (hx₀ : (↑m)⁻¹ ≤ 1 + x) :
    -1 < x := by
  calc -1 < -1 + (m:ℝ)⁻¹ := by
        refine lt_neg_add_iff_add_lt.mpr ?_
        simp only [add_neg_cancel, inv_pos]
        linarith
  _  ≤ x := by linarith

theorem yield_exists.y {n : ℕ} (hn : n ≠ 0) {ε : ℝ}
    {i : ℝ} (hi : annuity.a n i = ε)
    (hin : -1 < i) (y : ℝ) :
    -1 < y → ε = annuity.a n y → y = i := by
          intro hyn hyε
          by_contra H
          have : y < i ∨ i < y := lt_or_gt_of_ne H
          cases this with
          | inl h =>
            have := annuity.annuity_antitone hn h hyn
            linarith
          | inr h =>
            have := annuity.annuity_antitone hn h hin
            linarith

lemma yield_exists.sum {n : ℕ} (hn : n ≠ 0) (hnr : (n : ℝ) ≥ 1) :
    ∑ k ∈ Icc 1 n, ((2:ℝ) * ↑n)⁻¹ ^ k ≤ ∑ _ ∈ Icc 1 n, ((2:ℝ) * ↑n)⁻¹ := by
  apply sum_le_sum
  intro k hk
  simp only [mem_Icc] at hk
  have :  ((2:ℝ) * n)⁻¹ ≥ 0 := by
    positivity
  refine pow_le_of_le_one ?_ ?_ ?_
  · linarith
  · apply inv_le_one_of_one_le₀
    calc _ ≤ (n:ℝ) := hnr
         _ ≤ _     := by linarith
  · linarith

lemma yield_exists.bound {n : ℕ} (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε) (hnr : (n : ℝ) ≥ 1)
    (hnr₀ : ↑n > 0) (H : ε < 1) :
    (2 * ↑n / ε)⁻¹ ≤ 1 := by
  simp only [inv_div]
  calc ε / (2*n) ≤ 1 / (2*n) := by
        refine div_mul_le_div_mul_of_div_le_div ?_ ?_
        · refine (div_le_div_iff_of_pos_right ?_).mpr ?_
          · simp
          · linarith
        · simp
  _ ≤ _ := by
      suffices 1 ≤ 2 * n by
          refine (one_div_le ?_ ?_).mp ?_
          · simp
          · simp
            linarith
          · simp
            linarith
      calc 1 ≤ n := by contrapose! hn;linarith
              _ ≤ 2 * n := by omega

lemma le_geom_self {n : ℕ} (hnr : (n : ℝ) ≥ 1)
  (m : ℕ) (hm : m ≥ 1) : (m:ℝ) ≤ ∑ k ∈ Icc 1 n, (m:ℝ) ^ k := by
    calc (m:ℝ) ≤ ∑ k ∈ Icc 1 n, ↑m ^ 1 := by
                simp only [pow_one, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
                by_cases H : m = 0
                · subst H
                  simp
                suffices (1:ℝ) * m ≤ n * m by
                  convert this
                  simp
                apply mul_le_mul_of_nonneg
                · tauto
                all_goals simp
    _ ≤ _ := by
                apply sum_le_sum
                intro k hk
                simp at hk
                refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
                left
                constructor
                · simp;tauto
                · tauto

lemma yield_exists.small_epsilon {n : ℕ} (hn : n ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hnr : (n : ℝ) ≥ 1) (hnr₀ : (n : ℝ) > 0)
    (hnn₀ : n > 0) (H : ε < 1) :
  ∃! i, i > -1 ∧ ε = annuity.a n i := by
          have : annuity.a n (2 * n / ε - 1) < ε := by
            unfold annuity.a
            rw [add_sub_cancel]
            calc _ ≤  ∑ k ∈ Icc 1 n, (2*n / ε)⁻¹ := by
                    apply sum_le_sum
                    intro k hk
                    have h₁ : k ≥ 1 := by simp at hk;tauto
                    have h₀ : 0 ≤ (2*n / ε)⁻¹ := by
                      simp only [inv_div]
                      apply div_nonneg
                      · linarith
                      · simp
                    apply pow_le_of_le_one h₀ <| yield_exists.bound hn hε hnr hnn₀ H
                    omega
                 _ < _ := by
                    simp
                    ring_nf
                    field_simp
                    simp
          have : n / 1 ≤ n / ε := (div_le_div_iff₀ (by simp) hε).mpr
                <| (mul_le_mul_iff_of_pos_left hnr₀).mpr (by linarith)
          simp only [div_one] at this
          have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _ 0 (2 * n / ε - 1)
            (by
                calc (0:ℝ) ≤ 2 * n - 1 := by linarith
                     _ ≤ _ := by
                            field_simp;ring_nf
                            suffices  (↑n * ε) * 2 ≤ ↑n * 2 by linarith
                            suffices  (↑n * ε) ≤ ↑n by linarith
                            exact (le_div_iff₀ hε).mp this
                        )
                     (annuity.a n) (by
                        apply ContinuousOn.mono
                        · apply annuity_continuous (i := (2 * ↑n / ε - 1))
                        intro x hx
                        simp at hx ⊢
                        constructor
                        · linarith
                        · tauto) ε (by
                     simp
                     constructor <;> linarith)
          simp only [Set.mem_Icc] at hi
          have hin : -1 < i := by linarith
          use i
          simp only [gt_iff_lt, and_imp]
          constructor
          · constructor
            · linarith
            · exact hi.2.symm
          · apply yield_exists.y <;> tauto

noncomputable section

def yield_exists {n : ℕ} (hn : n ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃! i > -1, ε = annuity.a n i := by
  have hnr : (n:ℝ) ≥ 1 := by simp;omega
  have hnr₀ : (n:ℝ) > 0 := by simp;omega
  have hnn : n ≥ 1 := by omega
  have hnn₀ : n > 0 := by omega
  have hmm (m : ℕ) (hm : m ≥ 1) : m ≤ annuity.a n (-1 + 1/m) := by
    unfold annuity.a
    rw [add_neg_cancel_left, one_div, inv_inv]
    apply le_geom_self hnr m hm
  have : annuity.a n 0 = n := by unfold annuity.a annuity.geom_sum;simp
  by_cases H : ε < 1
  · exact yield_exists.small_epsilon hn hε hnr hnr₀ hnn₀ H
  have : annuity.a n (2 * n - 1) < ε := by
      unfold annuity.a
      rw [add_sub_cancel]
      calc _ ≤ _ := yield_exists.sum hn hnr
           _ < (1:ℝ) := by
              rw [Finset.sum_const]
              field_simp
              simp
              field_simp
              simp
            _ ≤ _ := by convert H; simp
  have ⟨m,hm⟩ := exists_nat_ge ε
  have hbound:  (-1:ℝ) + 1 / ↑m ≤ 2 * ↑n - 1 := by
      suffices (1:ℝ) / ↑m ≤ 2 * ↑n by linarith
      apply le_trans
      · change (1:ℝ) / m ≤ 1
        apply le_trans <| one_div_le_one_div_of_le hε hm
        · exact (div_le_one₀ hε).mpr (by convert H; simp)
      linarith
  have hcont : ContinuousOn (annuity.a n)
      (Set.Icc (-1 + 1 / ↑m) (2 * ↑n - 1)) := by
      apply ContinuousOn.mono
      · exact annuity_continuous (i := 2 * n - 1)
      · apply (Set.Icc_subset_Ioc_iff hbound).mpr
        constructor
        · apply lt_add_of_pos_right (-1)
          rw [one_div, inv_pos]
          exact lt_of_lt_of_le hε hm
        · exact le_refl _
  have hrange : ε ∈ Set.Icc (annuity.a n (2 * ↑n - 1))
                            (annuity.a n (-1 + 1 / ↑m)) := by
      simp only [one_div, Set.mem_Icc]
      constructor
      · exact le_of_lt this
      · apply le_trans hm
        specialize hmm m (by
            rw [not_lt] at H
            exact Nat.one_le_cast.mp <| le_trans H hm
            )
        simp only [one_div] at hmm
        exact hmm
  have ⟨i,hi⟩ := @intermediate_value_Icc' ℝ _ _ _ _ ℝ _ _ _
      (-1 + 1/m) (2 * n - 1) hbound (annuity.a n) hcont ε hrange
  simp only [one_div, Set.mem_Icc, neg_add_le_iff_le_add] at hi this
  have hin : -1 < i := by
      calc -1 < -1 + (m:ℝ)⁻¹ := by
            refine lt_neg_add_iff_add_lt.mpr ?_
            simp only [add_neg_cancel, inv_pos]
            linarith
      _  ≤ i := by linarith
  use i
  simp only [gt_iff_lt, and_imp]
  constructor
  · exact ⟨yield_exists.x hε hm hi.1.1, hi.2.symm⟩
  have := @yield_exists.y
  intro y hyn hyε
  by_contra H
  have : y < i ∨ i < y := lt_or_gt_of_ne H
  cases this with
  | inl h =>
      have := annuity.annuity_antitone hn h hyn
      linarith
  | inr h =>
      have := annuity.annuity_antitone hn h hin
      linarith

/-- Inverse of the annuity function. -/
def yield {n : ℕ} (hn : n ≠ 0) :
    Set.Ioi (0:ℝ) →  ℝ :=
    fun ε => (yield_exists hn ε.2).choose

/-- Now we can rename yield to annuity_equivalence.invFun -/
def annuity_equivalence (n : ℕ) (hn : n ≥ 2) : Equiv (Set.Ioi (-1:ℝ)) (Set.Ioi (0:ℝ)) := {
    toFun := fun i =>
        ⟨annuity.a n i, annuity.annuity_positive (by linarith) i.2⟩
    invFun := fun x =>
        ⟨
          yield (Nat.ne_zero_of_lt hn) x,
          (yield_exists (Nat.ne_zero_of_lt hn) x.2).choose_spec.1.1
        ⟩
    left_inv := by
        intro i
        have := (@yield_exists n (by linarith)
            (annuity.a n i) (annuity.annuity_positive (by linarith) i.2)).choose_spec
        symm
        refine SetCoe.ext ?_
        unfold yield
        simp only [gt_iff_lt, and_imp] at this ⊢
        apply this.2
        · exact i.2
        · rfl
    right_inv := by
        intro x
        have := (@yield_exists n (by linarith) x x.2).choose_spec
        symm
        refine SetCoe.ext ?_
        convert this.1.2
        unfold yield
        simp
}

-- lemma yield_is_inverse  (n : ℕ) (hn : n ≠ 0) (ε :Set.Icc (0:ℝ) n) :
--     Function.LeftInverse (yield n hn) (fun i => ⟨ite (0 ≤ i) (annuity.a n i) 0, by
--         simp
--         constructor
--         by_cases H : 0 ≤ i
--         rw [if_pos H]
--         apply annuity.annuity_positive hn (by linarith)
--         rw [if_neg H]

--         sorry⟩) := by
--     sorry


/-- If the value of an annuity is `n-1` then the yield interest rate `i` must have been 0. -/
theorem yield_zero {n : ℕ} (hn : n ≥ 2) (hd : 0 < (n : ℝ) - 1) :
  let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
  yield hn₀ ⟨↑n - 1, hd⟩ = 0 := by
    let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
    have hspec:= (@yield_exists (n-1) hn₀ (n-1) (by linarith)).choose_spec.2 0
    have := hspec (by
        obtain ⟨m,hm⟩ : ∃ m, n = m+1 := Nat.exists_eq_succ_of_ne_zero (by linarith)
        subst hm
        simp)
    simp_rw [this]
    simp [yield]

open annuity

/-- A bond with coupon zero has duration equal to maturity. -/
lemma duration_coupon_zero {n : ℕ}
    {d : ℝ} {i : ℝ} (hr : -1 < i)
    (h : duration_equation n i 0 d) :
    d = n := by
  have : (1+i)⁻¹ ^ n > 0 := pow_pos (inv_pos.mpr (by linarith)) _
  unfold duration_equation annuity.bond_price annuity.bond_price_sum at h
  generalize (1+i)⁻¹ ^ n = α at *
  have : d * α = n * α := by linarith
  rw [mul_eq_mul_right_iff] at this
  cases this with
  | inl h => tauto
  | inr h => subst h;simp at this

/-- Perhaps surprisingly:
Let i be the implied interest rate for an n-period
par bond of duration d.
Then the PV of an (n-1)-period unit-payment annuity with rate i is d-1.
This lets us compute `i` from `n` and `d`. -/
lemma eq_CPT_I_of_D_par {n : ℕ} (hn : n ≥ 2) -- if n=1, then D=n and we can't infer i.
    {i : ℝ} (hi : i > -1) {d : ℝ} (hd : 0 < d - 1)
    (h : duration_equation n i i d) :
    let hn₀ : n - 1 ≠ 0 := by contrapose! hn;omega
    yield hn₀ ⟨d - 1, hd⟩ = i := by
    by_cases H : i = 0
    · subst H
      simp_rw [duration_coupon_zero hi h]
      apply yield_zero hn
    unfold duration_equation
      annuity.bond_price
      annuity.bond_price_sum
      at h
    have : annuity.geom_sum n (1 + i)⁻¹ = annuity.a n i := rfl
    rw [this] at h
    rw [congrFun <| annuity.a_eq_a_formula (H) (by linarith)] at h
    unfold annuity.a_formula annuity.Ia annuity.id_mul_geom_sum at h
    have := @id_mul_geom_sum_formula (1+i)⁻¹ (by
      simp only [ne_eq, inv_eq_one, add_eq_left]
      exact H) n
    unfold id_mul_geom_sum at this
    rw [this] at h
    have : i ≠ 0 := H
    have : 1 + i ≠ 0 := by linarith
    set v := (1+i)⁻¹
    have hv₂ : (v - 1) ^ 2 ≠ 0 := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, v]
        intro hc
        have : (1 + i)⁻¹ = 1 := by linarith
        have : (1 + i) = 1 := by field_simp at this;tauto
        apply H
        linarith
    rw [mul_comm i, div_mul] at h
    field_simp at h ⊢
    have h₀ : - (i * v) * (↑n * v ^ (n + 1) - (↑n + 1) * v ^ n + 1)
              + (d - ↑n * v ^ n) * (v - 1) ^ 2 = 0 := by
        generalize (v-1)^2 = α at *
        field_simp at h
        linarith
    have h₁ : i * v = 1 - v := by unfold v; field_simp; ring_nf
    rw [h₁] at h₀
    have h₂ : -1 * ((v - 1) * (- (d * v) + d + v^n - 1)) = 0 := by
        ring_nf at h₀ this
        linarith
    have h₃ : v - 1 ≠ 0 := by contrapose! hv₂;rw [hv₂];simp
    have : (v - 1) * (- (d * v) + d + v^n - 1) = 0 := by linarith
    have : - (d * v) + d + v^n - 1 = 0 := (mul_eq_zero_iff_left h₃).mp this
    have : v^n - d * v + d - 1 = 0 := by linarith
    have : (v^n - d * v + d - 1) / (v - 1) = 0 := by rw [this]; simp
    obtain ⟨t,ht⟩ : ∃ m, n = m + 2 := Nat.exists_eq_add_of_le' hn
    obtain ⟨m,hm⟩ : ∃ m, n = m + 1 := by use t+1
    subst hm
    have hw : (v ^ (m + 1) - d * v + d - 1) = (v - 1) * (annuity.a m i - d + 1) := by
        have : v ^ (m + 1) = v ^ m * v := rfl
        rw [this, sub_mul, congrFun <| @annuity.a_eq_a_formula i H (by linarith)]
        unfold annuity.a_formula v
        field_simp
        ring_nf
    have h₃ : annuity.a m i - d + 1 = 0 := by
        rw [hw, mul_comm] at this
        rw [← this]
        field_simp
    have h₄ : d - 1 = annuity.a m i := by linarith
    have := (@yield_exists (m) (by linarith) (d - 1) hd).choose_spec
    simp only [gt_iff_lt, and_imp] at this
    simp_rw [this.2 i hi h₄]
    simp [yield]
