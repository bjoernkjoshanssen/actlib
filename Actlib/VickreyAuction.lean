import Mathlib.Analysis.RCLike.Basic
noncomputable section

/--
b = bid
m = maximum of others' bid
v = value
p = profit (or loss if negative)
-/
def p₂ (v m b : ℝ) := ite (b > m) (v - m) 0

/-- Add a percentage fee of `i`.
If `v < m * (1 + i)` we may decline the purchase.
-/
def p₂_with_fee (v m i b : ℝ) : ℝ :=
     ite (b > m) (max (v - m * (1 + i)) 0) 0

lemma vickrey_with_fee (v m i b : ℝ)
    (hm : 0 < m)
    (hi : 0 ≤ i) :
    p₂_with_fee v m i b ≤
    p₂_with_fee v m i v := by
    unfold p₂_with_fee
    have : 0 < 1 + i := by linarith
    split_ifs with g₀ g₁
    all_goals try simp
    all_goals try linarith
    ·   simp at g₁
        apply le_trans g₁
        suffices m * 1 ≤ m * (1 + i) by simp at this; exact this
        apply mul_le_mul
        simp
        linarith
        simp
        linarith

def p₁ (v m b : ℝ) := ite (b > m) (v - b) 0
def p₃ (v m₀ m₁ b : ℝ) := ite (b > max m₀ m₁) (v - min m₀ m₁) 0

/-- Vickrey auction profit when there is a minimum acceptable price of `a`. -/
def p₂_with_reserve (v m a b : ℝ) : ℝ :=
    ite (b ≥ a) (ite (m ≥ a) (p₂ v m b) (v - a)) 0
    --   · exact p₂ v m b -- both our bid and others' bids are high enough
    --   · exact v - a -- the second price was too low, so we pay the minimum acceptable price
    -- · exact 0 -- our bid was not high enough



/-- With reserve,
the best bid in a sealed-bid second-price auction is your true value. -/
lemma vickrey_with_reserve (v m a b : ℝ) : p₂_with_reserve v m a b ≤
                                           p₂_with_reserve v m a v := by
    unfold p₂_with_reserve p₂
    split_ifs
    all_goals try simp
    all_goals try linarith


/-- The best bid in a sealed-bid second-price auction is your true value. -/
lemma vickrey (v m b : ℝ) : p₂ v m b ≤ p₂ v m v := by
    unfold p₂
    split_ifs
    all_goals try simp
    all_goals linarith



open NNReal

/-- In a sealed-bid first-price auction, there is no
winning strategy.
Can also prove there is no `f` when `m=0`?
-/
lemma vickrey₁ : ¬ ∃ f : ℝ≥0 → ℝ≥0,
    ∀ (v : ℝ≥0), v > 0 → ∀ m > 0, ∀ b > 0, p₁ v m b ≤ p₁ v m (f v) := by
  unfold p₁
  push Not
  intro f
  use 2
  by_cases H : f 2 = 0
  · rw [H]
    constructor
    · simp
    · use 1/2
      constructor
      · simp
      · use 1
        rw [if_neg (by simp)]
        rw [if_pos one_half_lt_one]
        simp
  constructor
  · simp
  use 1 * f 2 / 2
  have H : (f 2).toReal > 0 := by convert pos_of_ne_zero H
  simp only [one_mul, gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right, coe_pos, half_lt_self_iff,
    NNReal.coe_ofNat]
  constructor
  · exact H
  use 2 * f 2 / 3 -- we squeeze our bid in between `m` and `f v`
  rw [if_pos (by refine coe_lt_coe.mp H)]
  rw [if_pos (by linarith)]
  constructor <;> linarith




/-- In a sealed-bid third-price auction, there is no
winning strategy.
-/
lemma vickrey' : ¬ ∃ f : ℝ≥0 → ℝ≥0, ∀ (v m₀ m₁ b : ℝ≥0),
    p₃ v m₀ m₁ b ≤
    p₃ v m₀ m₁ (f v) := by
    push Not
    intro f
    use 2, f 2, 1, 2 + f 2
    simp only [p₃]
    split_ifs
    all_goals try simp_all
    have : (f 2).toReal ≥ 0 := zero_le_coe
    linarith


/- If now `v` and `m` are uniform on `[0,1]`, in a first-bid auction we may choose
to bid `v/2`. Because given that `m≤v` that is `𝔼m`.
Then we prove the other player's `max 𝔼` profit is by using same strategy.
-/
#min_imports
