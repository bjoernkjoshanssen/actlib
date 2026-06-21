
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic

/-!

# Sipser Exercise 0.25

-/

def P_ (P M Y : ℂ) : ℕ → ℂ := λ n ↦ match n with
| 0 => P
| n + 1 => (P_ P M Y n)  * M - Y

theorem Sipser_025 (P M Y : ℂ) (hM: M - 1 ≠ 0) (t : ℕ) :
    P_ P M Y t = P * M^t - Y * (M^t - 1)/(M-1) := by
  induction t with
  | zero => simp; rfl
  | succ n n_ih =>
    have : P_ P M Y (Nat.succ n) = (P_ P M Y n) * M - Y := rfl
    rw [this, n_ih]
    apply mul_left_cancel₀ hM;
    field_simp
    ring
