import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!

# Ryan Sasaki's MA project 2022

Translated to Lean 4 by Quinn Culver; edited by Bjørn Kjos-Hanssen

-/

open Real

lemma D_add {f g : ℝ → ℝ} (df : Differentiable ℝ f) (dg : Differentiable ℝ g) :
    deriv (f + g) = deriv f + deriv g := by
  ext x;rw [deriv_add (df x) (dg x)]
  rfl


lemma D_mul {f g : ℝ → ℝ} (df : Differentiable ℝ f) (dg : Differentiable ℝ g) :
    deriv (f * g) = deriv f * g + f * deriv g := by
  ext x
  rw [deriv_mul (df x) (dg x)]
  rfl

lemma second_D_mul {f g : ℝ → ℝ} (df : Differentiable ℝ f) (d₂f : Differentiable ℝ (deriv f)) (dg : Differentiable ℝ g) (d₂g : Differentiable ℝ (deriv g)) :
    deriv (deriv (f * g)) = deriv (deriv f) * g + 2 * deriv f * deriv g + f * deriv (deriv g) := by
  rw [D_mul df dg, D_add (d₂f.mul dg) (df.mul d₂g), D_mul d₂f dg, D_mul df d₂g]
  grind

lemma exp_D {f : ℝ → ℝ} (df : Differentiable ℝ f) : deriv (λ x : ℝ => exp (f x)) = λ x : ℝ => exp (f x) * deriv f x := funext (λ x => deriv_exp (df x))

lemma const_mul_D (a : ℝ) : deriv (λ x : ℝ => a * x) = λ _ : ℝ => a := by
  ext y
  rw [deriv_const_mul]
  simp only [deriv_id'', mul_one]
  exact differentiableAt_fun_id

/--
The function satisfies Redington immunization at a point.
-/
def redington (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0 ∧ deriv f x = 0 ∧ deriv (deriv f) x > 0

lemma hf2_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
    (df : Differentiable ℝ f) (dg₀ : Differentiable ℝ g₀) (hf : f δ = 0) (hg₀ : 0 < g₀ δ)
    (hg : (deriv (f * g₀)) δ = 0) :
    (deriv f) δ = 0 :=
  let g := (f * g₀)
  have h₁ : deriv g = deriv f * g₀ + f * deriv g₀ := by apply (D_mul df dg₀)
  have h₂ : deriv f δ * g₀ δ + f δ * deriv g₀ δ = deriv g δ := by exact
    (congrFun h₁ δ).symm
  have h₃ : deriv f δ * g₀ δ = 0 := by rw [hf] at h₂; simp at h₂; rw [hg] at h₂; rw [h₂]
  have g₀_ne_zero : g₀ δ ≠ 0 := by exact ne_of_gt hg₀
  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₃

lemma d₂g_form_simplified_justification {f g₀ : ℝ → ℝ} {δ : ℝ}
    (df : Differentiable ℝ f) (d₂f : Differentiable ℝ (deriv f))
    (dg₀ : Differentiable ℝ g₀) (d₂g₀ : Differentiable ℝ (deriv g₀)) (hf : f δ = 0) (hf' : (deriv f) δ = 0) :
    (deriv (deriv (f * g₀))) δ = (deriv (deriv f)) δ * g₀ δ :=
  show (deriv (deriv (f * g₀))) δ = (deriv (deriv f)) δ * g₀ δ by
  calc
    (deriv (deriv (f * g₀))) δ = (deriv (deriv f) * g₀    + 2 * deriv f * deriv g₀     + f * deriv (deriv g₀)) δ   := congrFun (second_D_mul df d₂f dg₀ d₂g₀) δ
    _ = deriv (deriv f) δ * g₀ δ + 2 * deriv f δ * deriv g₀ δ + f δ * deriv (deriv g₀) δ  := by rfl
    _ = deriv (deriv f) δ * g₀ δ + 2 * deriv f δ * deriv g₀ δ +   0 * deriv (deriv g₀) δ  := by rw [hf]
    _ = deriv (deriv f) δ * g₀ δ + 2 * 0     * deriv g₀ δ +   0 * deriv (deriv g₀) δ  := by rw [hf']
    _ = (deriv (deriv f)) δ * g₀ δ := by ring

lemma hf1_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
  (hg : (f * g₀) δ = 0) (g₀_pos : 0 < g₀ δ):
  f δ = 0 :=
  have h₁ : f δ * g₀ δ = 0 := by rw [← hg]; rfl
  have g₀_ne_zero : g₀ δ ≠ 0 := ne_of_gt g₀_pos
  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₁

theorem g_form_implies_redington_f_iff_g {f : ℝ → ℝ} {t δ: ℝ}
  (df : Differentiable ℝ f)
  (d₂f : Differentiable ℝ (deriv f)):
  let g := λ x : ℝ => (f x) * exp (t * x)
  (redington f δ ↔ redington g δ) :=
  let g := λ x : ℝ => (f x) * exp (t * x)
  let g₀_arg   := λ x : ℝ => t * x
  let g₀       := λ x : ℝ=> exp (t * x)
  let f'       := deriv f
  let f''      := deriv f'
  let g'       := deriv g
  let g''      := deriv g'
  have g_form_at_δ : g δ = (f δ) * (g₀ δ) := rfl
  have dg₀_arg : Differentiable ℝ g₀_arg := Differentiable.const_mul (differentiable_id) t
  have dg₀ : Differentiable ℝ g₀ := Differentiable.exp dg₀_arg
  have dg₀_arg_form : deriv g₀_arg = λ _ : ℝ => t := by rw [const_mul_D t]
  have dg₀_form_lemma : ∀ y : ℝ, (λ (x : ℝ) => exp (g₀_arg x) * (λ (_ : ℝ) => t) x) y = (λ (x : ℝ) => t * exp (t * x)) y := by
    intro y
    exact mul_comm (exp (g₀_arg y)) ((λ _ => t) y)
  have dg₀_form : deriv g₀ = λ x : ℝ => t * exp (t * x) := by rw [exp_D dg₀_arg]; rw [dg₀_arg_form]; exact funext dg₀_form_lemma
  have d₂g₀ : Differentiable ℝ (deriv g₀) := by rw [dg₀_form]; apply Differentiable.mul (differentiable_const t) (dg₀)
  have g₀_pos : 0 < g₀ δ := exp_pos (t * δ)
  have forward_dir : redington f δ → redington g δ := by
    intro hf;
    have hf1 : f δ = 0 := hf.1;
    have hf2 : f' δ = 0 := hf.2.1;
    have hf3 : f'' δ > 0 := hf.2.2;
    have hg1 : g δ = 0 := by rw [g_form_at_δ]; rw [hf1]; rw [zero_mul]
    have hg2 : g' δ = 0 := by
      calc
      g' δ = deriv (f * g₀) δ                      := rfl
      _ = (deriv f * g₀ + f * deriv g₀) δ          := by rw[D_mul df dg₀]
      _ = (deriv f) δ * g₀ δ + f δ * (deriv g₀) δ  := by simp
      _ = 0 * g₀ δ + f δ * (deriv g₀) δ        := by rw [← hf2]
      _ = 0 * g₀ δ + 0 * (deriv g₀) δ          := by rw [hf1]
      _ = 0 + 0 := by repeat rw[zero_mul]
      _ = 0 := add_zero _
    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ := d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2
    have hg3 : 0 < g'' δ := by rw [d₂g_form_simplified]; apply mul_pos hf3 g₀_pos
    exact ⟨hg1, hg2, hg3⟩

  have reverse_dir : redington g δ → redington f δ := by
    intro hg;
    have hg3 : g'' δ > 0 := hg.2.2;
    have hf1 : f δ = 0 := hf1_justification hg.1 g₀_pos;
    have hf2 : f' δ = 0 := hf2_justification df dg₀ hf1 g₀_pos hg.2.1
    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ :=
      d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2
    have hf3 : f'' δ > 0 := by
      rw [d₂g_form_simplified] at hg3;
      exact (pos_iff_pos_of_mul_pos hg3).mpr g₀_pos
    exact ⟨hf1, hf2, hf3⟩
  ⟨forward_dir, reverse_dir⟩
