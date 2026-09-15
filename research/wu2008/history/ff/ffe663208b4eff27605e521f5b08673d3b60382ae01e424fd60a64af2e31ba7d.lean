import SrcBuchstabPolynomial
import SrcBuchstabPropagation

namespace WuSource.SrcBuchstab

open Set Real MeasureTheory LiLiuPrereqBuchstab

noncomputable section

def baseCoeffs (a : ℝ) (c : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![a * c 0 - 1, a * c 1 + c 0, a * c 2 + c 1, a * c 3 + c 2,
    a * c 4 + c 3, a * c 5 + c 4, a * c 6 + c 5]

def residual (a : ℝ) (c d : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun i => weightedCoeffs a c i - d i

theorem initial_enclosure {a h x : ℝ} {c : Fin 7 → ℝ}
    (ha : 1 ≤ a) (hx : 0 ≤ x) (hxh : x ≤ h) (ha' : a + h ≤ 2)
    (hc : deficit (baseCoeffs a c) h ≤ baseCoeffs a c 0)
    (hc6 : 0 ≤ c 6) : buchstab (a + x) ≤ poly c x := by
  have hn := poly_nonneg hx hxh hc
  have he : (a + x) * poly c x - 1 =
      poly (baseCoeffs a c) x + c 6 * x ^ 7 := by
    dsimp [poly, baseCoeffs]
    ring
  have hp : 0 ≤ c 6 * x ^ 7 := mul_nonneg hc6 (pow_nonneg hx 7)
  rw [buchstab_eq_one_div (by linarith) (by linarith)]
  apply (div_le_iff₀ (by linarith : 0 < a + x)).2
  nlinarith

theorem cell_enclosure {a h : ℝ} {c d : Fin 7 → ℝ} (ha : 2 ≤ a)
    (anchor : buchstab a ≤ c 0)
    (history : ∀ x : ℝ, 0 ≤ x → x ≤ h →
      buchstab (a + x - 1) ≤ poly d x)
    (cert : deficit (residual a c d) h ≤ residual a c d 0)
    {x : ℝ} (hx : 0 ≤ x) (hxh : x ≤ h) :
    buchstab (a + x) ≤ poly c x := by
  let f : ℝ → ℝ := fun z => (a + z) * poly c z - (a + z) * buchstab (a + z)
  have hc : ContinuousOn f (Icc 0 h) := by
    have hp : Continuous (poly c) := by unfold poly; fun_prop
    exact ((continuous_const.add continuous_id).mul hp |>.sub
      ((continuous_const.add continuous_id).mul
        (continuous_buchstab.comp (continuous_const.add continuous_id)))).continuousOn
  have hd (z : ℝ) (hz : z ∈ interior (Icc 0 h)) :
      HasDerivAt f (poly (weightedCoeffs a c) z - buchstab (a + z - 1)) z := by
    rw [interior_Icc] at hz
    have hb := (hasDerivAt_mul_buchstab (by linarith [hz.1] : 2 < a + z)).comp z
      ((hasDerivAt_id z).const_add a)
    have hb' : HasDerivAt (fun y => (a + y) * buchstab (a + y))
        (buchstab (a + z - 1)) z := by
      simpa only [mul_one, Function.comp_def] using hb
    exact (weighted_derivative a c z).sub hb'
  have hm : MonotoneOn f (Icc 0 h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h) hc
      (fun z hz => (hd z hz).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    have hr := poly_nonneg hz.1.le hz.2.le cert
    have he : poly (residual a c d) z =
        poly (weightedCoeffs a c) z - poly d z := by
      dsimp [poly, residual]
      ring
    rw [he] at hr
    linarith [history z hz.1.le hz.2.le]
  have hh : 0 ≤ h := hx.trans hxh
  have hm' := hm (show (0 : ℝ) ∈ Icc 0 h from ⟨le_rfl, hh⟩) ⟨hx, hxh⟩ hx
  have h0 : 0 ≤ f 0 := by
    dsimp [f, poly]
    simp only [zero_pow (by omega : (2 : ℕ) ≠ 0),
      zero_pow (by omega : (3 : ℕ) ≠ 0), zero_pow (by omega : (4 : ℕ) ≠ 0),
      zero_pow (by omega : (5 : ℕ) ≠ 0), zero_pow (by omega : (6 : ℕ) ≠ 0),
      mul_zero, add_zero]
    nlinarith
  have hfx : 0 ≤ f x := h0.trans hm'
  dsimp [f] at hfx
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < a + x)).mp (by linarith)

def left (n : ℕ) : ℝ := 1 + (n : ℝ) / 20

theorem left_delay {i : ℕ} (hi : 20 ≤ i) : left (i - 20) = left i - 1 := by
  dsimp [left]
  rw [Nat.cast_sub hi]
  norm_num
  ring

theorem left_previous {i : ℕ} (hi : 1 ≤ i) :
    left (i - 1) + 1 / 20 = left i := by
  dsimp [left]
  rw [Nat.cast_sub hi]
  norm_num
  ring

theorem certified_prefix (C : ℕ → Fin 7 → ℝ)
    (base : ∀ i : ℕ, i < 20 →
      deficit (baseCoeffs (left i) (C i)) (1 / 20) ≤ baseCoeffs (left i) (C i) 0 ∧
      0 ≤ C i 6)
    (start : (1 / 2 : ℝ) ≤ C 20 0)
    (join : ∀ i : ℕ, 20 < i → i < 68 → poly (C (i - 1)) (1 / 20) ≤ C i 0)
    (step : ∀ i : ℕ, 20 ≤ i → i < 68 →
      deficit (residual (left i) (C i) (C (i - 20))) (1 / 20) ≤
        residual (left i) (C i) (C (i - 20)) 0)
    (i : ℕ) (hi : i < 68) {x : ℝ} (hx : 0 ≤ x) (hxh : x ≤ 1 / 20) :
    buchstab (left i + x) ≤ poly (C i) x := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    by_cases hi20 : i < 20
    · apply initial_enclosure (by dsimp [left]; linarith [Nat.cast_nonneg (α := ℝ) i]) hx hxh _
        (base i hi20).1 (base i hi20).2
      have hi' : (i : ℝ) ≤ 19 := by exact_mod_cast (show i ≤ 19 by omega)
      dsimp [left]
      linarith
    · have hi20' : 20 ≤ i := by omega
      have ha : 2 ≤ left i := by
        have hh : (20 : ℝ) ≤ i := by exact_mod_cast hi20'
        dsimp [left]
        linarith
      apply cell_enclosure ha _ _ (step i hi20' hi) hx hxh
      · by_cases hieq : i = 20
        · subst i
          norm_num [left, buchstab_eq_one_div (by norm_num : (1 : ℝ) ≤ 2) le_rfl]
          exact start
        · have hip : 1 ≤ i := by omega
          have hh := ih (i - 1) (by omega) (by omega) (x := (1 / 20 : ℝ))
            (by norm_num) le_rfl
          rw [left_previous hip] at hh
          exact hh.trans (join i (by omega) hi)
      · intro z hz hz'
        have hh := ih (i - 20) (by omega) (by omega) hz hz'
        rw [left_delay hi20'] at hh
        convert hh using 1 <;> congr 1 <;> ring

theorem grid_cover (n : ℕ) {a h t : ℝ} (ha : a ≤ t)
    (ht : t ≤ a + ((n : ℝ) + 1) * h) :
    ∃ i : ℕ, i ≤ n ∧ a + (i : ℝ) * h ≤ t ∧
      t ≤ a + ((i : ℝ) + 1) * h := by
  induction n with
  | zero => exact ⟨0, le_rfl, by simpa using ha, by simpa using ht⟩
  | succ n ih =>
    by_cases hn : t ≤ a + ((n : ℝ) + 1) * h
    · obtain ⟨i, hi, hi', hi''⟩ := ih hn
      exact ⟨i, by omega, hi', hi''⟩
    · refine ⟨n + 1, le_rfl, ?_, ht⟩
      push_cast
      exact le_of_not_ge hn

theorem initial_window_covered {t : ℝ} (ht : (17 / 5 : ℝ) ≤ t) (ht' : t ≤ 22 / 5) :
    ∃ i : ℕ, 48 ≤ i ∧ i < 68 ∧ 0 ≤ t - left i ∧ t - left i ≤ 1 / 20 := by
  obtain ⟨i, hi, hi', hi''⟩ := grid_cover 19 (h := (1 / 20 : ℝ)) ht (by norm_num; exact ht')
  refine ⟨i + 48, by omega, by omega, ?_, ?_⟩ <;> dsimp [left] <;> push_cast <;> linarith

theorem certified_fine_tail (C : ℕ → Fin 7 → ℝ)
    (base : ∀ i : ℕ, i < 20 →
      deficit (baseCoeffs (left i) (C i)) (1 / 20) ≤ baseCoeffs (left i) (C i) 0 ∧
      0 ≤ C i 6)
    (start : (1 / 2 : ℝ) ≤ C 20 0)
    (join : ∀ i : ℕ, 20 < i → i < 68 → poly (C (i - 1)) (1 / 20) ≤ C i 0)
    (step : ∀ i : ℕ, 20 ≤ i → i < 68 →
      deficit (residual (left i) (C i) (C (i - 20))) (1 / 20) ≤
        residual (left i) (C i) (C (i - 20)) 0)
    (cap : ∀ i : ℕ, 48 ≤ i → i < 68 → ∀ j : Fin 7,
      bernstein (C i) (1 / 20) j ≤ 561522 / 1000000)
    {t : ℝ} (ht : (17 / 5 : ℝ) ≤ t) : buchstab t ≤ 561522 / 1000000 := by
  apply fine_tail_of_initial_window _ ht
  intro u hu hu'
  obtain ⟨i, hi, hi', hx, hx'⟩ := initial_window_covered hu hu'
  have hb := certified_prefix C base start join step i hi' hx hx'
  have hc := bernstein_cap (by norm_num : (0 : ℝ) < 1 / 20) hx hx' (cap i hi hi')
  have he : left i + (u - left i) = u := by ring
  rw [he] at hb
  exact hb.trans hc

#print axioms certified_fine_tail
#print axioms initial_window_covered

end

end WuSource.SrcBuchstab
