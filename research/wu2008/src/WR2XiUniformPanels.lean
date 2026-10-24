import WR2XiRectangleLower

/-! Uniform finite partitions for the original node-cell integral certificates. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory
open scoped Interval BigOperators

def panelPoint (a b : ℝ) (n k : ℕ) : ℝ := a + (b - a) * k / n

theorem panelPoint_zero (a b : ℝ) (n : ℕ) : panelPoint a b n 0 = a := by
  simp [panelPoint]

theorem panelPoint_last (a b : ℝ) {n : ℕ} (hn : 0 < n) : panelPoint a b n n = b := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [panelPoint, hn0]

theorem panelPoint_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Monotone (panelPoint a b n) := by
  intro i j hij
  unfold panelPoint
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (sub_nonneg.mpr hab)

theorem panelPoint_step (a b : ℝ) (n k : ℕ) :
    panelPoint a b n (k + 1) - panelPoint a b n k = (b - a) / n := by
  unfold panelPoint
  push_cast
  ring

/-- A single global integrability proof suffices for every finite panel. -/
theorem uniform_rectangle_lower {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hab : a ≤ b) (hn : 0 < n) (hi : IntervalIntegrable f volume a b)
    (hc : ∀ k < n, ∀ t ∈ Icc (panelPoint a b n k) (panelPoint a b n (k + 1)),
      c k ≤ f t) :
    (∑ k ∈ Finset.range n, ((b - a) / n) * c k) ≤ ∫ t in a..b, f t := by
  have hm := panelPoint_mono hab n
  have hint (k : ℕ) (hk : k < n) :
      IntervalIntegrable f volume (panelPoint a b n k) (panelPoint a b n (k + 1)) := by
    apply hi.mono_set
    rw [uIcc_of_le (hm (Nat.le_succ k)), uIcc_of_le hab]
    intro t ht
    have hl := hm (Nat.zero_le k)
    have hr := hm (Nat.succ_le_of_lt hk)
    rw [panelPoint_zero] at hl
    rw [panelPoint_last a b hn] at hr
    exact ⟨hl.trans ht.1, ht.2.trans hr⟩
  have h := rectangle_sum_lower (fun k _ => hm (Nat.le_succ k)) hint hc
  simpa only [panelPoint_step, panelPoint_zero, panelPoint_last a b hn] using h

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.uniform_rectangle_lower
