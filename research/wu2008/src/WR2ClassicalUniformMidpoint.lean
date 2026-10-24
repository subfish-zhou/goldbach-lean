import WR2ClassicalMidpointPanels

noncomputable section
namespace WuPaper.ClassicalUniformMidpoint
open Real Set MeasureTheory Finset

def step (a b : ℝ) (n : ℕ) : ℝ := (b-a)/n
def point (a b : ℝ) (n i : ℕ) : ℝ := a+step a b n*i

theorem point_mem {a b : ℝ} {n i : ℕ} (hn : 0 < n) (hab : a ≤ b) (hi : i ≤ n) :
    point a b n i ∈ Icc a b := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstep : 0 ≤ step a b n := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
  have hin : (i:ℝ) ≤ n := by exact_mod_cast hi
  have htop : step a b n*(n:ℝ) = b-a := by unfold step; exact div_mul_cancel₀ _ hn0
  constructor
  · dsimp [point]; linarith [mul_nonneg hstep hi0]
  · have h := mul_le_mul_of_nonneg_left hin hstep
    dsimp [point]; linarith

theorem midpoint_mem {a b : ℝ} {n i : ℕ} (hn : 0 < n) (hab : a ≤ b) (hi : i < n) :
    (point a b n i+point a b n (i+1))/2 ∈ Icc a b := by
  have hl := point_mem hn hab hi.le
  have hr := point_mem hn hab hi
  constructor <;> linarith [hl.1,hl.2,hr.1,hr.2]

/-- A uniform midpoint rule with an explicit derivative bound and arbitrary lower payments. -/
theorem uniform_lower {f f1 f2 : ℝ → ℝ} {a b B : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hd : ∀ s ∈ Icc a b, HasDerivAt f (f1 s) s)
    (hd1 : ∀ s ∈ Icc a b, HasDerivAt f1 (f2 s) s)
    (hB : ∀ s ∈ Icc a b, |f2 s| ≤ B)
    (q : ℕ → ℝ)
    (hq : ∀ i < n, q i ≤ f ((point a b n i+point a b n (i+1))/2)) :
    step a b n*(∑ i ∈ range n, q i)-(n:ℝ)*B*(step a b n)^3/24 ≤
      ∫ s in a..b, f s := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstep : 0 ≤ step a b n := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg _)
  have h0 : point a b n 0 = a := by simp [point]
  have hlast : point a b n n = b := by unfold point step; field_simp; ring
  have hx (i : ℕ) (hi : i ≤ n) : point a b n i ∈ Icc a b := point_mem hn hab hi
  have hwidth (i : ℕ) : point a b n (i+1)-point a b n i = step a b n := by
    simp only [point,Nat.cast_add,Nat.cast_one]
    ring
  have horder (i : ℕ) : point a b n i ≤ point a b n (i+1) := by linarith [hwidth i]
  have hsub (i : ℕ) (hi : i < n) : Icc (point a b n i) (point a b n (i+1)) ⊆ Icc a b :=
    fun _ ht => ⟨(hx i (by omega)).1.trans ht.1,ht.2.trans (hx (i+1) hi).2⟩
  have hi (i : ℕ) (hin : i < n) :
      IntervalIntegrable f volume (point a b n i) (point a b n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (horder i)]
    exact fun s hs => (hd s (hsub i hin hs)).continuousAt.continuousWithinAt
  have hp (i : ℕ) (hin : i < n) :
      step a b n*q i-B*(step a b n)^3/24 ≤
        ∫ s in point a b n i..point a b n (i+1), f s := by
    have hm := (WuSource.SrcFourEnclosure.midpoint_cell (horder i)
      (fun s hs => hd s (hsub i hin hs))
      (fun s hs => hd1 s (hsub i hin hs))
      (fun s hs => hB s (hsub i hin hs))).1
    rw [hwidth] at hm
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left (hq i hin) hstep) _).trans hm
  have hh := sum_le_sum (fun i hi => hp i (mem_range.mp hi))
  rw [intervalIntegral.sum_integral_adjacent_intervals hi,h0,hlast] at hh
  simp only [sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at hh
  linarith only [hh]

end WuPaper.ClassicalUniformMidpoint
#print axioms WuPaper.ClassicalUniformMidpoint.uniform_lower
