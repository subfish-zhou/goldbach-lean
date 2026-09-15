import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackKernel

/-! Full source domains and inverse slices. No source area is removed. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

inductive Kind where
  | six | seven | eight
  deriving DecidableEq

noncomputable def a : ℝ := 25 / 103
noncomputable def b : ℝ := 25 / 89
noncomputable def c : ℝ := 100 / 291
noncomputable def f : ℝ := 2 / 5
noncomputable def S : ℝ := 103 / 25
noncomputable def lo : Kind → ℝ → ℝ
  | .six, _ => c
  | .seven, t => t
  | .eight, _ => b
noncomputable def hi : Kind → ℝ
  | .six => f
  | .seven => b
  | .eight => c

def region (j : Kind) (t u : ℝ) : Prop :=
  t ∈ Icc a b ∧ u ∈ Icc (lo j t) (hi j)
noncomputable def V : Kind → ℝ → ℝ → ℝ
  | .six, t, u => S * (1 - t - u)
  | .seven, t, u => (1 - t - u) / t
  | .eight, t, u => (1 - t - u) / t
noncomputable def invU : Kind → ℝ → ℝ → ℝ
  | .six, v, t => gamma5FeedbackW v - t
  | .seven, v, t => 1 - (v + 1) * t
  | .eight, v, t => 1 - (v + 1) * t

def slice (j : Kind) (v t : ℝ) : Prop := region j t (invU j v t)
noncomputable def L : Kind → ℝ → ℝ
  | .six, v => max a (gamma5FeedbackW v - f)
  | .seven, v => max a ((1 - b) / (v + 1))
  | .eight, v => max a ((1 - c) / (v + 1))
noncomputable def U : Kind → ℝ → ℝ
  | .six, v => min b (gamma5FeedbackW v - c)
  | .seven, v => min b (1 / (v + 2))
  | .eight, v => min b ((1 - b) / (v + 1))
noncomputable def vLo : Kind → ℝ
  | .six => S * (1 - b - f)
  | .seven => (1 - 2 * b) / b
  | .eight => (1 - b - c) / b
noncomputable def vHi : Kind → ℝ
  | .six => S * (1 - a - c)
  | .seven => (1 - 2 * a) / a
  | .eight => (1 - a - b) / a

theorem constants : 0 < a ∧ a < b ∧ b < c ∧ c < f ∧
    1 / 10 ≤ a ∧ b < 3 / 10 ∧ f < 1 / 2 ∧ b + f < 3 / 4 := by
  norm_num [a, b, c, f]

theorem image_constants (j : Kind) : 1 < vLo j ∧ vHi j < 3 := by
  cases j <;> norm_num [vLo, vHi, S, a, b, c, f]

theorem lo_le_hi (j : Kind) {t : ℝ} (ht : t ∈ Icc a b) : lo j t ≤ hi j := by
  cases j
  · exact constants.2.2.2.1.le
  · exact ht.2
  · exact constants.2.2.1.le

theorem region_bounds {j : Kind} {t u : ℝ} (h : region j t u) :
    t ∈ Icc a b ∧ u ∈ Icc a f ∧ 1 / 4 < 1 - t - u := by
  rcases h with ⟨ht, hu⟩
  have hu' : u ∈ Icc a f := by
    cases j <;> simp only [lo, hi, mem_Icc] at hu
    · exact ⟨constants.2.1.le.trans (constants.2.2.1.le.trans hu.1), hu.2⟩
    · exact ⟨ht.1.trans hu.1, hu.2.trans (constants.2.2.1.le.trans constants.2.2.2.1.le)⟩
    · exact ⟨constants.2.1.le.trans hu.1, hu.2.trans constants.2.2.2.1.le⟩
  exact ⟨ht, hu', by linarith [ht.2, hu'.2, constants.2.2.2.2.2.2.2]⟩

theorem region_image {j : Kind} {t u : ℝ} (h : region j t u) :
    V j t u ∈ Icc (vLo j) (vHi j) := by
  have ht0 : 0 < t := constants.1.trans_le h.1.1
  rcases h with ⟨⟨hta, htb⟩, ⟨hul, huh⟩⟩
  cases j <;> simp only [V, vLo, vHi, lo, hi, mem_Icc] at *
  · norm_num [S, a, b, c, f] at *
    constructor <;> linarith
  · constructor
    · apply (le_div_iff₀ ht0).mpr
      norm_num [a, b] at *
      linarith
    · apply (div_le_iff₀ ht0).mpr
      norm_num [a, b] at *
      linarith
  · constructor
    · apply (le_div_iff₀ ht0).mpr
      norm_num [a, b, c] at *
      linarith
    · apply (div_le_iff₀ ht0).mpr
      norm_num [a, b, c] at *
      linarith

theorem inv_V (j : Kind) {t : ℝ} (ht : 0 < t) (u : ℝ) :
    invU j (V j t u) t = u := by
  cases j
  · dsimp [invU, V, gamma5FeedbackW, S, gamma5ClassicalS]
    ring
  · dsimp [invU, V]; field_simp; ring
  · dsimp [invU, V]; field_simp; ring

theorem V_inv (j : Kind) {t : ℝ} (ht : 0 < t) (v : ℝ) :
    V j t (invU j v t) = v := by
  cases j
  · dsimp [invU, V, gamma5FeedbackW, S, gamma5ClassicalS]
    ring
  · dsimp [invU, V]; field_simp; ring
  · dsimp [invU, V]; field_simp; ring

theorem slice_bounds {j : Kind} {v t : ℝ} (h : slice j v t) :
    v ∈ Icc (vLo j) (vHi j) ∧ t ∈ Icc a b ∧ invU j v t ∈ Icc a f := by
  have hb := region_bounds h
  have hv := region_image h
  rw [V_inv j (constants.1.trans_le hb.1.1)] at hv
  exact ⟨hv, hb.1, hb.2.1⟩

theorem slice_unit {j : Kind} {v t : ℝ} (h : slice j v t) : v ∈ Icc (1 : ℝ) 3 :=
  ⟨(image_constants j).1.le.trans (slice_bounds h).1.1,
    (slice_bounds h).1.2.trans (image_constants j).2.le⟩

theorem slice_iff (j : Kind) {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) (t : ℝ) :
    slice j v t ↔ L j v ≤ t ∧ t ≤ U j v := by
  have hq : 0 < v + 1 := by linarith [hv.1]
  have hr : 0 < v + 2 := by linarith [hv.1]
  cases j <;> simp only [slice, region, invU, lo, hi, L, U, mem_Icc,
    max_le_iff, le_min_iff]
  · constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;>
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rw [div_le_iff₀ hq, le_div_iff₀ hr]
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;>
      constructor <;> constructor <;> nlinarith
  · rw [div_le_iff₀ hq, le_div_iff₀ hq]
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;>
      constructor <;> constructor <;> nlinarith

end Wu2008DoubleSieve.Gamma678Feedback
