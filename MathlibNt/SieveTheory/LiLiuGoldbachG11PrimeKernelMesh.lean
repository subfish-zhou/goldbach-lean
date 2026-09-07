import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelLimit
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelReduction
import MathlibNt.SieveTheory.LiuPrimePairLogGridLimit

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11MeshStep (n : ℕ) : ℝ :=
  ((4 / 33 : ℝ) - 4 / 53) / (n + 1)

def goldbachG11MeshPoint (n i : ℕ) : ℝ :=
  4 / 53 + i * goldbachG11MeshStep n

def goldbachG11MeshCoords {α : Type*} (x : (α × α) × (α × α)) : Fin 4 → α :=
  ![x.1.1, x.1.2, x.2.1, x.2.2]

def goldbachG11MeshCells (n : ℕ) :
    Finset ((Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :=
  univ.filter fun j => j.1.1 ≤ j.1.2 ∧ j.1.2 ≤ j.2.1 ∧ j.2.1 ≤ j.2.2

def goldbachG11MeshLo (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : ℝ :=
  goldbachG11MeshPoint n (goldbachG11MeshCoords j i).val

def goldbachG11MeshHi (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : ℝ :=
  goldbachG11MeshPoint n ((goldbachG11MeshCoords j i).val + 1)

theorem goldbachG11MeshStep_pos (n : ℕ) : 0 < goldbachG11MeshStep n := by
  unfold goldbachG11MeshStep
  positivity

theorem goldbachG11MeshPoint_succ (n i : ℕ) :
    goldbachG11MeshPoint n (i + 1) =
      goldbachG11MeshPoint n i + goldbachG11MeshStep n := by
  simp only [goldbachG11MeshPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem goldbachG11MeshPoint_strictMono (n : ℕ) :
    StrictMono (goldbachG11MeshPoint n) := by
  intro i j hij
  unfold goldbachG11MeshPoint
  have := mul_lt_mul_of_pos_right (show (i : ℝ) < j by exact_mod_cast hij)
    (goldbachG11MeshStep_pos n)
  linarith

theorem goldbachG11MeshPoint_end (n : ℕ) :
    goldbachG11MeshPoint n (n + 1) = 4 / 33 := by
  unfold goldbachG11MeshPoint goldbachG11MeshStep
  push_cast
  field_simp
  ring

theorem goldbachG11MeshPoint_bounds (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) :
    goldbachG11MeshPoint n i ∈ Icc (4 / 53 : ℝ) (4 / 33) := by
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachG11MeshStep_pos n).le)
  · rw [← goldbachG11MeshPoint_end n]
    exact (goldbachG11MeshPoint_strictMono n).monotone hi

theorem goldbachG11MeshPoint_pos (n i : ℕ) :
    0 < goldbachG11MeshPoint n i := by
  unfold goldbachG11MeshPoint
  have := goldbachG11MeshStep_pos n
  positivity

theorem goldbachG11MeshCell_subset (n : ℕ) (i : Fin (n + 1)) :
    Icc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)) ⊆
      Icc (4 / 53 : ℝ) (4 / 33) := by
  intro x hx
  exact ⟨(goldbachG11MeshPoint_bounds n (by omega : (i : ℕ) ≤ n + 1)).1.trans hx.1,
    hx.2.trans (goldbachG11MeshPoint_bounds n (by omega : (i : ℕ) + 1 ≤ n + 1)).2⟩

theorem goldbachG11Mesh_exists_cell (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (4 / 53 : ℝ) (4 / 33)) :
    ∃ i : Fin (n + 1),
      x ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)) := by
  have hend : x ≤ 4 / 53 + ((n + 1 : ℕ) : ℝ) * goldbachG11MeshStep n := by
    change x ≤ goldbachG11MeshPoint n (n + 1)
    rw [goldbachG11MeshPoint_end]
    exact hx.2
  obtain ⟨i, hi, hl, hu⟩ :=
    LiuWeight.exists_nat_cell (n + 1) (goldbachG11MeshStep_pos n) hx.1 hend
  exact ⟨⟨i, hi⟩, hl, hu⟩

theorem goldbachG11Mesh_index_mono {n : ℕ} {i j : Fin (n + 1)} {x y : ℝ}
    (hx : x ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))
    (hy : y ∈ Ioc (goldbachG11MeshPoint n j) (goldbachG11MeshPoint n (j + 1)))
    (hxy : x ≤ y) : i ≤ j := by
  by_contra h
  have hji : (j : ℕ) + 1 ≤ i := by
    have : j < i := lt_of_not_ge h
    exact Nat.succ_le_of_lt this
  have hle := (goldbachG11MeshPoint_strictMono n).monotone hji
  linarith [hx.1, hy.2]

def goldbachG11MeshSup (h : ℝ → ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  sSup (h '' Icc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))

def goldbachG11MeshCoeff (h : ℝ → ℝ) (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) : ℝ :=
  goldbachG11MeshSup h n j.1.1 / goldbachG11MeshPoint n j.1.2

theorem goldbachG11MeshSup_attained (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (n : ℕ) (i : Fin (n + 1)) :
    ∃ x ∈ Icc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)),
      h x = goldbachG11MeshSup h n i := by
  exact (isCompact_Icc.image_of_continuousOn
    (hh.mono (goldbachG11MeshCell_subset n i))).sSup_mem
      ((Set.nonempty_Icc.mpr
        ((goldbachG11MeshPoint_strictMono n) (Nat.lt_succ_self _)).le).image h)

theorem goldbachG11MeshSup_le (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (n : ℕ) (i : Fin (n + 1)) {M : ℝ}
    (hM : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ M) :
    goldbachG11MeshSup h n i ≤ M := by
  obtain ⟨x, hx, he⟩ := goldbachG11MeshSup_attained h hh n i
  rw [← he]
  exact hM x (goldbachG11MeshCell_subset n i hx)

theorem goldbachG11MeshCoeff_nonneg (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (n : ℕ) (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    0 ≤ goldbachG11MeshCoeff h n j := by
  obtain ⟨x, hx, he⟩ := goldbachG11MeshSup_attained h hh n j.1.1
  unfold goldbachG11MeshCoeff
  rw [← he]
  exact div_nonneg (hpos x (goldbachG11MeshCell_subset n j.1.1 hx))
    (goldbachG11MeshPoint_pos _ _).le

theorem goldbachG11MeshCoeff_majorant (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (n : ℕ) (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    {r q : ℝ} (hr : r ∈ Ioc (goldbachG11MeshLo n j 0) (goldbachG11MeshHi n j 0))
    (hq : q ∈ Ioc (goldbachG11MeshLo n j 1) (goldbachG11MeshHi n j 1)) :
    h r / q ≤ goldbachG11MeshCoeff h n j := by
  have hr' : r ∈ Icc (goldbachG11MeshPoint n j.1.1)
      (goldbachG11MeshPoint n (j.1.1 + 1)) := ⟨hr.1.le, hr.2⟩
  have hsup : h r ≤ goldbachG11MeshSup h n j.1.1 :=
    le_csSup (isCompact_Icc.bddAbove_image (hh.mono (goldbachG11MeshCell_subset n j.1.1)))
      (mem_image_of_mem h hr')
  have hq' : goldbachG11MeshPoint n j.1.2 < q := hq.1
  exact (div_le_div_of_nonneg_left
    (hpos r (goldbachG11MeshCell_subset n j.1.1 hr'))
    (goldbachG11MeshPoint_pos _ _) hq'.le).trans
      (div_le_div_of_nonneg_right hsup (goldbachG11MeshPoint_pos _ _).le)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig