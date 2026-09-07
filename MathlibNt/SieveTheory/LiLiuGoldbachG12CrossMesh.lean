import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelLimit
import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelMeshLimit

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG12HighMeshStep (n : ℕ) : ℝ :=
  ((3 / 11 : ℝ) - 4 / 33) / (n + 1)

def goldbachG12HighMeshPoint (n i : ℕ) : ℝ :=
  4 / 33 + i * goldbachG12HighMeshStep n

theorem goldbachG12HighMeshStep_pos (n : ℕ) : 0 < goldbachG12HighMeshStep n := by
  unfold goldbachG12HighMeshStep
  positivity

theorem goldbachG12HighMeshPoint_succ (n i : ℕ) :
    goldbachG12HighMeshPoint n (i + 1) =
      goldbachG12HighMeshPoint n i + goldbachG12HighMeshStep n := by
  simp only [goldbachG12HighMeshPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem goldbachG12HighMeshPoint_strictMono (n : ℕ) :
    StrictMono (goldbachG12HighMeshPoint n) := by
  intro i j hij
  unfold goldbachG12HighMeshPoint
  have := mul_lt_mul_of_pos_right (show (i : ℝ) < j by exact_mod_cast hij)
    (goldbachG12HighMeshStep_pos n)
  linarith

theorem goldbachG12HighMeshPoint_end (n : ℕ) :
    goldbachG12HighMeshPoint n (n + 1) = 3 / 11 := by
  unfold goldbachG12HighMeshPoint goldbachG12HighMeshStep
  push_cast
  field_simp
  ring

theorem goldbachG12HighMeshPoint_bounds (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) :
    goldbachG12HighMeshPoint n i ∈ Icc (4 / 33 : ℝ) (3 / 11) := by
  constructor
  · exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (goldbachG12HighMeshStep_pos n).le)
  · rw [← goldbachG12HighMeshPoint_end n]
    exact (goldbachG12HighMeshPoint_strictMono n).monotone hi

theorem goldbachG12HighMeshPoint_pos (n i : ℕ) :
    0 < goldbachG12HighMeshPoint n i := by
  unfold goldbachG12HighMeshPoint
  have := goldbachG12HighMeshStep_pos n
  positivity

theorem goldbachG12HighMeshCell_subset (n : ℕ) (i : Fin (n + 1)) :
    Icc (goldbachG12HighMeshPoint n i) (goldbachG12HighMeshPoint n (i + 1)) ⊆
      Icc (4 / 33 : ℝ) (3 / 11) := by
  intro x hx
  exact ⟨(goldbachG12HighMeshPoint_bounds n (by omega : (i : ℕ) ≤ n + 1)).1.trans hx.1,
    hx.2.trans (goldbachG12HighMeshPoint_bounds n (by omega : (i : ℕ) + 1 ≤ n + 1)).2⟩

theorem goldbachG12HighMesh_exists_cell (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (4 / 33 : ℝ) (3 / 11)) :
    ∃ i : Fin (n + 1),
      x ∈ Ioc (goldbachG12HighMeshPoint n i) (goldbachG12HighMeshPoint n (i + 1)) := by
  have hend : x ≤ 4 / 33 + ((n + 1 : ℕ) : ℝ) * goldbachG12HighMeshStep n := by
    change x ≤ goldbachG12HighMeshPoint n (n + 1)
    rw [goldbachG12HighMeshPoint_end]
    exact hx.2
  obtain ⟨i, hi, hl, hu⟩ :=
    LiuWeight.exists_nat_cell (n + 1) (goldbachG12HighMeshStep_pos n) hx.1 hend
  exact ⟨⟨i, hi⟩, hl, hu⟩

theorem goldbachG12HighMesh_index_mono {n : ℕ} {i j : Fin (n + 1)} {x y : ℝ}
    (hx : x ∈ Ioc (goldbachG12HighMeshPoint n i) (goldbachG12HighMeshPoint n (i + 1)))
    (hy : y ∈ Ioc (goldbachG12HighMeshPoint n j) (goldbachG12HighMeshPoint n (j + 1)))
    (hxy : x ≤ y) : i ≤ j := by
  by_contra h
  have hji : (j : ℕ) + 1 ≤ i := by
    have : j < i := lt_of_not_ge h
    exact Nat.succ_le_of_lt this
  have hle := (goldbachG12HighMeshPoint_strictMono n).monotone hji
  linarith [hx.1, hy.2]


/-- Only the first three coordinates are ordered. -/
def goldbachG12MeshCells (n : ℕ) :
    Finset ((Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :=
  Finset.univ.filter fun j => j.1.1 ≤ j.1.2 ∧ j.1.2 ≤ j.2.1

def goldbachG12MeshLo (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : ℝ :=
  if i = 3 then goldbachG12HighMeshPoint n (goldbachG11MeshCoords j i).val
  else goldbachG11MeshPoint n (goldbachG11MeshCoords j i).val

def goldbachG12MeshHi (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : ℝ :=
  if i = 3 then goldbachG12HighMeshPoint n ((goldbachG11MeshCoords j i).val + 1)
  else goldbachG11MeshPoint n ((goldbachG11MeshCoords j i).val + 1)

theorem goldbachG12MeshLo_pos (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : 0 < goldbachG12MeshLo n j i := by
  unfold goldbachG12MeshLo
  split_ifs
  · exact goldbachG12HighMeshPoint_pos _ _
  · exact goldbachG11MeshPoint_pos _ _

theorem goldbachG12MeshLo_lt_hi (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    (i : Fin 4) : goldbachG12MeshLo n j i < goldbachG12MeshHi n j i := by
  unfold goldbachG12MeshLo goldbachG12MeshHi
  split_ifs
  · exact goldbachG12HighMeshPoint_strictMono n (Nat.lt_succ_self _)
  · exact goldbachG11MeshPoint_strictMono n (Nat.lt_succ_self _)

/-- The closed original cross is covered without enlarging its geometric domain. -/
theorem goldbachG12Labels_subset_primeBox (N : ℕ) :
    goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ)) ⊆
      goldbachG11PrimeBox N ![4 / 53, 4 / 53, 4 / 53, 4 / 33]
        ![4 / 33, 4 / 33, 4 / 33, 3 / 11] := by
  rintro ⟨t, s, r, q⟩ hv
  obtain ⟨hr, hq, hs, ht, _, hl, hrq, hqs, hsb, hbt, htc⟩ :=
    mem_goldbachG12Labels_iff.mp hv
  have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
  have hrl := (goldbachG11_prime_lower_cutoff_iff N r hr).mp hl
  have htl := (goldbachG12_prime_cross_cutoff_iff N t ht).mp hbt
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  exact ⟨⟨ht, htl, htc⟩, ⟨hs, (hrl.trans_le hrqR).trans_le hqsR, hsb⟩,
    ⟨hr, hrl, hrqR.trans (hqsR.trans hsb)⟩, hq, hrl.trans_le hrqR, hqsR.trans hsb⟩

def goldbachG12MeshBox : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Ioc (4 / 53) (4 / 33) ×ˢ Ioc (4 / 53) (4 / 33)) ×ˢ
    (Ioc (4 / 53) (4 / 33) ×ˢ Ioc (4 / 33) (3 / 11))

def goldbachG12MeshAmbient : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Icc (4 / 53) (4 / 33) ×ˢ Icc (4 / 53) (4 / 33)) ×ˢ
    (Icc (4 / 53) (4 / 33) ×ˢ Icc (4 / 33) (3 / 11))

def goldbachG12MeshSource : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {x | x ∈ goldbachG12MeshBox ∧ x.1.1 ≤ x.1.2 ∧ x.1.2 ≤ x.2.1}

def goldbachG12MeshCell (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Ioc (goldbachG12MeshLo n j 0) (goldbachG12MeshHi n j 0) ×ˢ
    Ioc (goldbachG12MeshLo n j 1) (goldbachG12MeshHi n j 1)) ×ˢ
  (Ioc (goldbachG12MeshLo n j 2) (goldbachG12MeshHi n j 2) ×ˢ
    Ioc (goldbachG12MeshLo n j 3) (goldbachG12MeshHi n j 3))

def goldbachG12MeshRegion (n : ℕ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ⋃ j ∈ goldbachG12MeshCells n, goldbachG12MeshCell n j

theorem measurableSet_goldbachG12MeshCell (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    MeasurableSet (goldbachG12MeshCell n j) :=
  (measurableSet_Ioc.prod measurableSet_Ioc).prod
    (measurableSet_Ioc.prod measurableSet_Ioc)

theorem measurableSet_goldbachG12MeshAmbient : MeasurableSet goldbachG12MeshAmbient :=
  (measurableSet_Icc.prod measurableSet_Icc).prod
    (measurableSet_Icc.prod measurableSet_Icc)

theorem isCompact_goldbachG12MeshAmbient : IsCompact goldbachG12MeshAmbient :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

theorem measurableSet_goldbachG12MeshSource : MeasurableSet goldbachG12MeshSource := by
  have hr : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.1) := by fun_prop
  have hq : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.2) := by fun_prop
  have hs : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.2.1) := by fun_prop
  apply MeasurableSet.inter
    ((measurableSet_Ioc.prod measurableSet_Ioc).prod
      (measurableSet_Ioc.prod measurableSet_Ioc))
  exact (measurableSet_le hr hq).inter
    (measurableSet_le hq hs)

theorem goldbachG12MeshBox_subset_ambient : goldbachG12MeshBox ⊆ goldbachG12MeshAmbient := by
  intro x hx
  exact ⟨⟨⟨hx.1.1.1.le, hx.1.1.2⟩, ⟨hx.1.2.1.le, hx.1.2.2⟩⟩,
    ⟨⟨hx.2.1.1.le, hx.2.1.2⟩, ⟨hx.2.2.1.le, hx.2.2.2⟩⟩⟩

theorem goldbachG12MeshCell_subset_box (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    goldbachG12MeshCell n j ⊆ goldbachG12MeshBox := by
  have h (i : Fin (n + 1)) {x : ℝ}
      (hx : x ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1))) :
      x ∈ Ioc (4 / 53 : ℝ) (4 / 33) :=
    ⟨(goldbachG11MeshPoint_bounds n (by omega : (i : ℕ) ≤ n + 1)).1.trans_lt hx.1,
      (goldbachG11MeshCell_subset n i ⟨hx.1.le, hx.2⟩).2⟩
  intro x hx
  have ht : x.2.2 ∈ Ioc (4 / 33 : ℝ) (3 / 11) :=
    ⟨(goldbachG12HighMeshPoint_bounds n (by omega : (j.2.2 : ℕ) ≤ n + 1)).1.trans_lt hx.2.2.1,
      (goldbachG12HighMeshCell_subset n j.2.2 ⟨hx.2.2.1.le, hx.2.2.2⟩).2⟩
  exact ⟨⟨h j.1.1 hx.1.1, h j.1.2 hx.1.2⟩, ⟨h j.2.1 hx.2.1, ht⟩⟩

theorem goldbachG12MeshCell_unique {n : ℕ}
    {j k : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hj : x ∈ goldbachG12MeshCell n j) (hk : x ∈ goldbachG12MeshCell n k) : j = k := by
  have h {i l : Fin (n + 1)} {y : ℝ}
      (hi : y ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))
      (hl : y ∈ Ioc (goldbachG11MeshPoint n l) (goldbachG11MeshPoint n (l + 1))) : i = l :=
    le_antisymm (goldbachG11Mesh_index_mono hi hl le_rfl)
      (goldbachG11Mesh_index_mono hl hi le_rfl)
  have ht : j.2.2 = k.2.2 := le_antisymm
    (goldbachG12HighMesh_index_mono hj.2.2 hk.2.2 le_rfl)
    (goldbachG12HighMesh_index_mono hk.2.2 hj.2.2 le_rfl)
  exact Prod.ext (Prod.ext (h hj.1.1 hk.1.1) (h hj.1.2 hk.1.2))
    (Prod.ext (h hj.2.1 hk.2.1) ht)

theorem goldbachG12MeshBox_cover (n : ℕ) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG12MeshBox) :
    ∃ j, x ∈ goldbachG12MeshCell n j := by
  obtain ⟨i, hi⟩ := goldbachG11Mesh_exists_cell n hx.1.1
  obtain ⟨j, hj⟩ := goldbachG11Mesh_exists_cell n hx.1.2
  obtain ⟨k, hk⟩ := goldbachG11Mesh_exists_cell n hx.2.1
  obtain ⟨l, hl⟩ := goldbachG12HighMesh_exists_cell n hx.2.2
  exact ⟨((i, j), (k, l)), ⟨hi, hj⟩, ⟨hk, hl⟩⟩

theorem goldbachG12MeshSource_cover (n : ℕ) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG12MeshSource) :
    ∃ j ∈ goldbachG12MeshCells n, x ∈ goldbachG12MeshCell n j := by
  obtain ⟨j, hj⟩ := goldbachG12MeshBox_cover n hx.1
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
  exact ⟨goldbachG11Mesh_index_mono hj.1.1 hj.1.2 hx.2.1,
    goldbachG11Mesh_index_mono hj.1.2 hj.2.1 hx.2.2⟩

theorem goldbachG12MeshCell_order_error {n : ℕ}
    {j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    (hj : j ∈ goldbachG12MeshCells n) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG12MeshCell n j) :
    x.1.1 < x.1.2 + goldbachG11MeshStep n ∧
      x.1.2 < x.2.1 + goldbachG11MeshStep n := by
  have h {i k : Fin (n + 1)} {u v : ℝ} (hik : i ≤ k)
      (hu : u ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))
      (hv : v ∈ Ioc (goldbachG11MeshPoint n k) (goldbachG11MeshPoint n (k + 1))) :
      u < v + goldbachG11MeshStep n := by
    have hm := (goldbachG11MeshPoint_strictMono n).monotone hik
    rw [goldbachG11MeshPoint_succ] at hu
    linarith [hu.2, hv.1]
  have hs := (Finset.mem_filter.mp hj).2
  exact ⟨h hs.1 hx.1.1 hx.1.2, h hs.2 hx.1.2 hx.2.1⟩

theorem goldbachG12Mesh_prime_cover (n N : ℕ) (hN : 4 ≤ N)
    (v : GoldbachG11Label)
    (hv : v ∈ goldbachG12Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ)) ((N : ℝ) ^ (3 / 11 : ℝ))) :
    ∃ j ∈ goldbachG12MeshCells n,
      v ∈ goldbachG11PrimeBox N (goldbachG12MeshLo n j) (goldbachG12MeshHi n j) := by
  rcases v with ⟨t, s, r, q⟩
  have hp := goldbachG12Labels_subset_primeBox N hv
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval] at hp
  have hN' : 1 < N := by omega
  have hr := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.1.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.2.1.2
  have hq := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.2.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.2.2.2
  have hs := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.1.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.1.2
  have ht := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.1.1.pos
    (4 / 33) (3 / 11)).mpr hp.1.2
  have hm {u w : ℕ} (hu : 0 < u) (huw : u ≤ w) :
      LiuWeight.primeLogExponent N u ≤ LiuWeight.primeLogExponent N w := by
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huw))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  obtain ⟨_, _, _, _, _, _, hrq, hqs, _, _, _⟩ := mem_goldbachG12Labels_iff.mp hv
  obtain ⟨j, hj, hx⟩ := goldbachG12MeshSource_cover n
    (x := ((LiuWeight.primeLogExponent N r, LiuWeight.primeLogExponent N q),
      (LiuWeight.primeLogExponent N s, LiuWeight.primeLogExponent N t)))
    ⟨⟨⟨hr, hq⟩, ⟨hs, ht⟩⟩, hm hp.2.2.1.1.pos hrq, hm hp.2.2.2.1.pos hqs⟩
  refine ⟨j, hj, ?_⟩
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval]
  exact ⟨⟨hp.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.1.1.pos _ _).mp hx.2.2⟩,
    ⟨hp.2.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.1.1.pos _ _).mp hx.2.1⟩,
    ⟨hp.2.2.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.1.1.pos _ _).mp hx.1.1⟩,
    ⟨hp.2.2.2.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.2.1.pos _ _).mp hx.1.2⟩⟩

def goldbachG12MeshDensity (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  LiuWeight.liuLogDensity x.1 * LiuWeight.liuLogDensity x.2

def goldbachG12MeshIntegrand (h : ℝ → ℝ) (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (h x.1.1 / x.1.2) * goldbachG12MeshDensity x

theorem continuousOn_goldbachG12MeshDensity :
    ContinuousOn goldbachG12MeshDensity goldbachG12MeshAmbient := by
  unfold goldbachG12MeshDensity LiuWeight.liuLogDensity
  apply ContinuousOn.mul
  · refine continuousOn_const.div (by fun_prop) ?_
    intro x hx
    exact mul_ne_zero (by linarith [hx.1.1.1]) (by linarith [hx.1.2.1])
  · refine continuousOn_const.div (by fun_prop) ?_
    intro x hx
    exact mul_ne_zero (by linarith [hx.2.1.1]) (by linarith [hx.2.2.1])

theorem goldbachG12MeshDensity_nonneg {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG12MeshAmbient) : 0 ≤ goldbachG12MeshDensity x := by
  have hr : 0 ≤ x.1.1 := by linarith [hx.1.1.1]
  have hq : 0 ≤ x.1.2 := by linarith [hx.1.2.1]
  have hs : 0 ≤ x.2.1 := by linarith [hx.2.1.1]
  have ht : 0 ≤ x.2.2 := by linarith [hx.2.2.1]
  exact mul_nonneg (div_nonneg zero_le_one (mul_nonneg hr hq))
    (div_nonneg zero_le_one (mul_nonneg hs ht))

theorem integrableOn_goldbachG12MeshDensity {s : Set ((ℝ × ℝ) × (ℝ × ℝ))}
    (hs : MeasurableSet s) (hsub : s ⊆ goldbachG12MeshAmbient) :
    IntegrableOn goldbachG12MeshDensity s := by
  exact continuousOn_goldbachG12MeshDensity.integrableOn_of_subset_isCompact
    isCompact_goldbachG12MeshAmbient hs hsub
      (lt_of_le_of_lt (measure_mono hsub) isCompact_goldbachG12MeshAmbient.measure_lt_top).ne

theorem integrable_goldbachG12MeshSource (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    Integrable (goldbachG12MeshSource.indicator (goldbachG12MeshIntegrand h)) := by
  have hc : ContinuousOn (goldbachG12MeshIntegrand h) goldbachG12MeshAmbient := by
    apply ContinuousOn.mul
    · refine (hh.comp (by fun_prop) (fun _ hx => hx.1.1)).div (by fun_prop) ?_
      intro x hx
      linarith [hx.1.2.1]
    · exact continuousOn_goldbachG12MeshDensity
  have hsub : goldbachG12MeshSource ⊆ goldbachG12MeshAmbient :=
    fun _ hx => goldbachG12MeshBox_subset_ambient hx.1
  exact (integrable_indicator_iff measurableSet_goldbachG12MeshSource).mpr
    (hc.integrableOn_of_subset_isCompact isCompact_goldbachG12MeshAmbient
      measurableSet_goldbachG12MeshSource hsub
        (lt_of_le_of_lt (measure_mono hsub) isCompact_goldbachG12MeshAmbient.measure_lt_top).ne)

theorem goldbachG12LogBoxMass_eq_meshIntegral (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    goldbachG11LogBoxMass (goldbachG12MeshLo n j) (goldbachG12MeshHi n j) =
      ∫ x in goldbachG12MeshCell n j, goldbachG12MeshDensity x := by
  unfold goldbachG12MeshCell goldbachG12MeshDensity
  rw [Measure.volume_eq_prod (ℝ × ℝ) (ℝ × ℝ), setIntegral_prod_mul]
  unfold goldbachG11LogBoxMass
  have hp (i : Fin 4) : 0 < goldbachG12MeshLo n j i := goldbachG12MeshLo_pos _ _ _
  have hl (i : Fin 4) : goldbachG12MeshLo n j i < goldbachG12MeshHi n j i :=
    goldbachG12MeshLo_lt_hi _ _ _
  rw [LiuWeight.logarithmicRectangleMass_eq_setIntegral (hp 0) (hl 0) (hp 1) (hl 1),
    LiuWeight.logarithmicRectangleMass_eq_setIntegral (hp 2) (hl 2) (hp 3) (hl 3)]

private theorem g12_integral_four (F : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (hF : Integrable F) :
    (∫ x, F x) = ∫ r : ℝ, ∫ q : ℝ, ∫ s : ℝ, ∫ t : ℝ, F ((r, q), (s, t)) := by
  simp only [Measure.volume_eq_prod] at hF ⊢
  rw [integral_prod F hF, integral_prod _ hF.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hF.prod_right_ae] with r hr
  apply integral_congr_ae
  filter_upwards [hr] with q hq
  exact integral_prod _ hq

theorem goldbachG12MeshSource_mem_iff (r q s t : ℝ) :
    ((r, q), (s, t)) ∈ goldbachG12MeshSource ↔
      r ∈ Ioc (4 / 53 : ℝ) (4 / 33) ∧ q ∈ Icc r (4 / 33) ∧
        s ∈ Icc q (4 / 33) ∧ t ∈ Ioc (4 / 33 : ℝ) (3 / 11) := by
  constructor
  · intro hx
    exact ⟨hx.1.1.1, ⟨hx.2.1, hx.1.1.2.2⟩,
      ⟨hx.2.2, hx.1.2.1.2⟩, hx.1.2.2⟩
  · rintro ⟨hr, hq, hs, ht⟩
    exact ⟨⟨⟨hr, ⟨hr.1.trans_le hq.1, hq.2⟩⟩,
      ⟨⟨(hr.1.trans_le hq.1).trans_le hs.1, hs.2⟩,
        ht⟩⟩,
      hq.1, hs.1⟩

private theorem g12_source_indicator (f : ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ) (r q s t : ℝ) :
    goldbachG12MeshSource.indicator f ((r, q), (s, t)) =
      (Ioc (4 / 53 : ℝ) (4 / 33)).indicator (fun r =>
        (Icc r (4 / 33)).indicator (fun q =>
          (Icc q (4 / 33)).indicator (fun s =>
            (Ioc (4 / 33 : ℝ) (3 / 11)).indicator (fun t => f ((r, q), (s, t))) t) s) q) r := by
  classical
  simp only [Set.indicator_apply, goldbachG12MeshSource_mem_iff]
  split_ifs <;> simp_all

private theorem g12_integral_parameter_indicator (s : Set ℝ) (x : ℝ) (f : ℝ → ℝ → ℝ) :
    (∫ y, s.indicator (fun x => f x y) x) = s.indicator (fun x => ∫ y, f x y) x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx]

theorem goldbachG12PrimeIntegral_eq_meshSource (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) :
    goldbachG12PrimeIntegral h =
      ∫ x, goldbachG12MeshSource.indicator (goldbachG12MeshIntegrand h) x := by
  rw [g12_integral_four _ (integrable_goldbachG12MeshSource h hh)]
  simp_rw [g12_source_indicator, g12_integral_parameter_indicator,
    integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioc]
  unfold goldbachG12PrimeIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (4 / 53 : ℝ) ≤ 4 / 33)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr.2]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro q hq
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hq.2]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s _hs
  dsimp only
  rw [intervalIntegral.integral_of_le (by norm_num : (4 / 33 : ℝ) ≤ 3 / 11)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  simp only [goldbachG12MeshIntegrand, goldbachG12MeshDensity, LiuWeight.liuLogDensity,
    div_eq_mul_inv, mul_inv, pow_two]
  ring

def goldbachG12MeshUpperIntegrand (h : ℝ → ℝ) (n : ℕ)
    (x : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  ∑ j ∈ goldbachG12MeshCells n,
    goldbachG11MeshCoeff h n j * (goldbachG12MeshCell n j).indicator goldbachG12MeshDensity x

def goldbachG12MeshUpperSum (h : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ goldbachG12MeshCells n, goldbachG11MeshCoeff h n j *
    goldbachG11LogBoxMass (goldbachG12MeshLo n j) (goldbachG12MeshHi n j)

theorem tendsto_goldbachG12MeshCoeff (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (j : ∀ n : ℕ, (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1)))
    {x : (ℝ × ℝ) × (ℝ × ℝ)} (hx : ∀ n, x ∈ goldbachG12MeshCell n (j n)) :
    Tendsto (fun n => goldbachG11MeshCoeff h n (j n)) atTop (nhds (h x.1.1 / x.1.2)) := by
  have hr := tendsto_goldbachG11MeshSup h hh (fun n => (j n).1.1)
    (fun n => ⟨(hx n).1.1.1.le, (hx n).1.1.2⟩)
  have hq := tendsto_goldbachG11Mesh_sameCell (fun n => (j n).1.2)
    (fun n => goldbachG11MeshPoint n (j n).1.2)
    (fun n => ⟨(hx n).1.2.1.le, (hx n).1.2.2⟩)
    (fun n => ⟨le_rfl, ((goldbachG11MeshPoint_strictMono n) (Nat.lt_succ_self _)).le⟩)
  have hqpos : 0 < x.1.2 :=
    (goldbachG11MeshPoint_pos 0 (j 0).1.2).trans (hx 0).1.2.1
  exact hr.div hq hqpos.ne'

theorem integrable_goldbachG12MeshUpperIntegrand (h : ℝ → ℝ) (n : ℕ) :
    Integrable (goldbachG12MeshUpperIntegrand h n) := by
  exact integrable_finsetSum _ fun j _ =>
    ((integrableOn_goldbachG12MeshDensity (measurableSet_goldbachG12MeshCell n j)
      (fun _ hx => goldbachG12MeshBox_subset_ambient
        (goldbachG12MeshCell_subset_box n j hx))).integrable_indicator
      (measurableSet_goldbachG12MeshCell n j)).const_mul _

theorem goldbachG12MeshUpperSum_eq_integral (h : ℝ → ℝ) (n : ℕ) :
    goldbachG12MeshUpperSum h n = ∫ x, goldbachG12MeshUpperIntegrand h n x := by
  unfold goldbachG12MeshUpperSum goldbachG12MeshUpperIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, integral_indicator (measurableSet_goldbachG12MeshCell n j),
      goldbachG12LogBoxMass_eq_meshIntegral]
  · intro j _
    exact ((integrableOn_goldbachG12MeshDensity (measurableSet_goldbachG12MeshCell n j)
      (fun _ hx => goldbachG12MeshBox_subset_ambient
        (goldbachG12MeshCell_subset_box n j hx))).integrable_indicator
      (measurableSet_goldbachG12MeshCell n j)).const_mul _

theorem goldbachG12MeshUpperIntegrand_eq_of_mem (h : ℝ → ℝ) {n : ℕ}
    {j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    (hj : j ∈ goldbachG12MeshCells n) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG12MeshCell n j) :
    goldbachG12MeshUpperIntegrand h n x = goldbachG11MeshCoeff h n j * goldbachG12MeshDensity x := by
  classical
  unfold goldbachG12MeshUpperIntegrand
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hx]
  · intro k _ hkj
    rw [indicator_of_notMem (fun hk => hkj (goldbachG12MeshCell_unique hk hx)), mul_zero]
  · exact fun h => (h hj).elim

theorem goldbachG12MeshUpperIntegrand_eq_zero (h : ℝ → ℝ) {n : ℕ}
    {x : (ℝ × ℝ) × (ℝ × ℝ)} (hx : x ∉ goldbachG12MeshRegion n) :
    goldbachG12MeshUpperIntegrand h n x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  rw [indicator_of_notMem (fun h => hx (Set.mem_iUnion₂.mpr ⟨j, hj, h⟩)), mul_zero]

theorem goldbachG12MeshRegion_eventually_not_mem {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∉ goldbachG12MeshSource) :
    ∀ᶠ n : ℕ in atTop, x ∉ goldbachG12MeshRegion n := by
  by_cases hb : x ∈ goldbachG12MeshBox
  · have ho : ¬ (x.1.1 ≤ x.1.2 ∧ x.1.2 ≤ x.2.1) :=
      fun ho => hx ⟨hb, ho⟩
    simp only [not_and_or, not_le] at ho
    rcases ho with hrq | hqs
    · filter_upwards [tendsto_goldbachG11MeshStep.eventually
        (gt_mem_nhds (sub_pos.mpr hrq))] with n hn
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      have he := goldbachG12MeshCell_order_error hj hxj
      linarith [he.1]
    · filter_upwards [tendsto_goldbachG11MeshStep.eventually
        (gt_mem_nhds (sub_pos.mpr hqs))] with n hn
      intro hmem
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
      have he := goldbachG12MeshCell_order_error hj hxj
      linarith [he.2]
  · apply Eventually.of_forall
    intro n hmem
    obtain ⟨j, _, hxj⟩ := Set.mem_iUnion₂.mp hmem
    exact hb (goldbachG12MeshCell_subset_box n j hxj)

theorem tendsto_goldbachG12MeshUpperIntegrand (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33))) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    Tendsto (fun n => goldbachG12MeshUpperIntegrand h n x) atTop
      (nhds (goldbachG12MeshSource.indicator (goldbachG12MeshIntegrand h) x)) := by
  by_cases hx : x ∈ goldbachG12MeshSource
  · choose j hj hxj using fun n => goldbachG12MeshSource_cover n hx
    rw [indicator_of_mem hx]
    exact ((tendsto_goldbachG12MeshCoeff h hh j hxj).mul_const
      (goldbachG12MeshDensity x)).congr
        (fun n => (goldbachG12MeshUpperIntegrand_eq_of_mem h (hj n) (hxj n)).symm)
  · rw [indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [goldbachG12MeshRegion_eventually_not_mem hx] with n hn
    exact (goldbachG12MeshUpperIntegrand_eq_zero h hn).symm

theorem goldbachG12MeshUpperIntegrand_dominated (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ M)
    (n : ℕ) (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖goldbachG12MeshUpperIntegrand h n x‖ ≤
      (M / (4 / 53)) * goldbachG12MeshAmbient.indicator goldbachG12MeshDensity x := by
  by_cases hx : x ∈ goldbachG12MeshRegion n
  · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    have hb := goldbachG12MeshBox_subset_ambient (goldbachG12MeshCell_subset_box n j hxj)
    have hd := goldbachG12MeshDensity_nonneg hb
    rw [goldbachG12MeshUpperIntegrand_eq_of_mem h hj hxj, indicator_of_mem hb,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (goldbachG11MeshCoeff_nonneg h hh hpos n j) hd)]
    exact mul_le_mul_of_nonneg_right (goldbachG11MeshCoeff_le h hh hM0 hM n j) hd
  · rw [goldbachG12MeshUpperIntegrand_eq_zero h hx, norm_zero]
    apply mul_nonneg (div_nonneg hM0 (by norm_num))
    by_cases hb : x ∈ goldbachG12MeshAmbient
    · rw [indicator_of_mem hb]
      exact goldbachG12MeshDensity_nonneg hb
    · rw [indicator_of_notMem hb]

theorem tendsto_goldbachG12MeshUpperSum (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x) :
    Tendsto (goldbachG12MeshUpperSum h) atTop (nhds (goldbachG12PrimeIntegral h)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hh
  have hb : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), h x ≤ max 0 M :=
    fun x hx => (hM (mem_image_of_mem h hx)).trans (le_max_right _ _)
  rw [goldbachG12PrimeIntegral_eq_meshSource h hh]
  change Tendsto (fun n => goldbachG12MeshUpperSum h n) atTop _
  simp only [goldbachG12MeshUpperSum_eq_integral]
  apply tendsto_integral_of_dominated_convergence
    (fun x => (max 0 M / (4 / 53)) *
      goldbachG12MeshAmbient.indicator goldbachG12MeshDensity x)
  · exact fun n => (integrable_goldbachG12MeshUpperIntegrand h n).aestronglyMeasurable
  · exact ((integrableOn_goldbachG12MeshDensity measurableSet_goldbachG12MeshAmbient
      Subset.rfl).integrable_indicator measurableSet_goldbachG12MeshAmbient).const_mul _
  · exact fun n => Eventually.of_forall
      (goldbachG12MeshUpperIntegrand_dominated h hh hpos (le_max_left _ _) hb n)
  · exact Eventually.of_forall (tendsto_goldbachG12MeshUpperIntegrand h hh)

theorem goldbachG12MeshUpperSum_exists_le_integral (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (4 / 53 : ℝ) (4 / 33)))
    (hpos : ∀ x ∈ Icc (4 / 53 : ℝ) (4 / 33), 0 ≤ h x)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ n : ℕ, goldbachG12MeshUpperSum h n ≤ goldbachG12PrimeIntegral h + ν := by
  have he := (tendsto_goldbachG12MeshUpperSum h hh hpos).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ hν))
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨n, hn.le⟩


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
