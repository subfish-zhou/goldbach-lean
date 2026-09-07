import MathlibNt.SieveTheory.LiLiuGoldbachG11PrimeKernelMesh

open Filter MeasureTheory Set
open scoped BigOperators Topology Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11MeshBox : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Ioc (4 / 53) (4 / 33) ×ˢ Ioc (4 / 53) (4 / 33)) ×ˢ
    (Ioc (4 / 53) (4 / 33) ×ˢ Ioc (4 / 53) (4 / 33))

def goldbachG11MeshAmbient : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Icc (4 / 53) (4 / 33) ×ˢ Icc (4 / 53) (4 / 33)) ×ˢ
    (Icc (4 / 53) (4 / 33) ×ˢ Icc (4 / 53) (4 / 33))

def goldbachG11MeshSource : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {x | x ∈ goldbachG11MeshBox ∧ x.1.1 ≤ x.1.2 ∧ x.1.2 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}

def goldbachG11MeshCell (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (Ioc (goldbachG11MeshLo n j 0) (goldbachG11MeshHi n j 0) ×ˢ
    Ioc (goldbachG11MeshLo n j 1) (goldbachG11MeshHi n j 1)) ×ˢ
  (Ioc (goldbachG11MeshLo n j 2) (goldbachG11MeshHi n j 2) ×ˢ
    Ioc (goldbachG11MeshLo n j 3) (goldbachG11MeshHi n j 3))

def goldbachG11MeshRegion (n : ℕ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ⋃ j ∈ goldbachG11MeshCells n, goldbachG11MeshCell n j

theorem measurableSet_goldbachG11MeshCell (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    MeasurableSet (goldbachG11MeshCell n j) :=
  (measurableSet_Ioc.prod measurableSet_Ioc).prod
    (measurableSet_Ioc.prod measurableSet_Ioc)

theorem measurableSet_goldbachG11MeshAmbient : MeasurableSet goldbachG11MeshAmbient :=
  (measurableSet_Icc.prod measurableSet_Icc).prod
    (measurableSet_Icc.prod measurableSet_Icc)

theorem isCompact_goldbachG11MeshAmbient : IsCompact goldbachG11MeshAmbient :=
  (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)

theorem measurableSet_goldbachG11MeshSource : MeasurableSet goldbachG11MeshSource := by
  have hr : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.1) := by fun_prop
  have hq : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.2) := by fun_prop
  have hs : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.2.1) := by fun_prop
  have ht : Measurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.2.2) := by fun_prop
  apply MeasurableSet.inter
    ((measurableSet_Ioc.prod measurableSet_Ioc).prod
      (measurableSet_Ioc.prod measurableSet_Ioc))
  exact (measurableSet_le hr hq).inter
    ((measurableSet_le hq hs).inter (measurableSet_le hs ht))

theorem goldbachG11MeshBox_subset_ambient : goldbachG11MeshBox ⊆ goldbachG11MeshAmbient := by
  intro x hx
  exact ⟨⟨⟨hx.1.1.1.le, hx.1.1.2⟩, ⟨hx.1.2.1.le, hx.1.2.2⟩⟩,
    ⟨⟨hx.2.1.1.le, hx.2.1.2⟩, ⟨hx.2.2.1.le, hx.2.2.2⟩⟩⟩

theorem goldbachG11MeshCell_subset_box (n : ℕ)
    (j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))) :
    goldbachG11MeshCell n j ⊆ goldbachG11MeshBox := by
  have h (i : Fin (n + 1)) {x : ℝ}
      (hx : x ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1))) :
      x ∈ Ioc (4 / 53 : ℝ) (4 / 33) :=
    ⟨(goldbachG11MeshPoint_bounds n (by omega : (i : ℕ) ≤ n + 1)).1.trans_lt hx.1,
      (goldbachG11MeshCell_subset n i ⟨hx.1.le, hx.2⟩).2⟩
  intro x hx
  exact ⟨⟨h j.1.1 hx.1.1, h j.1.2 hx.1.2⟩, ⟨h j.2.1 hx.2.1, h j.2.2 hx.2.2⟩⟩

theorem goldbachG11MeshCell_unique {n : ℕ}
    {j k : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hj : x ∈ goldbachG11MeshCell n j) (hk : x ∈ goldbachG11MeshCell n k) : j = k := by
  have h {i l : Fin (n + 1)} {y : ℝ}
      (hi : y ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))
      (hl : y ∈ Ioc (goldbachG11MeshPoint n l) (goldbachG11MeshPoint n (l + 1))) : i = l :=
    le_antisymm (goldbachG11Mesh_index_mono hi hl le_rfl)
      (goldbachG11Mesh_index_mono hl hi le_rfl)
  exact Prod.ext (Prod.ext (h hj.1.1 hk.1.1) (h hj.1.2 hk.1.2))
    (Prod.ext (h hj.2.1 hk.2.1) (h hj.2.2 hk.2.2))

theorem goldbachG11MeshBox_cover (n : ℕ) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG11MeshBox) :
    ∃ j, x ∈ goldbachG11MeshCell n j := by
  obtain ⟨i, hi⟩ := goldbachG11Mesh_exists_cell n hx.1.1
  obtain ⟨j, hj⟩ := goldbachG11Mesh_exists_cell n hx.1.2
  obtain ⟨k, hk⟩ := goldbachG11Mesh_exists_cell n hx.2.1
  obtain ⟨l, hl⟩ := goldbachG11Mesh_exists_cell n hx.2.2
  exact ⟨((i, j), (k, l)), ⟨hi, hj⟩, ⟨hk, hl⟩⟩

theorem goldbachG11MeshSource_cover (n : ℕ) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG11MeshSource) :
    ∃ j ∈ goldbachG11MeshCells n, x ∈ goldbachG11MeshCell n j := by
  obtain ⟨j, hj⟩ := goldbachG11MeshBox_cover n hx.1
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
  exact ⟨goldbachG11Mesh_index_mono hj.1.1 hj.1.2 hx.2.1,
    goldbachG11Mesh_index_mono hj.1.2 hj.2.1 hx.2.2.1,
    goldbachG11Mesh_index_mono hj.2.1 hj.2.2 hx.2.2.2⟩

theorem goldbachG11MeshCell_order_error {n : ℕ}
    {j : (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))}
    (hj : j ∈ goldbachG11MeshCells n) {x : (ℝ × ℝ) × (ℝ × ℝ)}
    (hx : x ∈ goldbachG11MeshCell n j) :
    x.1.1 < x.1.2 + goldbachG11MeshStep n ∧
      x.1.2 < x.2.1 + goldbachG11MeshStep n ∧
        x.2.1 < x.2.2 + goldbachG11MeshStep n := by
  have h {i k : Fin (n + 1)} {u v : ℝ} (hik : i ≤ k)
      (hu : u ∈ Ioc (goldbachG11MeshPoint n i) (goldbachG11MeshPoint n (i + 1)))
      (hv : v ∈ Ioc (goldbachG11MeshPoint n k) (goldbachG11MeshPoint n (k + 1))) :
      u < v + goldbachG11MeshStep n := by
    have hm := (goldbachG11MeshPoint_strictMono n).monotone hik
    rw [goldbachG11MeshPoint_succ] at hu
    linarith [hu.2, hv.1]
  have hs := (Finset.mem_filter.mp hj).2
  exact ⟨h hs.1 hx.1.1 hx.1.2, h hs.2.1 hx.1.2 hx.2.1, h hs.2.2 hx.2.1 hx.2.2⟩

theorem goldbachG11Mesh_prime_cover (n N : ℕ) (hN : 4 ≤ N)
    (v : GoldbachG11Label)
    (hv : v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ))) :
    ∃ j ∈ goldbachG11MeshCells n,
      v ∈ goldbachG11PrimeBox N (goldbachG11MeshLo n j) (goldbachG11MeshHi n j) := by
  rcases v with ⟨t, s, r, q⟩
  have hp := goldbachG11Labels_subset_primeBox N hv
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval] at hp
  have hN' : 1 < N := by omega
  have hr := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.1.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.2.1.2
  have hq := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.2.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.2.2.2
  have hs := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.1.1.pos
    (4 / 53) (4 / 33)).mpr hp.2.1.2
  have ht := (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.1.1.pos
    (4 / 53) (4 / 33)).mpr hp.1.2
  have hm {u w : ℕ} (hu : 0 < u) (huw : u ≤ w) :
      LiuWeight.primeLogExponent N u ≤ LiuWeight.primeLogExponent N w := by
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huw))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  obtain ⟨_, _, _, _, _, _, hrq, hqs, hst, _⟩ := mem_goldbachG11Labels_iff.mp hv
  obtain ⟨j, hj, hx⟩ := goldbachG11MeshSource_cover n
    (x := ((LiuWeight.primeLogExponent N r, LiuWeight.primeLogExponent N q),
      (LiuWeight.primeLogExponent N s, LiuWeight.primeLogExponent N t)))
    ⟨⟨⟨hr, hq⟩, ⟨hs, ht⟩⟩, hm hp.2.2.1.1.pos hrq, hm hp.2.2.2.1.pos hqs,
      hm hp.2.1.1.pos hst⟩
  refine ⟨j, hj, ?_⟩
  simp only [goldbachG11PrimeBox, Finset.mem_sigma, mem_goldbachG11PrimeInterval]
  exact ⟨⟨hp.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.1.1.pos _ _).mp hx.2.2⟩,
    ⟨hp.2.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.1.1.pos _ _).mp hx.2.1⟩,
    ⟨hp.2.2.1.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.1.1.pos _ _).mp hx.1.1⟩,
    ⟨hp.2.2.2.1, (LiuWeight.primeLogExponent_mem_interval_iff hN' hp.2.2.2.1.pos _ _).mp hx.1.2⟩⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig