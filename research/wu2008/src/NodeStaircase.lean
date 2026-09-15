import NodeActual

namespace NodeExtension
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval BigOperators

/-- The nine original upper nodes, indexed from zero in Lean. -/
noncomputable def upperNode (i : Fin 9) : ℝ := (22 + (i.val : ℝ)) / 10

noncomputable def upperLeft (i : Fin 9) : ℝ := if i.val = 0 then 1 else (21 + (i.val : ℝ)) / 10

noncomputable def nineProfile (z : Fin 9 → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin 9, (Ioc (upperLeft i) (upperNode i)).indicator (fun _ => z i) t

noncomputable def actualNine (δ : ℝ) (i : Fin 9) : ℝ :=
  wuImprovementLimit true δ (upperNode i)

theorem upperNode_bounds (i : Fin 9) : 1 ≤ upperNode i ∧ upperNode i ≤ 3 := by
  have hi : (i.val : ℝ) ≤ 8 := by exact_mod_cast (show i.val ≤ 8 by omega)
  have hz : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [upperNode]
  constructor <;> linarith

theorem cells_separated {i j : Fin 9} (hij : i < j) : upperNode i ≤ upperLeft j := by
  have hj : j.val ≠ 0 := by intro h; have h' : i.val < j.val := hij; omega
  have hh : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val from hij)
  simp only [upperNode, upperLeft, if_neg hj]
  linarith

theorem cells_unique {i j : Fin 9} {t : ℝ}
    (hi : t ∈ Ioc (upperLeft i) (upperNode i))
    (hj : t ∈ Ioc (upperLeft j) (upperNode j)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have he := cells_separated h
    linarith [hi.2, hj.1]
  · exact h
  · have he := cells_separated h
    linarith [hj.2, hi.1]

theorem nineProfile_cell (z : Fin 9 → ℝ) {i : Fin 9} {t : ℝ}
    (ht : t ∈ Ioc (upperLeft i) (upperNode i)) : nineProfile z t = z i := by
  classical
  unfold nineProfile
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    exact indicator_of_notMem (fun hj => hji (cells_unique hj ht)) _
  · simp

theorem nineProfile_integrable (z : Fin 9 → ℝ) :
    IntervalIntegrable (nineProfile z) volume 1 3 := by
  classical
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mpr
  apply integrable_finsetSum
  intro i _
  exact (integrable_const (z i)).indicator measurableSet_Ioc

theorem nineProfile_nonneg {z : Fin 9 → ℝ} (hz : ∀ i, 0 ≤ z i) (t : ℝ) :
    0 ≤ nineProfile z t := by
  apply Finset.sum_nonneg
  intro i _
  exact indicator_nonneg (fun _ _ => hz i) t

theorem actualNine_nonneg {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) (i : Fin 9) :
    0 ≤ actualNine δ i :=
  wuImprovementLimit_nonneg true hd (by linarith : δ < 1 / 2)
    (upperNode_bounds i).1 ((upperNode_bounds i).2.trans (by norm_num))

theorem nineProfile_le_actual {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    nineProfile (actualNine δ) t ≤ wuImprovementLimit true δ t := by
  classical
  by_cases he : ∃ i : Fin 9, t ∈ Ioc (upperLeft i) (upperNode i)
  · obtain ⟨i, hi⟩ := he
    rw [nineProfile_cell _ hi]
    exact wuImprovementLimit_upper_antitone hd hdhi
      ⟨ht.1, ht.2.trans (by norm_num)⟩
      ⟨(upperNode_bounds i).1, (upperNode_bounds i).2.trans (by norm_num)⟩ hi.2
  · have hz : nineProfile (actualNine δ) t = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => he ⟨i, hi⟩) _
    rw [hz]
    exact wuImprovementLimit_nonneg true hd (by linarith : δ < 1 / 2)
      ht.1 (ht.2.trans (by norm_num))

/-- The nine actual nodes produce the complete continuous extension, with no numerical premises
and no assumed integrability or double-integral inequalities. -/
theorem actual_nine_extension {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    (∀ t, 0 ≤ nineProfile (actualNine δ) t) ∧
    aProfile (nineProfile (actualNine δ)) ≤ wuImprovementLimit false δ 4 ∧
    (∀ u ∈ Icc (2 : ℝ) 4, gProfile (nineProfile (actualNine δ)) u ≤ wuImprovementLimit false δ u) ∧
    (∀ v ∈ Icc (3 : ℝ) 5, eProfile (nineProfile (actualNine δ)) v ≤ wuImprovementLimit true δ v) := by
  exact ⟨nineProfile_nonneg (actualNine_nonneg hd hdhi),
    profile_extension hd hdhi (nineProfile_integrable _) (fun _ ht => nineProfile_le_actual hd hdhi ht)⟩

theorem cells_cover {t : ℝ} (ht : t ∈ Ioc (1 : ℝ) 3) :
    ∃ i : Fin 9, t ∈ Ioc (upperLeft i) (upperNode i) := by
  have hex : ∃ n : ℕ, n < 9 ∧ t ≤ (22 + (n : ℝ)) / 10 := by
    refine ⟨8, by omega, ?_⟩
    norm_num
    exact ht.2
  let n := Nat.find hex
  have hn : n < 9 ∧ t ≤ (22 + (n : ℝ)) / 10 := Nat.find_spec hex
  refine ⟨⟨n, hn.1⟩, ?_, hn.2⟩
  dsimp [upperLeft]
  split_ifs with hzero
  · exact ht.1
  · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
    have hmin : ¬ ((n - 1) < 9 ∧ t ≤ (22 + ((n - 1 : ℕ) : ℝ)) / 10) :=
      Nat.find_min hex (show n - 1 < Nat.find hex from Nat.sub_lt hpos (by omega))
    have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    by_contra h
    apply hmin
    refine ⟨by omega, ?_⟩
    rw [hpred]
    linarith

end NodeExtension
