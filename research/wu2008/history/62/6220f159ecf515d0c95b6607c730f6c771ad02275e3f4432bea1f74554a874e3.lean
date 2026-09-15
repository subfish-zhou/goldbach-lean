import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassFamilySharp

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthClosureLo (n i : ℕ) : ℝ := i / (n + 1 : ℕ)
noncomputable def truncatedSixthClosureHi (n i : ℕ) : ℝ := (i + 1 : ℕ) / (n + 1 : ℕ)
noncomputable def truncatedSixthClosureIndex (n : ℕ) (x : ℝ) : ℕ := ⌊(n + 1 : ℕ) * x⌋₊
noncomputable def truncatedSixthClosureCells (n : ℕ) : Finset (ℕ × ℕ) :=
  range (n + 1) ×ˢ range (n + 1)
noncomputable def truncatedSixthClosureCell (n : ℕ) (j : ℕ × ℕ) : Set (ℝ × ℝ) :=
  Set.Ico (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1) ×ˢ
    Set.Ico (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2)
noncomputable def truncatedSixthClosureLower (n : ℕ) (j : ℕ × ℕ) : ℝ × ℝ :=
  (truncatedSixthClosureLo n j.1, truncatedSixthClosureLo n j.2)
noncomputable def truncatedSixthClosureUpper (n : ℕ) (j : ℕ × ℕ) : ℝ × ℝ :=
  (truncatedSixthClosureHi n j.1, truncatedSixthClosureHi n j.2)

theorem truncatedSixthClosure_lo_lt_hi (n i : ℕ) :
    truncatedSixthClosureLo n i < truncatedSixthClosureHi n i := by
  unfold truncatedSixthClosureLo truncatedSixthClosureHi
  apply div_lt_div_of_pos_right _ (by positivity)
  exact_mod_cast Nat.lt_succ_self i

theorem truncatedSixthClosure_index_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    truncatedSixthClosureLo n (truncatedSixthClosureIndex n x) ≤ x ∧
      x < truncatedSixthClosureHi n (truncatedSixthClosureIndex n x) := by
  have hm : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  constructor
  · exact (div_le_iff₀ hm).mpr (by
      simpa [truncatedSixthClosureIndex, mul_comm] using Nat.floor_le (mul_nonneg hm.le hx))
  · apply (lt_div_iff₀ hm).mpr
    simpa [truncatedSixthClosureIndex, Nat.cast_add, Nat.cast_one, mul_comm] using
      Nat.lt_floor_add_one ((n + 1 : ℕ) * x)

theorem truncatedSixthClosure_index_lt (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    truncatedSixthClosureIndex n x < n + 1 := by
  apply (Nat.floor_lt (mul_nonneg (by positivity) hx0)).mpr
  nlinarith [show (0 : ℝ) < (n + 1 : ℕ) by positivity]

theorem truncatedSixthClosure_cell_unique {n : ℕ} {j k : ℕ × ℕ} {v : ℝ × ℝ}
    (hj : v ∈ truncatedSixthClosureCell n j) (hk : v ∈ truncatedSixthClosureCell n k) :
    j = k := by
  have hcoord {i l : ℕ} {x : ℝ}
      (hi : x ∈ Set.Ico (truncatedSixthClosureLo n i) (truncatedSixthClosureHi n i))
      (hl : x ∈ Set.Ico (truncatedSixthClosureLo n l) (truncatedSixthClosureHi n l)) : i = l := by
    have hm : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have h1 := (div_le_iff₀ hm).mp hi.1
    have h2 := (lt_div_iff₀ hm).mp hi.2
    have h3 := (div_le_iff₀ hm).mp hl.1
    have h4 := (lt_div_iff₀ hm).mp hl.2
    have hil : (i : ℝ) < l + 1 := by simpa using h1.trans_lt h4
    have hli : (l : ℝ) < i + 1 := by simpa using h3.trans_lt h2
    have : i < l + 1 := by exact_mod_cast hil
    have : l < i + 1 := by exact_mod_cast hli
    omega
  exact Prod.ext (hcoord hj.1 hk.1) (hcoord hj.2 hk.2)

theorem truncatedSixthClosure_cell_mem {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ truncatedSixthClosureCells n) {v : ℝ × ℝ}
    (hv : v ∈ truncatedSixthClosureCell n j) :
    v ∈ Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1 := by
  have hupper {i : ℕ} (hi : i < n + 1) : truncatedSixthClosureHi n i ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    exact_mod_cast (show i + 1 ≤ n + 1 by omega)
  have hj' := Finset.mem_product.mp hj
  have hlo (i : ℕ) : 0 ≤ truncatedSixthClosureLo n i := by
    unfold truncatedSixthClosureLo
    positivity
  exact ⟨⟨(hlo _).trans hv.1.1,
      hv.1.2.trans_le (hupper (mem_range.mp hj'.1))⟩,
    ⟨(hlo _).trans hv.2.1,
      hv.2.2.trans_le (hupper (mem_range.mp hj'.2))⟩⟩

theorem truncatedSixthClosure_corner_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => truncatedSixthClosureLo n (truncatedSixthClosureIndex n x))
      atTop (𝓝 x) ∧
    Tendsto (fun n => truncatedSixthClosureHi n (truncatedSixthClosureIndex n x))
      atTop (𝓝 x) := by
  have hmesh : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hdiff (n i : ℕ) : truncatedSixthClosureHi n i =
      truncatedSixthClosureLo n i + 1 / ((n + 1 : ℕ) : ℝ) := by
    simp [truncatedSixthClosureHi, truncatedSixthClosureLo, add_div]
  have hlo : Tendsto (fun n => truncatedSixthClosureLo n (truncatedSixthClosureIndex n x))
      atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => x - 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 x) by
        simpa using tendsto_const_nhds.sub hmesh) tendsto_const_nhds
    · intro n
      have h := (truncatedSixthClosure_index_bounds n hx).2
      rw [hdiff] at h
      linarith
    · exact fun n => (truncatedSixthClosure_index_bounds n hx).1
  refine ⟨hlo, ?_⟩
  simp_rw [hdiff]
  simpa using hlo.add hmesh

theorem truncatedSixthClosure_cell_measurable (n : ℕ) (j : ℕ × ℕ) :
    MeasurableSet (truncatedSixthClosureCell n j) :=
  measurableSet_Ico.prod measurableSet_Ico

theorem truncatedSixthClosure_cell_volume (n : ℕ) (j : ℕ × ℕ) :
    volume.real (truncatedSixthClosureCell n j) =
      (truncatedSixthClosureHi n j.1 - truncatedSixthClosureLo n j.1) *
      (truncatedSixthClosureHi n j.2 - truncatedSixthClosureLo n j.2) := by
  change ((volume.prod volume) _).toReal = _
  rw [truncatedSixthClosureCell,
    Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Ico, Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (truncatedSixthClosure_lo_lt_hi _ _).le),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (truncatedSixthClosure_lo_lt_hi _ _).le)]

end Wu2008DoubleSieve
