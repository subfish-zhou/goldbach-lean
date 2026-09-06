import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Purely finite block geometry.  `cell i` is a conductor block with lower
endpoint `i`. -/
structure ProductionConductorBlockGeometry (N Q C : ℕ) where
  index : Finset ℕ
  cell : ℕ → Finset ℕ
  lower_pos : ∀ i ∈ index, 0 < i
  levels : ∀ i ∈ index, ∀ d ∈ cell i, i ≤ d
  pairwise : (↑index : Set ℕ).PairwiseDisjoint cell
  cover : index.biUnion cell = highConductorSet N Q C
  inv_lower_sum_le : (∑ i ∈ index, (i : ℝ)⁻¹) ≤
    2 / (logConductorThreshold N C : ℝ)
  lower_sum_le : (∑ i ∈ index, (i : ℝ)) ≤ 2 * (Q : ℝ)

private def dyadicDepth (R Q : ℕ) : ℕ := Nat.log 2 (Q / R) + 1

private def dyadicLowers (R Q : ℕ) : Finset ℕ :=
  if R < Q then
    (Finset.range (dyadicDepth R Q)).image fun j => R * 2 ^ j
  else ∅

private def dyadicCell (N Q C i : ℕ) : Finset ℕ :=
  (highConductorSet N Q C).filter fun d => i < d ∧ d ≤ 2 * i

private lemma exists_dyadic_exponent_of_mem {R Q i : ℕ}
    (hi : i ∈ dyadicLowers R Q) :
    ∃ j ∈ Finset.range (dyadicDepth R Q), R * 2 ^ j = i := by
  by_cases hRQ : R < Q
  · exact Finset.mem_image.mp (by simpa [dyadicLowers, hRQ] using hi)
  · simp [dyadicLowers, hRQ] at hi

private lemma sum_two_pow (k : ℕ) :
    ∑ j ∈ Finset.range k, (2 : ℕ) ^ j = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hk : 0 < 2 ^ k := pow_pos (by omega) _
      rw [pow_succ]
      omega

private lemma sum_inv_two_pow_le_two (k : ℕ) :
    (∑ j ∈ Finset.range k, ((2 : ℝ) ^ j)⁻¹) ≤ 2 := by
  rw [show (∑ j ∈ Finset.range k, ((2 : ℝ) ^ j)⁻¹) =
      ∑ j ∈ Finset.range k, ((2 : ℝ)⁻¹) ^ j by
    apply Finset.sum_congr rfl
    intro j hj
    simp]
  rw [geom_sum_eq (by norm_num : (2 : ℝ)⁻¹ ≠ 1)]
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ k := by positivity
  norm_num
  linarith

private lemma dyadicLower_injective (R : ℕ) (hR : 0 < R) :
    Function.Injective (fun j => R * 2 ^ j) := by
  intro i j hij
  have : 2 ^ i = 2 ^ j := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) hij
  exact (pow_right_injective₀ (by norm_num : (0 : ℕ) < 2)
    (by norm_num : (2 : ℕ) ≠ 1)) this

private lemma dyadic_cover_aux (R Q d : ℕ) (hR : 0 < R) (hRd : R < d)
    (hdQ : d ≤ Q) :
    ∃ j < dyadicDepth R Q, R * 2 ^ j < d ∧ d ≤ 2 * (R * 2 ^ j) := by
  let x := (d - 1) / R
  have hx : 0 < x := by
    dsimp [x]
    exact Nat.div_pos (by omega) hR
  let j := Nat.log 2 x
  have hlo : R * 2 ^ j < d := by
    have hp : 2 ^ j ≤ x := Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)
    have hmul : R * 2 ^ j ≤ d - 1 := by
      calc
        R * 2 ^ j ≤ R * x := Nat.mul_le_mul_left R hp
        _ ≤ d - 1 := Nat.mul_div_le _ _
    omega
  have hhi : d ≤ 2 * (R * 2 ^ j) := by
    have hxlt : x < 2 ^ (j + 1) := by
      simpa [j] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
    have hdiv : d - 1 < R * 2 ^ (j + 1) := by
      have := Nat.lt_mul_of_div_lt hxlt hR
      simpa [x, mul_comm] using this
    rw [pow_succ] at hdiv
    calc
      d ≤ R * (2 ^ j * 2) := by omega
      _ = 2 * (R * 2 ^ j) := by ring
  have hj : j < dyadicDepth R Q := by
    have hxQ : x ≤ Q / R := Nat.div_le_div_right (by omega)
    have hlog := Nat.log_mono_right (b := 2) hxQ
    dsimp [dyadicDepth]
    omega
  exact ⟨j, hj, hlo, hhi⟩

private lemma dyadic_cells_pairwise (N Q C R : ℕ) (_hR : 0 < R) :
    (↑(dyadicLowers R Q) : Set ℕ).PairwiseDisjoint (dyadicCell N Q C) := by
  intro i hi j hj hij
  change Disjoint (dyadicCell N Q C i) (dyadicCell N Q C j)
  rw [Finset.disjoint_left]
  intro d hdi hdj
  simp only [dyadicCell, Finset.mem_filter] at hdi hdj
  rcases exists_dyadic_exponent_of_mem hi with ⟨a, ha, rfl⟩
  rcases exists_dyadic_exponent_of_mem hj with ⟨b, hb, hab⟩
  subst j
  have hab' : a ≠ b := by
    intro h
    subst b
    exact hij rfl
  rcases lt_or_gt_of_ne hab' with hablt | hbalt
  · have hp : 2 ^ (a + 1) ≤ 2 ^ b :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ a) ≤ R * 2 ^ b := by
      nlinarith
    omega
  · have hp : 2 ^ (b + 1) ≤ 2 ^ a :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ b) ≤ R * 2 ^ a := by
      nlinarith
    omega

/-- Canonical production dyadic conductor geometry.  Its cells are
`R*2^j < d ≤ min (2*R*2^j) Q`, intersected with the production high-conductor
set. -/
noncomputable def productionConductorBlockGeometry
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) :
    ProductionConductorBlockGeometry N Q C := by
  let R := logConductorThreshold N C
  let I := dyadicLowers R Q
  let cell := dyadicCell N Q C
  refine
    { index := I
      cell := cell
      lower_pos := ?_
      levels := ?_
      pairwise := ?_
      cover := ?_
      inv_lower_sum_le := ?_
      lower_sum_le := ?_ }
  · intro i hi
    rcases exists_dyadic_exponent_of_mem hi with ⟨j, hj, rfl⟩
    exact Nat.mul_pos hR (pow_pos (by norm_num) _)
  · intro i hi d hd
    exact (Finset.mem_filter.mp hd).2.1.le
  · exact dyadic_cells_pairwise N Q C R hR
  · ext d
    constructor
    · intro hd
      rw [Finset.mem_biUnion] at hd
      rcases hd with ⟨i, hi, hdi⟩
      exact (Finset.mem_filter.mp hdi).1
    · intro hd
      have hmem := Finset.mem_filter.mp hd
      have hRd : R < d := hmem.2
      have hdQ : d ≤ Q := (Finset.mem_Icc.mp hmem.1).2
      rcases dyadic_cover_aux R Q d hR hRd hdQ with ⟨j, hj, hlo, hhi⟩
      rw [Finset.mem_biUnion]
      refine ⟨R * 2 ^ j, ?_, ?_⟩
      · have hRQ : R < Q := hRd.trans_le hdQ
        simp only [I, dyadicLowers, if_pos hRQ]
        exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hd, hlo, hhi⟩
  · by_cases hRQ : R < Q
    · change (∑ i ∈ dyadicLowers R Q, (i : ℝ)⁻¹) ≤ 2 / (R : ℝ)
      rw [dyadicLowers, if_pos hRQ]
      rw [Finset.sum_image (f := fun i : ℕ => ((i : ℝ)⁻¹))
        (dyadicLower_injective R hR).injOn]
      rw [show (∑ j ∈ Finset.range (dyadicDepth R Q), ((R * 2 ^ j : ℕ) : ℝ)⁻¹) =
        (R : ℝ)⁻¹ * ∑ j ∈ Finset.range (dyadicDepth R Q), ((2 : ℝ) ^ j)⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        push_cast
        rw [mul_inv]]
      have := sum_inv_two_pow_le_two (dyadicDepth R Q)
      have hRreal : (0 : ℝ) ≤ (R : ℝ)⁻¹ := by positivity
      calc
        (R : ℝ)⁻¹ * ∑ j ∈ Finset.range (dyadicDepth R Q), ((2 : ℝ) ^ j)⁻¹ ≤
            (R : ℝ)⁻¹ * 2 := mul_le_mul_of_nonneg_left this hRreal
        _ = 2 / (R : ℝ) := by ring
    · simp [I, dyadicLowers, hRQ, div_nonneg]
  · by_cases hRQ : R < Q
    · change (∑ i ∈ dyadicLowers R Q, (i : ℝ)) ≤ 2 * (Q : ℝ)
      rw [dyadicLowers, if_pos hRQ]
      rw [Finset.sum_image (f := fun i : ℕ => (i : ℝ))
        (dyadicLower_injective R hR).injOn]
      push_cast
      rw [← Finset.mul_sum]
      norm_cast
      rw [sum_two_pow]
      have hdiv : R * (Q / R) ≤ Q := Nat.mul_div_le Q R
      have hqdiv : Q / R ≠ 0 := by
        exact Nat.ne_of_gt (Nat.div_pos hRQ.le hR)
      have hp := Nat.pow_log_le_self 2 hqdiv
      have hpow : 2 ^ dyadicDepth R Q ≤ 2 * (Q / R) := by
        dsimp [dyadicDepth]
        rw [pow_succ]
        simpa [mul_comm] using Nat.mul_le_mul_left 2 hp
      have : R * (2 ^ dyadicDepth R Q - 1) ≤ 2 * Q := by
        calc
          R * (2 ^ dyadicDepth R Q - 1) ≤ R * 2 ^ dyadicDepth R Q :=
            Nat.mul_le_mul_left R (Nat.sub_le _ _)
          _ ≤ R * (2 * (Q / R)) := Nat.mul_le_mul_left R hpow
          _ = 2 * (R * (Q / R)) := by ring
          _ ≤ 2 * Q := Nat.mul_le_mul_left 2 hdiv
      exact_mod_cast this
    · simp [I, dyadicLowers, hRQ]

/-- Every cell of the canonical production geometry lies in its literal dyadic
conductor interval.  This is a property of the concrete canonical construction,
not an additional premise of `ProductionConductorBlockGeometry`. -/
theorem productionConductorBlockGeometry_cell_subset_Ioc
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) (i : ℕ) :
    (productionConductorBlockGeometry N Q C hR).cell i ⊆
      Finset.Ioc i (2 * i) := by
  intro d hd
  change d ∈ dyadicCell N Q C i at hd
  exact Finset.mem_Ioc.mpr (Finset.mem_filter.mp hd).2

/-- The concrete dyadic conductor geometry has at most one index per binary
scale up to `N`. -/
theorem productionConductorBlockGeometry_index_card_le_log2
    (N Q C : ℕ) (hR : 0 < logConductorThreshold N C) (hQ : Q ≤ N) :
    (productionConductorBlockGeometry N Q C hR).index.card ≤ Nat.log2 N + 1 := by
  unfold productionConductorBlockGeometry
  dsimp only
  unfold dyadicLowers dyadicDepth
  split_ifs with hRQ
  · calc
      (Finset.image (fun j => logConductorThreshold N C * 2 ^ j)
          (Finset.range (Nat.log 2 (Q / logConductorThreshold N C) + 1))).card ≤
          (Finset.range (Nat.log 2 (Q / logConductorThreshold N C) + 1)).card :=
        Finset.card_image_le
      _ = Nat.log 2 (Q / logConductorThreshold N C) + 1 := by simp
      _ ≤ Nat.log2 N + 1 := by
        rw [Nat.log2_eq_log_two]
        gcongr
        exact (Nat.div_le_self Q _).trans hQ
  · simp

end
end AnalyticNumberTheory.LargeSieve
