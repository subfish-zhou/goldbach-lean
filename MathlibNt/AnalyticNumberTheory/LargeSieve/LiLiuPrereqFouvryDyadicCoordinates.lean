import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedScale

/-!
# Positive coordinates for five-variable partial summation

The frequency sign is kept separate. Coordinate cutoffs select genuine
rectangular prefixes of the actual arithmetic carrier; they do not erase
compatibility, residue, low-omega, or original-support conditions.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wAnalyticCoordinates (t : WExtractedTuple × ℤ) : Fin 5 → ℕ :=
  ![t.2.natAbs, (wGCDTuple (wExtractedOriginal t.1)).k₁,
    (wGCDTuple (wExtractedOriginal t.1)).n₁, t.1.1.2.1, t.1.1.2.2]

theorem wAnalyticCoordinates_pos {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) (i : Fin 5) :
    0 < wAnalyticCoordinates t i := by
  obtain ⟨_, _, _, _, hk, hn, hr, hs, hh⟩ := wExtractedKeyFiber_positive hN hQ ht
  have hh' : 0 < t.2.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hh)
  revert i
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    wAnalyticCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact ⟨hh', hk, hn, hr, hs⟩

def wDyadicScale (n : ℕ) : ℝ := (2 : ℝ) ^ Nat.log 2 n

theorem wDyadicScale_pos (n : ℕ) : 0 < wDyadicScale n := by
  unfold wDyadicScale
  positivity

theorem wDyadicScale_bounds {n : ℕ} (hn : 0 < n) :
    wDyadicScale n ≤ (n : ℝ) ∧ (n : ℝ) < 2 * wDyadicScale n := by
  unfold wDyadicScale
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  · have hb := Nat.lt_pow_succ_log_self (b := 2) (by decide) n
    rw [pow_succ, mul_comm] at hb
    exact_mod_cast hb

theorem wDyadicScale_normalized {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / wDyadicScale n ∈ Set.Icc (1 : ℝ) 2 := by
  have hb := wDyadicScale_bounds hn
  rw [Set.mem_Icc, le_div_iff₀ (wDyadicScale_pos n),
    div_le_iff₀ (wDyadicScale_pos n), one_mul]
  exact ⟨hb.1, hb.2.le⟩

def wAnalyticDyadicKey (t : WExtractedTuple × ℤ) : Fin 5 → ℕ :=
  fun i => Nat.log 2 (wAnalyticCoordinates t i)

/-- Prefixes are taken in all five analytic variables, with the original
fiber and its arithmetic masks still present. -/
def wAnalyticPrefix (T : Finset (WExtractedTuple × ℤ)) (v : Fin 5 → ℕ) :
    Finset (WExtractedTuple × ℤ) :=
  T.filter (fun t => ∀ i, wAnalyticCoordinates t i ≤ v i)

/-- The correct arithmetic sum left after removing only the slow weight. -/
def wAnalyticPrefixSum (T : Finset (WExtractedTuple × ℤ))
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (v : Fin 5 → ℕ) : ℂ :=
  ∑ t ∈ wAnalyticPrefix T v,
    (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) * wExtractedArithmeticPhase a t.2 t.1

/-- Fix the sign as well as dyadic sizes before passing to a positive
continuous rectangle. `false` denotes the negative frequency branch. -/
def wAnalyticDyadicBlock (T : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (positive : Bool) : Finset (WExtractedTuple × ℤ) :=
  T.filter (fun t => wAnalyticDyadicKey t = j ∧ decide (0 < t.2) = positive)

theorem wAnalyticDyadicBlock_bounds {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N Q a P R S ξ b K) j positive) (i : Fin 5) :
    (2 : ℝ) ^ j i ≤ (wAnalyticCoordinates t i : ℝ) ∧
      (wAnalyticCoordinates t i : ℝ) < 2 * (2 : ℝ) ^ j i := by
  obtain ⟨ht, hj, _⟩ := mem_filter.mp ht
  have he : Nat.log 2 (wAnalyticCoordinates t i) = j i := congrFun hj i
  simpa only [wDyadicScale, he] using
    wDyadicScale_bounds (wAnalyticCoordinates_pos hN hQ ht i)

/-- The original signed integer frequency is recovered from its positive
coordinate and its sign, including all unit-frequency cases. -/
theorem wAnalyticDyadicBlock_frequency {T : Finset (WExtractedTuple × ℤ)}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock T j positive) :
    (t.2 : ℝ) = (if positive then 1 else -1) * (wAnalyticCoordinates t 0 : ℝ) := by
  have hs := (mem_filter.mp ht).2.2
  simp only [wAnalyticCoordinates, Matrix.cons_val_zero]
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul]
    have hn : t.2 ≤ 0 := by simpa using hs
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonpos (by exact_mod_cast hn), neg_neg]
  · simp only [↓reduceIte, one_mul]
    have hn : 0 < t.2 := by simpa using hs
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hn)]

/-- Every point of a nonempty dyadic block lies in the full positive
unit rectangle used by the smooth-weight estimate. -/
def wAnalyticUnitCoordinates (j : Fin 5 → ℕ) (t : WExtractedTuple × ℤ) : Fin 5 → ℝ :=
  fun i => (wAnalyticCoordinates t i : ℝ) / (2 : ℝ) ^ j i

theorem wAnalyticUnitCoordinates_mem {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N Q a P R S ξ b K) j positive) (i : Fin 5) :
    wAnalyticUnitCoordinates j t i ∈ Set.Icc (1 : ℝ) 2 := by
  have hb := wAnalyticDyadicBlock_bounds hN hQ ht i
  dsimp only [wAnalyticUnitCoordinates]
  rw [Set.mem_Icc, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity), one_mul]
  exact ⟨hb.1, hb.2.le⟩

/-- An exact finite partition into signed dyadic rectangles. Repeated
coordinate values, including different `n₂` values, retain multiplicity. -/
theorem sum_wAnalyticDyadicBlocks {A : Type*} [AddCommMonoid A]
    (T : Finset (WExtractedTuple × ℤ)) (F : WExtractedTuple × ℤ → A) :
    ∑ t ∈ T, F t =
      ∑ j ∈ T.image wAnalyticDyadicKey,
        ((∑ t ∈ wAnalyticDyadicBlock T j true, F t) +
          ∑ t ∈ wAnalyticDyadicBlock T j false, F t) := by
  have he := sum_fiberwise_of_maps_to
    (s := T) (t := T.image wAnalyticDyadicKey) (g := wAnalyticDyadicKey)
    (fun t ht => mem_image.mpr ⟨t, ht, rfl⟩) F
  rw [← he]
  apply sum_congr rfl
  intro j _
  have hf : (T.filter (fun t => wAnalyticDyadicKey t = j)).filter
      (fun t => 0 < t.2) = wAnalyticDyadicBlock T j true := by
    ext t
    simp [wAnalyticDyadicBlock, and_assoc]
  have hf' : (T.filter (fun t => wAnalyticDyadicKey t = j)).filter
      (fun t => ¬0 < t.2) = wAnalyticDyadicBlock T j false := by
    ext t
    simp [wAnalyticDyadicBlock, and_assoc]
  rw [← hf, ← hf', sum_filter_add_sum_filter_not]

/-- A scale bound for the actual coordinates, including retained frequency,
derived without replacing the carrier by an arbitrary rectangular set. -/
def wAnalyticCoordinateBound (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) : ℕ :=
  max (wExtractedMaxFrequency H N Q a P R S ξ) (max (Q.sup id) (N.sup id))

theorem wAnalyticCoordinates_le_bound {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) (i : Fin 5) :
    wAnalyticCoordinates t i ≤ wAnalyticCoordinateBound H N Q a P R S ξ := by
  have hfreq := (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1
  have hz := (mem_wExtractedFrequencies_iff.mp hfreq).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  obtain ⟨hq, hr⟩ := wExtractedOriginal_reducedModuli hz
  have hq' := (mem_filter.mp hq).1
  have hr' := (mem_filter.mp hr).1
  have hcoord₀ : t.2.natAbs ≤ wExtractedMaxFrequency H N Q a P R S ξ :=
    wExtractedFrequencies_natAbs_le hfreq
  have hcoord₁ : (wGCDTuple (wExtractedOriginal t.1)).k₁ ≤ Q.sup id :=
    (Nat.le_of_dvd (hQ _ hq') hv.k₁_dvd).trans (le_sup (f := id) hq')
  have hcoord₂ : (wGCDTuple (wExtractedOriginal t.1)).n₁ ≤ N.sup id := by
    have hnmem : (wExtractedOriginal t.1).2.1 ∈ N := hm.2.2.2.2.2.2.2.1
    have hd : (wGCDTuple (wExtractedOriginal t.1)).n₁ ∣
        (wExtractedOriginal t.1).2.1 := by
      rw [hv.N₁_eq]
      exact dvd_mul_left _ _
    exact (Nat.le_of_dvd (hN _ hnmem) hd).trans (le_sup (f := id) hnmem)
  have hcoord₃ : t.1.1.2.1 ≤ Q.sup id := by
    apply (Nat.le_of_dvd (hQ _ hr') ?_).trans (le_sup (f := id) hr')
    exact ⟨t.1.1.1.1 * t.1.1.1.2 * t.1.1.2.2, by dsimp [wExtractedOriginal]; ring⟩
  have hcoord₄ : t.1.1.2.2 ≤ Q.sup id := by
    apply (Nat.le_of_dvd (hQ _ hr') ?_).trans (le_sup (f := id) hr')
    exact ⟨t.1.1.1.1 * t.1.1.2.1 * t.1.1.1.2, by dsimp [wExtractedOriginal]; ring⟩
  unfold wAnalyticCoordinateBound
  revert i
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    wAnalyticCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- An explicit polynomial in logarithms pays all five dyadic coordinates.
The existing fixed frequency shell can only reduce this coarse count. -/
theorem wAnalyticDyadicKey_image_card_le
    (T : Finset (WExtractedTuple × ℤ)) (B : ℕ)
    (hB : ∀ t ∈ T, ∀ i, wAnalyticCoordinates t i ≤ B) :
    (T.image wAnalyticDyadicKey).card ≤ (Nat.log 2 B + 1) ^ 5 := by
  have hsub : T.image wAnalyticDyadicKey ⊆
      Fintype.piFinset (fun _ : Fin 5 => range (Nat.log 2 B + 1)) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hj
    apply Fintype.mem_piFinset.mpr
    intro i
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hB t ht i)))
  have hc := card_le_card hsub
  simpa only [Fintype.card_piFinset, card_range, prod_const, card_univ,
    Fintype.card_fin] using hc

theorem wExtractedKeyFiber_dyadic_card_le {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) :
    ((wExtractedKeyFiber H N Q a P R S ξ b K).image wAnalyticDyadicKey).card ≤
      (Nat.log 2 (wAnalyticCoordinateBound H N Q a P R S ξ) + 1) ^ 5 :=
  wAnalyticDyadicKey_image_card_le _ _
    (fun _ ht i => wAnalyticCoordinates_le_bound hN hQ ht i)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
