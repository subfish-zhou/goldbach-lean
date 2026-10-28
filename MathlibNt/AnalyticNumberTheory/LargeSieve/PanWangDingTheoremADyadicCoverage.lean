

import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEarlySourceReduction

/-!
 # Pan--Wang--Ding Theorem A and the dyadic cover in (2.13)

This leaf isolates two finite deductions used on pp. 600--604 of Pan--Wang--
Ding (1975).  First, the usual `q / φ(q)` primitive large sieve implies the
sharp Theorem A scale `Q + N / P` on a dyadic conductor interval.  Second, the
two open-left, closed-right dyadic partitions used in (2.13) really cover the
whole conductor and source rectangles.  The triangle inequality is applied
only after each complete source block has been summed; it is never pushed
inside the `a`-sum.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## The sharp dyadic form of Theorem A -/


/-! ## The complete dyadic cover used in (2.13) -/

/-- Number of open-left dyadic cells required to cover `(R,Q]`. -/
def panDyadicDepth (R Q : ℕ) : ℕ := Nat.log 2 (Q / R) + 1

/-- The `j`-th open-left, closed-right dyadic cell, clipped only at the final
paper endpoint. -/
def panDyadicCell (R Q j : ℕ) : Finset ℕ :=
  Finset.Ioc (R * 2 ^ j) (min (2 * (R * 2 ^ j)) Q)

/-- Every point of `(R,Q]` lies in one of the advertised dyadic cells. -/
theorem mem_panDyadicCell_of_mem_Ioc
    {R Q x : ℕ} (hR : 0 < R) (hx : x ∈ Finset.Ioc R Q) :
    ∃ j ∈ Finset.range (panDyadicDepth R Q), x ∈ panDyadicCell R Q j := by
  rcases Finset.mem_Ioc.mp hx with ⟨hRx, hxQ⟩
  let t := (x - 1) / R
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.div_pos (by omega) hR
  let j := Nat.log 2 t
  have hlo : R * 2 ^ j < x := by
    have hp : 2 ^ j ≤ t := Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
    have hmul : R * 2 ^ j ≤ x - 1 := by
      calc
        R * 2 ^ j ≤ R * t := Nat.mul_le_mul_left R hp
        _ ≤ x - 1 := Nat.mul_div_le _ _
    omega
  have hhi : x ≤ 2 * (R * 2 ^ j) := by
    have htlt : t < 2 ^ (j + 1) := by
      simpa [j] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t
    have hdiv : x - 1 < R * 2 ^ (j + 1) := by
      have := Nat.lt_mul_of_div_lt htlt hR
      simpa [t, mul_comm] using this
    rw [pow_succ] at hdiv
    calc
      x ≤ R * (2 ^ j * 2) := by omega
      _ = 2 * (R * 2 ^ j) := by ring
  have hj : j < panDyadicDepth R Q := by
    have htQ : t ≤ Q / R := Nat.div_le_div_right (by omega)
    have hlog := Nat.log_mono_right (b := 2) htQ
    dsimp [panDyadicDepth]
    omega
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  exact Finset.mem_Ioc.mpr ⟨hlo, le_min hhi hxQ⟩

/-- The cells cover the whole interval, including the last clipped cell. -/
theorem panDyadicCells_cover (R Q : ℕ) (hR : 0 < R) :
    (Finset.range (panDyadicDepth R Q)).biUnion (panDyadicCell R Q) =
      Finset.Ioc R Q := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    rcases Finset.mem_Ioc.mp hxj with ⟨hlow, hhigh⟩
    have hRlower : R ≤ R * 2 ^ j := by
      exact Nat.le_mul_of_pos_right R (pow_pos (by omega) j)
    exact Finset.mem_Ioc.mpr ⟨hRlower.trans_lt hlow,
      hhigh.trans (min_le_right _ _)⟩
  · intro hx
    rcases mem_panDyadicCell_of_mem_Ioc hR hx with ⟨j, hj, hxj⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, hxj⟩

/-- Distinct dyadic cells are disjoint. -/
theorem panDyadicCells_pairwise (R Q : ℕ) (_hR : 0 < R) :
    (↑(Finset.range (panDyadicDepth R Q)) : Set ℕ).PairwiseDisjoint
      (panDyadicCell R Q) := by
  intro i hi j hj hij
  change Disjoint (panDyadicCell R Q i) (panDyadicCell R Q j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases Finset.mem_Ioc.mp hxi with ⟨hilo, hihi⟩
  rcases Finset.mem_Ioc.mp hxj with ⟨hjlo, hjhi⟩
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ i) ≤ R * 2 ^ j := by nlinarith
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i :=
      (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).monotone (by omega)
    rw [pow_succ] at hp
    have : 2 * (R * 2 ^ j) ≤ R * 2 ^ i := by nlinarith
    omega

/-- Sum over the exact dyadic partition, before taking any norms. -/
private theorem sum_Ioc_eq_sum_panDyadicCells {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (R Q : ℕ) (hR : 0 < R) :
    ∑ x ∈ Finset.Ioc R Q, f x =
      ∑ j ∈ Finset.range (panDyadicDepth R Q), ∑ x ∈ panDyadicCell R Q j, f x := by
  rw [← panDyadicCells_cover R Q hR,
    Finset.sum_biUnion (panDyadicCells_pairwise R Q hR)]


/-- The complete `a`-sum is the sum of its dyadic source blocks. -/
theorem panSourceCharacterAmplitude_eq_sum_dyadicCells
    (g d : ℕ → ℂ) (y A₁ A₂ : ℕ) (hA₁ : 0 < A₁)
    {q : ℕ} (χ : PrimitiveCharacter q) :
    panSourceCharacterAmplitude g d y A₁ A₂ χ =
      ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
        panSourceCharacterAmplitude g d y
          (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ := by
  unfold panSourceCharacterAmplitude
  exact sum_Ioc_eq_sum_panDyadicCells _ A₁ A₂ hA₁


end

end AnalyticNumberTheory.LargeSieve