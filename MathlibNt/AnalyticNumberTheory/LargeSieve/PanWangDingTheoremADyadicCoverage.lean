

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

/-- A convenient explicit form of the standard weighted primitive large-sieve
input.  The constant `C` is absolute; this definition merely records the exact
`N + Q²` scale needed below. -/
def PanWeightedPrimitiveLargeSieve (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ), 0 < Q →
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q, ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) ≤
      C * ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2

/-- **Pan--Wang--Ding Theorem A, sharp dyadic scale.**

On `P < q ≤ Q ≤ 2P`, write `1/φ(q) = (1/q)(q/φ(q))` and use
`1/q ≤ 1/P`.  Thus the standard `N + Q²` weighted primitive large sieve gives
an absolute multiple of `N/P + Q`; the displayed constant is `2C`. -/
theorem panTheoremALeft_le_sharp_dyadic
    {C : ℝ} (hLS : PanWeightedPrimitiveLargeSieve C)
    (b : ℤ → ℂ) (M : ℤ) (N P Q : ℕ)
    (hP : 0 < P) (hPQ : P < Q) (hQP : Q ≤ 2 * P) :
    panTheoremALeft b M N P Q ≤
      (2 * C) * ((Q : ℝ) + (N : ℝ) / P) *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  let Z : ℝ := ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2
  have hC : 0 ≤ C := hLS.1
  have hQ : 0 < Q := hP.trans hPQ
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hQR : (Q : ℝ) ≤ 2 * P := by exact_mod_cast hQP
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    positivity
  have hweighted := hLS.2 b M N Q hQ
  have hcell :
      panTheoremALeft b M N P Q ≤
        (1 / (P : ℝ)) *
          (∑ q ∈ Finset.Ioc P Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) := by
    unfold panTheoremALeft
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hqP : P < q := (Finset.mem_Ioc.mp hq).1
    have hqpos : 0 < q := hP.trans hqP
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hsum : 0 ≤ ∑ χ : PrimitiveCharacter q,
        ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 := by positivity
    have hcoeff : (q.totient : ℝ)⁻¹ ≤
        (1 / (P : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) := by
      simp only [div_eq_mul_inv, one_mul]
      have hqPR : (P : ℝ) ≤ q := by exact_mod_cast hqP.le
      have hPinv : 0 ≤ ((P : ℝ)⁻¹) := (inv_nonneg.mpr hPR.le)
      calc
        (q.totient : ℝ)⁻¹ =
            (P : ℝ)⁻¹ * ((P : ℝ) * (q.totient : ℝ)⁻¹) := by
          field_simp [hPR.ne']
        _ ≤ (P : ℝ)⁻¹ * ((q : ℝ) * (q.totient : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hqPR (inv_nonneg.mpr hφ.le)) hPinv
        _ = (P : ℝ)⁻¹ * ((q : ℝ) * (q.totient : ℝ)⁻¹) := rfl
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hsum
  have hsubset : Finset.Ioc P Q ⊆ Finset.Icc 1 Q := by
    intro q hq
    rcases Finset.mem_Ioc.mp hq with ⟨hqP, hqQ⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hqQ⟩
  have hrestrict :
      (∑ q ∈ Finset.Ioc P Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) ≤
        ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖primitiveIntervalAmplitude b M N χ‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro q hq hnot
    positivity
  calc
    panTheoremALeft b M N P Q ≤
        (1 / (P : ℝ)) *
          (∑ q ∈ Finset.Ioc P Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) := hcell
    _ ≤ (1 / (P : ℝ)) *
          (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖primitiveIntervalAmplitude b M N χ‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrestrict (by positivity)
    _ ≤ (1 / (P : ℝ)) * (C * ((N : ℝ) + (Q : ℝ) ^ 2) * Z) := by
        exact mul_le_mul_of_nonneg_left (by simpa [Z] using hweighted) (by positivity)
    _ ≤ (2 * C) * ((Q : ℝ) + (N : ℝ) / P) * Z := by
      have hscale : (1 / (P : ℝ)) * ((N : ℝ) + (Q : ℝ) ^ 2) ≤
          2 * ((Q : ℝ) + (N : ℝ) / P) := by
        rw [one_div]
        have hQ0 : (0 : ℝ) ≤ Q := by positivity
        have hN0 : (0 : ℝ) ≤ N := by positivity
        have hq2 : (Q : ℝ) ^ 2 ≤ 2 * (P : ℝ) * Q := by nlinarith
        rw [div_eq_mul_inv]
        have hmul := mul_le_mul_of_nonneg_left hq2 (inv_nonneg.mpr hPR.le)
        field_simp [hPR.ne'] at hmul ⊢
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale hC) hZ]

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

/-- The clipped `(j,k)` block used to state the exact finite form of (2.13).
The norm remains outside the complete source sum in its `k`-cell. -/
def panIymDyadicCoveredBlock
    (g d : ℕ → ℂ) (y D₁ D A₁ A₂ : ℕ) (j k : ℕ) : ℝ :=
  ∑ q ∈ panDyadicCell D₁ D j, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      ‖panSourceCharacterAmplitude g d y
        (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ‖

/-- The complete `a`-sum is the sum of its dyadic source blocks. -/
theorem panSourceCharacterAmplitude_eq_sum_dyadicCells
    (g d : ℕ → ℂ) (y A₁ A₂ : ℕ) (hA₁ : 0 < A₁)
    {q : ℕ} (χ : PrimitiveCharacter q) :
    panSourceCharacterAmplitude g d y A₁ A₂ χ =
      ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
        panSourceCharacterAmplitude g d y
          (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ := by
  unfold panSourceCharacterAmplitude
  rw [← panDyadicCells_cover A₁ A₂ hA₁,
    Finset.sum_biUnion (panDyadicCells_pairwise A₁ A₂ hA₁)]
  simp only [panDyadicCell]

/-- **Equation (2.13), complete finite dyadic block inequality.**

The conductor cells are disjoint, while the source decomposition uses one
triangle inequality per character after summing every `a` in a full source
cell.  This is exactly the absolute-value level in the paper. -/
theorem panIymHigh_le_sum_dyadicCoveredBlocks
    (g d : ℕ → ℂ) (y A₁ A₂ D₁ D : ℕ)
    (hA₁ : 0 < A₁) (hD₁ : 0 < D₁) :
    panIymHigh g d y A₁ A₂ D₁ D ≤
      ∑ j ∈ Finset.range (panDyadicDepth D₁ D),
        ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
          panIymDyadicCoveredBlock g d y D₁ D A₁ A₂ j k := by
  unfold panIymHigh panIymDyadicCoveredBlock
  rw [← panDyadicCells_cover D₁ D hD₁,
    Finset.sum_biUnion (panDyadicCells_pairwise D₁ D hD₁)]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (∑ q ∈ panDyadicCell D₁ D j, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q,
          ‖panSourceCharacterAmplitude g d y A₁ A₂ χ‖) ≤
      ∑ q ∈ panDyadicCell D₁ D j, (q.totient : ℝ)⁻¹ *
        ∑ χ : PrimitiveCharacter q,
          ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
            ‖panSourceCharacterAmplitude g d y
              (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ‖ := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro χ hχ
        rw [panSourceCharacterAmplitude_eq_sum_dyadicCells g d y A₁ A₂ hA₁ χ]
        exact norm_sum_le _ _
    _ = ∑ q ∈ panDyadicCell D₁ D j,
        ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
          ∑ χ : PrimitiveCharacter q, (q.totient : ℝ)⁻¹ *
            ‖panSourceCharacterAmplitude g d y
              (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (panDyadicDepth A₁ A₂),
        ∑ q ∈ panDyadicCell D₁ D j, (q.totient : ℝ)⁻¹ *
          ∑ χ : PrimitiveCharacter q,
            ‖panSourceCharacterAmplitude g d y
              (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ‖ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]

end

end AnalyticNumberTheory.LargeSieve