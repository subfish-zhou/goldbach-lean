import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimePartitionCost

/-!
# Lemma 7 on the actual extracted arithmetic carrier

Fouvry (1987), pp. 628--629, III.7. The pair is `(n₂,n₁*s')`.
Its positivity, coprimality and growing prime-factor bounds are derived from
the original retained masks. The partition acts on tuples, not on their
possibly repeated pair images, so no beta-index multiplicity is lost.
-/

noncomputable section
open Classical Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open _root_.LiLiuPrereqFouvry.CoprimePartition

def wCoprimePair (z : WExtractedTuple) : ℕ × ℕ :=
  ((wGCDTuple (wExtractedOriginal z)).n₂,
    (wGCDTuple (wExtractedOriginal z)).n₁ * z.1.2.2)

def wCoprimePairBound (N : Finset ℕ) (S : ℝ) : ℕ :=
  max 2 (max (N.sup id) (N.sup id * ⌊S⌋₊))

def wCoprimeOrder (x : ℝ) : ℕ := ⌊2 * highOmegaCutoff x⌋₊

/-- Every retained tuple, including one with zero coefficient, is in the
precise domain of Lemma 7. No roughness or SW assumption is needed here. -/
theorem wCoprimePair_admissible {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x)) :
    wCoprimePair z ∈ admissiblePairs (wCoprimePairBound N S) (wCoprimeOrder x) := by
  obtain ⟨hv, hc⟩ := wExtractedOriginal_valid hN hQ hz
  obtain ⟨_, hΔ', _, hs', _, _, _, hN₁, hN₂, _, _, hP, hωs, _, _⟩ :=
    mem_wFactorExtractionTuples_iff.mp hz
  have hd₁ : (wGCDTuple (wExtractedOriginal z)).n₁ ∣ z.2.2.1 := by
    change _ ∣ (wExtractedOriginal z).2.1
    rw [hv.N₁_eq]
    exact dvd_mul_left _ _
  have hd₂ : (wGCDTuple (wExtractedOriginal z)).n₂ ∣ z.2.2.2 := by
    change _ ∣ (wExtractedOriginal z).2.2
    rw [hv.N₂_eq]
    exact dvd_mul_left _ _
  have hds : z.1.2.2 ∣ z.1.1.2 * z.1.2.2 := dvd_mul_left _ _
  have hdq : z.1.2.2 ∣ (wExtractedOriginal z).1.2 := by
    exact dvd_mul_of_dvd_right hds _
  have hns : (wGCDTuple (wExtractedOriginal z)).n₂.Coprime z.1.2.2 :=
    hc.2.1.of_dvd hd₂ hdq
  have hn₁ : (wGCDTuple (wExtractedOriginal z)).n₁ ≤ N.sup id :=
    (Nat.le_of_dvd (hN _ hN₁) hd₁).trans (le_sup (f := id) hN₁)
  have hn₂ : (wGCDTuple (wExtractedOriginal z)).n₂ ≤ N.sup id :=
    (Nat.le_of_dvd (hN _ hN₂) hd₂).trans (le_sup (f := id) hN₂)
  have hω₁ : ((wGCDTuple (wExtractedOriginal z)).n₁.primeFactors.card : ℝ) ≤
      highOmegaCutoff x :=
    (Nat.cast_le.mpr (card_le_card (Nat.primeFactors_mono hd₁
      (hN _ hN₁).ne'))).trans hP.1.1.1.2.1
  have hω₂ : ((wGCDTuple (wExtractedOriginal z)).n₂.primeFactors.card : ℝ) ≤
      highOmegaCutoff x :=
    (Nat.cast_le.mpr (card_le_card (Nat.primeFactors_mono hd₂
      (hN _ hN₂).ne'))).trans hP.1.1.1.2.2
  have hωs' : (z.1.2.2.primeFactors.card : ℝ) ≤ highOmegaCutoff x :=
    (Nat.cast_le.mpr (card_le_card (Nat.primeFactors_mono hds
      (Nat.mul_pos (mem_Ioc.mp hΔ').1 (mem_Ioc.mp hs').1).ne'))).trans hωs
  have hωprod :
      (((wGCDTuple (wExtractedOriginal z)).n₁ * z.1.2.2).primeFactors.card : ℝ) ≤
        2 * highOmegaCutoff x := by
    rw [Nat.primeFactors_mul hv.n₁_pos.ne' (mem_Ioc.mp hs').1.ne']
    have hu := Nat.cast_le (α := ℝ).mpr (card_union_le
      (wGCDTuple (wExtractedOriginal z)).n₁.primeFactors z.1.2.2.primeFactors)
    push_cast at hu
    linarith
  have hξ : 0 ≤ highOmegaCutoff x := (Nat.cast_nonneg _).trans hω₂
  apply mem_admissiblePairs.mpr
  dsimp only [wCoprimePair]
  refine ⟨⟨hv.n₂_pos, hn₂.trans ?_⟩,
    ⟨Nat.mul_pos hv.n₁_pos (mem_Ioc.mp hs').1, ?_⟩,
    hv.n₁_n₂.symm.mul_right hns, Nat.le_floor ?_, Nat.le_floor hωprod⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (Nat.mul_le_mul hn₁ (mem_Ioc.mp hs').2).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  · linarith

/-- The exact label depends only on the pair, not on `k₁`, `r'` or the
frequency. This is the independence used when forming Cauchy pairs. -/
def wCoprimeLabel (x : ℝ) (N : Finset ℕ) (S : ℝ) (t : WExtractedTuple × ℤ) :
    Finset (ℕ × ℕ) :=
  cell (wCoprimePairBound N S) (wCoprimeOrder x)
    (matrixColor (wCoprimePairBound N S) (wCoprimeOrder x) (wCoprimePair t.1))

def wCoprimeFiber (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (U : Finset (WExtractedTuple × ℤ)) (c : Finset (ℕ × ℕ)) :
    Finset (WExtractedTuple × ℤ) :=
  U.filter (fun t => wCoprimeLabel x N S t = c)

theorem wCoprimeLabel_eq_of_pair_eq (x : ℝ) (N : Finset ℕ) (S : ℝ)
    {t u : WExtractedTuple × ℤ} (h : wCoprimePair t.1 = wCoprimePair u.1) :
    wCoprimeLabel x N S t = wCoprimeLabel x N S u := by
  simp only [wCoprimeLabel, h]

theorem wCoprimeLabel_mem_partition {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K) :
    wCoprimeLabel x N S t ∈ partition (wCoprimePairBound N S) (wCoprimeOrder x) ∧
      wCoprimePair t.1 ∈ wCoprimeLabel x N S t := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hp := wCoprimePair_admissible hN hQ hz
  exact ⟨mem_partition.mpr ⟨_, hp, rfl⟩, mem_cell.mpr ⟨hp, rfl⟩⟩

/-- Cross-coprimality now holds for two distinct actual tuples in a cell,
not just for two abstract admissible pairs. -/
theorem wCoprimeFiber_cross_coprime {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    {c : Finset (ℕ × ℕ)} {t u : WExtractedTuple × ℤ}
    (ht : t ∈ wCoprimeFiber x N S U c) (hu : u ∈ wCoprimeFiber x N S U c) :
    (wCoprimePair t.1).1.Coprime (wCoprimePair u.1).2 ∧
      (wCoprimePair u.1).1.Coprime (wCoprimePair t.1).2 := by
  obtain ⟨ht, htc⟩ := mem_filter.mp ht
  obtain ⟨hu, huc⟩ := mem_filter.mp hu
  obtain ⟨hp, htp⟩ := wCoprimeLabel_mem_partition hN hQ (hU ht)
  have hup := (wCoprimeLabel_mem_partition hN hQ (hU hu)).2
  rw [htc] at hp htp
  rw [huc] at hup
  exact ⟨partition_cross_coprime hp htp hup, partition_cross_coprime hp hup htp⟩

/-- This identity keeps all tuple multiplicities and all signed weights.
There is no absolute value inside a cell. -/
theorem sum_wCoprimeFibers {A : Type*} [AddCommMonoid A]
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (U : Finset (WExtractedTuple × ℤ))
    (F : WExtractedTuple × ℤ → A) :
    ∑ t ∈ U, F t =
      ∑ c ∈ U.image (wCoprimeLabel x N S), ∑ t ∈ wCoprimeFiber x N S U c, F t := by
  exact (sum_fiberwise_of_maps_to
    (fun t ht => mem_image.mpr ⟨t, ht, rfl⟩) F).symm

theorem wCoprimeLabel_image_card_le {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K) :
    (U.image (wCoprimeLabel x N S)).card ≤
      (partition (wCoprimePairBound N S) (wCoprimeOrder x)).card := by
  apply card_le_card
  intro c hc
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hc
  exact (wCoprimeLabel_mem_partition hN hQ (hU ht)).1

/-- The original `2*(log x)^(1/5)` product-variable order has subpolynomial
cost. The threshold precedes every finite carrier and every varying residue. -/
theorem eventually_wCoprimeLabel_image_card_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
      (a : ℤ) (η R S : ℝ) (b : ℕ) (K : WExtractedKey)
      (U : Finset (WExtractedTuple × ℤ)),
      (∀ n ∈ N, 0 < n) → (∀ q ∈ Q, 0 < q) →
      (wCoprimePairBound N S : ℝ) ≤ x →
      U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
        R S (highOmegaCutoff x) b K →
      ((U.image (wCoprimeLabel x N S)).card : ℝ) ≤ x ^ ε := by
  filter_upwards [eventually_card_realPartition_le_rpow_of_factor
    (C := 2) (by norm_num) hε, eventually_ge_atTop (1 : ℝ)] with x hx hx₁
  intro H N Q a η R S b K U hN hQ hB hU
  have hξ : 0 ≤ highOmegaCutoff x := by
    exact Real.rpow_nonneg (Real.log_nonneg hx₁) _
  have hω : (wCoprimeOrder x : ℝ) ≤ 2 * Real.log x ^ (1 / 5 : ℝ) :=
    Nat.floor_le (mul_nonneg (by norm_num) hξ)
  have hcount := hx (wCoprimePairBound N S) (by
    exact_mod_cast le_max_left 2 (max (N.sup id) (N.sup id * ⌊S⌋₊))) hB
    (wCoprimeOrder x) hω
  simp only [realPartition, Nat.floor_natCast] at hcount
  exact (Nat.cast_le.mpr (wCoprimeLabel_image_card_le hN hQ hU)).trans hcount

/-- The actual C.2 levels satisfy the pair cutoff required above, including
the near-endpoint branch `S = 1`. Thus the cutoff is not a new analytic input. -/
theorem wCoprimePairBound_c2_le {x ν ε : ℝ} (hx : 4 ≤ x)
    (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10)
    {N : Finset ℕ} (hN : ∀ n ∈ N, (n : ℝ) ≤ 2 * x ^ ν) :
    (wCoprimePairBound N (x ^ c2SExponent ν ε) : ℝ) ≤ x := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hS : 1 ≤ x ^ c2SExponent ν ε :=
    (c2_factor_levels hx₁ hε hεν hν).2.1
  have hs : ν + c2SExponent ν ε ≤ (1 / 2 : ℝ) := by
    unfold c2SExponent
    by_cases he : 0 ≤ (1 - 10 * ν) / 9 - ε / 2
    · rw [max_eq_right he]
      linarith
    · rw [max_eq_left (by linarith : (1 - 10 * ν) / 9 - ε / 2 ≤ 0)]
      linarith
  have hp : x ^ ν * x ^ c2SExponent ν ε ≤ Real.sqrt x := by
    rw [← Real.rpow_add hx₀, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx₁ hs
  have hsup : ((N.sup id : ℕ) : ℝ) ≤ 2 * x ^ ν :=
    (Nat.cast_le.mpr (Finset.sup_le (fun n hn => Nat.le_floor (hN n hn)))).trans
      (Nat.floor_le (by positivity))
  have hprod : ((N.sup id : ℕ) : ℝ) * ⌊x ^ c2SExponent ν ε⌋₊ ≤ x := by
    have he : ((N.sup id : ℕ) : ℝ) * ⌊x ^ c2SExponent ν ε⌋₊ ≤
        2 * Real.sqrt x := by
      calc
        _ ≤ (2 * x ^ ν) * x ^ c2SExponent ν ε :=
          mul_le_mul hsup (Nat.floor_le (by positivity)) (Nat.cast_nonneg _) (by positivity)
        _ ≤ 2 * Real.sqrt x := by nlinarith
    have hsqrt := Real.sq_sqrt hx₀.le
    have hsqrt₀ := Real.sqrt_nonneg x
    nlinarith
  have hf : (1 : ℝ) ≤ ⌊x ^ c2SExponent ν ε⌋₊ := by
    exact_mod_cast (Nat.le_floor (by simpa using hS) : 1 ≤ ⌊x ^ c2SExponent ν ε⌋₊)
  have hn : ((N.sup id : ℕ) : ℝ) ≤ x :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) hf).trans hprod
  simpa only [wCoprimePairBound, Nat.cast_max, Nat.cast_ofNat, Nat.cast_mul] using
    max_le (by linarith : (2 : ℝ) ≤ x) (max_le hn hprod)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
