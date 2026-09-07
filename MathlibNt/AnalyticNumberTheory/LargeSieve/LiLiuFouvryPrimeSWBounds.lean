import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSW
import MathlibNt.SieveTheory.Richert1969Ordinary418Specialization

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset Filter
open scoped Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory
noncomputable section

/-- An individual genuine AP error is bounded by its term in unconditional BV. -/
theorem primeSW_small_prefix (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      2 ≤ N → ∀ d ∈ Icc 1 (LiuWeight.panModulusCutoff N C),
      ∀ x ∈ Icc 2 N, ∀ b ∈ AnalyticNumberTheory.Sieve.unitResidues d,
      |primeAPError x d b| ≤ K * (N : ℝ) / Real.log N ^ A := by
  obtain ⟨C, hC, K, hK, hBV⟩ := richert418 A hA
  refine ⟨C, hC, K, hK, ?_⟩
  filter_upwards [hBV] with N hN
  intro hN2 d hd x hx b hb
  exact ((abs_primeAPError_le_residueMax hb).trans
    (primeAPResidueMaxError_le_prefixMax hx)).trans
    ((single_le_sum (fun q _ => primeAPPrefixMaxError_nonneg N q) hd).trans (hN hN2))

/-- Literal interval subtraction for an arbitrary fixed predicate. -/
theorem primeSWSum_Ioc (P : ℕ → Prop) [DecidablePred P] {u v : ℕ} (huv : u ≤ v) :
    primeSWSum (Ioc u v) P = primeSWSum (range (v + 1)) P -
      primeSWSum (range (u + 1)) P := by
  have he : Ioc u v = range (v + 1) \ range (u + 1) := by
    apply Finset.ext
    intro n
    constructor
    · intro hn
      obtain ⟨hnu, hnv⟩ := mem_Ioc.mp hn
      exact mem_sdiff.mpr ⟨mem_range.mpr (by omega), fun hn => by
        have := mem_range.mp hn
        omega⟩
    · intro hn
      obtain ⟨hnv, hnu⟩ := mem_sdiff.mp hn
      exact mem_Ioc.mpr ⟨by
        have : ¬n < u + 1 := fun h => hnu (mem_range.mpr h)
        omega, by have := mem_range.mp hnv; omega⟩
  unfold primeSWSum
  rw [he]
  exact eq_sub_iff_add_eq.mpr
    (sum_sdiff (f := fun n => if P n then primeSWBeta n else 0)
      (range_mono (by omega : u + 1 ≤ v + 1)))

/-- No rounding correction is lost: the support is exactly the natural Ioc. -/
theorem primeSWInterval_AP_eq_sub {u v : ℝ} (huv : u ≤ v) (d b : ℕ) :
    primeSWSum (primeSWInterval u v) (fun n => Nat.ModEq d n b) =
      (BombieriVinogradov.primesInAP ⌊v⌋₊ d b : ℝ) -
        (BombieriVinogradov.primesInAP ⌊u⌋₊ d b : ℝ) := by
  rw [primeSWInterval, primeSWSum_Ioc _ (Nat.floor_mono huv)]
  simp only [primeSWSum_eq_card, BombieriVinogradov.primesInAP]

/-- Canonicalization does not change the actual prime count. -/
theorem primeSW_primesInAP_mod (x d b : ℕ) :
    BombieriVinogradov.primesInAP x d (b % d) =
      BombieriVinogradov.primesInAP x d b := by
  unfold BombieriVinogradov.primesInAP
  simp only [Nat.ModEq, Nat.mod_mod]
  rfl

/-- Prefix maximal bounds apply to every integer representative of a reduced class. -/
theorem primeSW_error_le_prefix {N x d b : ℕ} (hx : x ∈ Icc 2 N)
    (hd : 0 < d) (hb : b.Coprime d) :
    |primeAPError x d b| ≤ primeAPPrefixMaxError N d := by
  have hm : b % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt b hd), ?_⟩
    change (b % d).gcd d = 1
    rw [(Nat.mod_modEq b d).gcd_eq, hb.gcd_eq_one]
  have he : primeAPError x d (b % d) = primeAPError x d b := by
    rw [primeAPError, primeAPError, primeSW_primesInAP_mod]
  rw [← he]
  exact (abs_primeAPError_le_residueMax hm).trans
    (primeAPResidueMaxError_le_prefixMax hx)

/-- The same unconditional BV constant controls every moving interval endpoint. -/
theorem primeSW_interval_li_bound {N : ℕ} {u v : ℝ} (huv : u ≤ v)
    (hu : ⌊u⌋₊ ∈ Icc 2 N) (hv : ⌊v⌋₊ ∈ Icc 2 N)
    {d b : ℕ} (hd : 0 < d) (hb : b.Coprime d) :
    |primeSWSum (primeSWInterval u v) (fun n => Nat.ModEq d n b) -
      (logarithmicIntegral ⌊v⌋₊ - logarithmicIntegral ⌊u⌋₊) / d.totient| ≤
        2 * primeAPPrefixMaxError N d := by
  rw [primeSWInterval_AP_eq_sub huv]
  have he : (BombieriVinogradov.primesInAP ⌊v⌋₊ d b : ℝ) -
      (BombieriVinogradov.primesInAP ⌊u⌋₊ d b : ℝ) -
      (logarithmicIntegral ⌊v⌋₊ - logarithmicIntegral ⌊u⌋₊) / d.totient =
      primeAPError ⌊v⌋₊ d b - primeAPError ⌊u⌋₊ d b := by
    unfold primeAPError
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (primeSW_error_le_prefix hv hd hb)
    (primeSW_error_le_prefix hu hd hb)).trans_eq (by ring))

/-- There are at most `d` divisors of a positive modulus. -/
theorem primeSW_tau_two_le (d : ℕ) : fouvryTau 2 d ≤ d := by
  rw [fouvryTau_two]
  calc
    d.divisors.card ≤ (Icc 1 d).card := card_le_card (by
      intro n hn
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hn,
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hn).2)
          (Nat.dvd_of_mem_divisors hn)⟩)
    _ = d := by simp

/-- The normalization by the actual coprime mass differs from `li` by
ordinary prime-counting error and explicitly retained prime-divisor losses. -/
theorem primeSW_interval_discrepancy_bound {N : ℕ} {u v : ℝ} (huv : u ≤ v)
    (hu : ⌊u⌋₊ ∈ Icc 2 N) (hv : ⌊v⌋₊ ∈ Icc 2 N)
    {d h b : ℕ} (hd : 0 < d) (hh : 0 < h) (hb : b.Coprime d) :
    |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤
      2 * primeAPPrefixMaxError N d + 2 * primeAPPrefixMaxError N 1 +
        d + 2 * (fouvryTau 2 h : ℝ) := by
  let S := primeSWInterval u v
  let L := logarithmicIntegral ⌊v⌋₊ - logarithmicIntegral ⌊u⌋₊
  have hφ : (1 : ℝ) ≤ d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφ0 : (0 : ℝ) ≤ d.totient := Nat.cast_nonneg _
  have htot := primeSW_interval_li_bound huv hu hv (d := 1) (b := 0)
    (by omega) (by decide)
  have htrue : primeSWSum S (fun n => Nat.ModEq 1 n 0) = primeSWSum S (fun _ => True) := by
    unfold primeSWSum
    simp only [Nat.ModEq, Nat.mod_one, ite_true]
  rw [show Nat.totient 1 = 1 from rfl, Nat.cast_one, div_one, htrue] at htot
  have hmass : |primeSWSum S (fun n => n.Coprime d) - primeSWSum S (fun _ => True)| ≤
      (d : ℝ) := by
    have hp := primeSWSum_sieve_abs_sub_le S (fun _ => True) hd.ne'
    simp only [true_and] at hp
    exact hp.trans (by exact_mod_cast primeSW_tau_two_le d)
  have hmean : |primeSWSum S (fun n => n.Coprime d) - L| ≤
      (d : ℝ) + 2 * primeAPPrefixMaxError N 1 :=
    (abs_sub_le _ _ _).trans (add_le_add hmass htot)
  have hAP := primeSW_interval_li_bound huv hu hv hd hb
  have he : betaCoprimeAPDiscrepancy S primeSWBeta d 1 b =
      (primeSWSum S (fun n => Nat.ModEq d n b) - L / d.totient) -
        (primeSWSum S (fun n => n.Coprime d) - L) / d.totient := by
    rw [primeSW_discrepancy_eq]
    simp only [Nat.coprime_one_right_eq_true, true_and, mul_one]
    ring
  have hplain : |betaCoprimeAPDiscrepancy S primeSWBeta d 1 b| ≤
      2 * primeAPPrefixMaxError N d + 2 * primeAPPrefixMaxError N 1 + d := by
    rw [he]
    calc
      _ ≤ |primeSWSum S (fun n => Nat.ModEq d n b) - L / d.totient| +
          |(primeSWSum S (fun n => n.Coprime d) - L) / d.totient| := abs_sub _ _
      _ ≤ 2 * primeAPPrefixMaxError N d +
          ((d : ℝ) + 2 * primeAPPrefixMaxError N 1) / d.totient := by
        rw [abs_div, Nat.abs_cast]
        exact add_le_add hAP (div_le_div_of_nonneg_right hmean hφ0)
      _ ≤ _ := by
        have hE := primeAPPrefixMaxError_nonneg N 1
        have := div_le_self (show 0 ≤ (d : ℝ) + 2 * primeAPPrefixMaxError N 1 by
          positivity) hφ
        linarith
  have hp := primeSW_sieve_discrepancy_sub_le S hd hh b
  have ht := abs_add_le
    (betaCoprimeAPDiscrepancy S primeSWBeta d h b -
      betaCoprimeAPDiscrepancy S primeSWBeta d 1 b)
    (betaCoprimeAPDiscrepancy S primeSWBeta d 1 b)
  rw [sub_add_cancel] at ht
  exact ht.trans (by linarith)

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
