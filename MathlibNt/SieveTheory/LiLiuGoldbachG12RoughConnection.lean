import MathlibNt.SieveTheory.LiLiuGoldbachG11RoughSandwich

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Original closed cross carrier, with coordinates t, s, r, q. -/
noncomputable def goldbachG12Labels (N : ℕ) (z b c : ℝ) : Finset GoldbachG11Label :=
  (goldbachClosedPrimes N b c).sigma fun _t =>
    (goldbachClosedPrimes N z b).sigma fun s =>
      (goldbachClosedPrimes N z s).sigma fun r =>
        goldbachClosedPrimes N r s

theorem goldbachG12Labels_sum (N : ℕ) (z b c : ℝ) (f : GoldbachG11Label → ℤ) :
    ∑ v ∈ goldbachG12Labels N z b c, f v =
      ∑ t ∈ goldbachClosedPrimes N b c,
        ∑ s ∈ goldbachClosedPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z s,
            ∑ q ∈ goldbachClosedPrimes N r s, f ⟨t, s, r, q⟩ := by
  simp [goldbachG12Labels, Finset.sum_sigma']

theorem goldbachWeightG12_eq_label_sum (A : Finset ℕ) (N : ℕ) (z b c : ℝ) :
    goldbachWeightG12 A N z b c =
      ∑ v ∈ goldbachG12Labels N z b c,
        literalH A (N * v.2.2.1) (goldbachG11LabelProd v) v.2.2.2 := by
  rw [goldbachG12Labels_sum]
  rfl

theorem mem_goldbachG12Labels_iff {N r q s t : ℕ} {z b c : ℝ} :
    (⟨t, s, r, q⟩ : GoldbachG11Label) ∈ goldbachG12Labels N z b c ↔
      r.Prime ∧ q.Prime ∧ s.Prime ∧ t.Prime ∧
        Nat.Coprime (r * q * s * t) N ∧
        z ≤ (r : ℝ) ∧ r ≤ q ∧ q ≤ s ∧ (s : ℝ) ≤ b ∧ b ≤ (t : ℝ) ∧
          (t : ℝ) ≤ c := by
  simp only [goldbachG12Labels, Finset.mem_sigma, mem_goldbachClosedPrimes_iff]
  constructor
  · rintro ⟨⟨ht, htN, hbt, htc⟩, ⟨hs, hsN, _, hsb⟩,
      ⟨hr, hrN, hzr, _⟩, hq, hqN, hrq, hqs⟩
    refine ⟨hr, hq, hs, ht, ?_, hzr, ?_, ?_, hsb, hbt, htc⟩
    · exact (((hr.coprime_iff_not_dvd.mpr hrN).mul_left
        (hq.coprime_iff_not_dvd.mpr hqN)).mul_left
        (hs.coprime_iff_not_dvd.mpr hsN)).mul_left
        (ht.coprime_iff_not_dvd.mpr htN)
    · exact_mod_cast hrq
    · exact_mod_cast hqs
  · rintro ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, hsb, hbt, htc⟩
    rcases Nat.coprime_mul_iff_left.mp hcop with ⟨hrqs, htN⟩
    rcases Nat.coprime_mul_iff_left.mp hrqs with ⟨hrqN, hsN⟩
    rcases Nat.coprime_mul_iff_left.mp hrqN with ⟨hrN, hqN⟩
    have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
    have hqsR : (q : ℝ) ≤ s := by exact_mod_cast hqs
    exact ⟨⟨ht, ht.coprime_iff_not_dvd.mp htN, hbt, htc⟩,
      ⟨hs, hs.coprime_iff_not_dvd.mp hsN, (hzr.trans hrqR).trans hqsR, hsb⟩,
      ⟨hr, hr.coprime_iff_not_dvd.mp hrN, hzr, hrqR.trans hqsR⟩,
      hq, hq.coprime_iff_not_dvd.mp hqN, hrqR, hqsR⟩

/-- Membership itself supplies all endpoint order needed for the G11 cell API. -/
theorem goldbachG12Labels_subset_goldbachG11Labels (N : ℕ) (z b c : ℝ) :
    goldbachG12Labels N z b c ⊆ goldbachG11Labels N z c := by
  rintro ⟨t, s, r, q⟩ hv
  rcases mem_goldbachG12Labels_iff.mp hv with
    ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, hsb, hbt, htc⟩
  exact mem_goldbachG11Labels_iff.mpr
    ⟨hr, hq, hs, ht, hcop, hzr, hrq, hqs, by exact_mod_cast hsb.trans hbt, htc⟩

theorem goldbachG12LabelProd_pos {N : ℕ} {z b c : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG12Labels N z b c) : 0 < goldbachG11LabelProd v :=
  goldbachG11LabelProd_pos (goldbachG12Labels_subset_goldbachG11Labels N z b c hv)

open Classical in
/-- The rough count is the actual quotient-filter cardinal, not a modulus-N sieve. -/
theorem goldbachG12RoughCount_eq_filter (N : ℕ) (ε : ℝ) (v : GoldbachG11Label)
    {z b c : ℝ} (hε : 0 ≤ ε) (hv : v ∈ goldbachG12Labels N z b c) :
    goldbachG11RoughCount N ε v =
      (((goldbachDifferenceCarrier N ε).filter fun n =>
        goldbachG11LabelProd v ∣ n ∧
          SurvivesSieve 1 v.2.2.2 (n / goldbachG11LabelProd v)).card : ℤ) :=
  goldbachG11RoughCount_eq_filter N ε v hε (goldbachG12LabelProd_pos hv)

theorem goldbachG12_cell_sandwich (N : ℕ) (ε : ℝ) (v : GoldbachG11Label)
    {z b c : ℝ} (hε : 0 ≤ ε) (hv : v ∈ goldbachG12Labels N z b c) :
    goldbachG11RoughCount N ε v ≤
        literalH (goldbachDifferenceCarrier N ε) (N * v.2.2.1)
          (goldbachG11LabelProd v) v.2.2.2 ∧
      literalH (goldbachDifferenceCarrier N ε) (N * v.2.2.1)
          (goldbachG11LabelProd v) v.2.2.2 ≤
        goldbachG11RoughCount N ε v +
          goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v +
          goldbachG11NCount (goldbachDifferenceCarrier N ε) N v :=
  goldbachG11_cell_sandwich N ε v hε
    (goldbachG12Labels_subset_goldbachG11Labels N z b c hv)

/-- Both bounds retain exactly the original cross labels, including repeated primes. -/
theorem goldbachWeightG12_roughQuotient_sandwich
    (N : ℕ) (ε z b c : ℝ) (hε : 0 ≤ ε) :
    (∑ v ∈ goldbachG12Labels N z b c, goldbachG11RoughCount N ε v) ≤
        goldbachWeightG12 (goldbachDifferenceCarrier N ε) N z b c ∧
      goldbachWeightG12 (goldbachDifferenceCarrier N ε) N z b c ≤
        (∑ v ∈ goldbachG12Labels N z b c, goldbachG11RoughCount N ε v) +
          (∑ v ∈ goldbachG12Labels N z b c,
            goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v) +
          (∑ v ∈ goldbachG12Labels N z b c,
            goldbachG11NCount (goldbachDifferenceCarrier N ε) N v) := by
  rw [goldbachWeightG12_eq_label_sum]
  constructor
  · exact Finset.sum_le_sum fun v hv => (goldbachG12_cell_sandwich N ε v hε hv).1
  · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v hv => (goldbachG12_cell_sandwich N ε v hε hv).2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
