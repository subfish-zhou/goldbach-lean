import MathlibNt.SieveTheory.LiLiuGoldbachG10Cofactor

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachG10BuchstabBridge (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The genuine triple layer attached to the corrected closed G10 carrier. -/
noncomputable def goldbachWeightT16 (A : Finset ℕ) (N : ℕ) (b c : ℝ) : ℤ :=
  ∑ rs ∈ goldbachC10Pairs N b c,
    ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
      literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ)

theorem goldbachWeightT16_nonneg (A : Finset ℕ) (N : ℕ) (b c : ℝ) :
    0 ≤ goldbachWeightT16 A N b c := by
  unfold goldbachWeightT16
  refine Finset.sum_nonneg ?_
  intro rs hrs
  refine Finset.sum_nonneg ?_
  intro t ht
  exact literalH_nonneg A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ)

private theorem goldbachG10Bridge_literalH_le_of_pointwise
    {A : Finset ℕ} {M₁ d₁ M₂ d₂ : ℕ} {x₁ x₂ : ℝ}
    (hpoint : ∀ n : ℕ, literalHPoint M₁ d₁ x₁ n → literalHPoint M₂ d₂ x₂ n) :
    literalH A M₁ d₁ x₁ ≤ literalH A M₂ d₂ x₂ := by
  unfold literalH
  have hsubset : A.filter (literalHPoint M₁ d₁ x₁) ⊆ A.filter (literalHPoint M₂ d₂ x₂) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnA, hnPoint⟩
    exact Finset.mem_filter.mpr ⟨hnA, hpoint n hnPoint⟩
  exact_mod_cast Finset.card_le_card hsubset

private theorem goldbachG10Bridge_literalH_mono_cutoff
    (A : Finset ℕ) (M d : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    literalH A M d y ≤ literalH A M d x := by
  refine goldbachG10Bridge_literalH_le_of_pointwise ?_
  intro n hn
  exact ⟨hn.1, survivesSieve_mono hxy hn.2⟩

private theorem goldbachG10Bridge_buchstab_carrier_subset
    {N : ℕ} {rs : ℕ × ℕ} :
    (siftingPrimes (N * goldbachC10Prod rs) (goldbachC10Cutoff N rs)).filter
        (fun t : ℕ => (rs.2 : ℝ) ≤ (t : ℝ)) ⊆
      goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs) := by
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨htSift, hst⟩
  rcases mem_siftingPrimes.mp htSift with ⟨htPrime, htUpper, htModulus⟩
  have htN : ¬t ∣ N := by
    intro htN
    exact htModulus <| by
      simpa [Nat.mul_comm] using
        (dvd_mul_of_dvd_right htN (goldbachC10Prod rs))
  exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htN, hst, htUpper.le⟩

private theorem goldbachG10Bridge_buchstab_summand_eq
    (A : Finset ℕ) (N : ℕ) {rs : ℕ × ℕ} {t : ℕ}
    (ht : t ∈
      (siftingPrimes (N * goldbachC10Prod rs) (goldbachC10Cutoff N rs)).filter
        (fun t : ℕ => (rs.2 : ℝ) ≤ (t : ℝ))) :
    literalH (A.filter fun n => goldbachC10Prod rs ∣ n)
        (N * goldbachC10Prod rs) t (t : ℝ) =
      literalH A (N * goldbachC10Prod rs) (goldbachC10Prod rs * t) (t : ℝ) := by
  rcases Finset.mem_filter.mp ht with ⟨htSift, _⟩
  rcases mem_siftingPrimes.mp htSift with ⟨htPrime, _, htModulus⟩
  have htProd : ¬t ∣ goldbachC10Prod rs := by
    intro htProd
    exact htModulus <| by
      simpa [Nat.mul_comm] using (dvd_mul_of_dvd_right htProd N)
  have hcop : Nat.Coprime (goldbachC10Prod rs) t :=
    (htPrime.coprime_iff_not_dvd.mpr htProd).symm
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    literalH_filter_mul_of_coprime A (N * goldbachC10Prod rs) (goldbachC10Prod rs) t (t : ℝ) hcop

private theorem goldbachG10Bridge_correctedTriple_le_t16Cell
    (A : Finset ℕ) (N r s t : ℕ)
    (hsPrime : s.Prime) (hst : (s : ℝ) ≤ (t : ℝ)) :
    literalH A ((N * r) * s) (r * s * t) (t : ℝ) ≤
      literalH A (N * r) (r * s * t) (s : ℝ) := by
  refine goldbachG10Bridge_literalH_le_of_pointwise ?_
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro ℓ hℓPrime hℓn hℓNr
  by_cases hℓs : ℓ ∣ s
  · have hEq : ℓ = s := (Nat.prime_dvd_prime_iff_eq hℓPrime hsPrime).mp hℓs
    subst hEq
    exact le_rfl
  · have hℓNrs : ¬ℓ ∣ (N * r) * s := by
      intro hMul
      rcases hℓPrime.dvd_mul.mp hMul with hNr | hs
      · exact hℓNr hNr
      · exact hℓs hs
    exact hst.trans (hn.2 ℓ hℓPrime hℓn hℓNrs)

private theorem goldbachS5Closed_carrier_eq_goldbachC10Pairs
    (N : ℕ) (b c : ℝ) :
    (goldbachS4Pairs N b).filter
        (fun rs : ℕ × ℕ => (rs.1 : ℝ) ≤ c ∧ c ≤ (rs.2 : ℝ)) =
      goldbachC10Pairs N b c := by
  ext rs
  constructor
  · intro hrs
    rcases Finset.mem_filter.mp hrs with ⟨hrsS4, hrc, hcs⟩
    rcases Finset.mem_filter.mp hrsS4 with ⟨_, hrs'⟩
    exact mem_goldbachC10Pairs_iff.mpr
      ⟨hrs'.1, hrs'.2.1, hrs'.2.2.1, hrs'.2.2.2.1, hrc, hcs, hrs'.2.2.2.2.2⟩
  · intro hrs
    rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, hcop, hbr, hrc, hcs, hrsq⟩
    have hrsLe : rs.1 ≤ rs.2 := by
      exact_mod_cast (le_trans hrc hcs)
    have hrRange : rs.1 ∈ range (N + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le <|
        Nat.le_trans (Nat.le_mul_of_pos_right rs.1 (pow_pos hsPrime.pos 2)) hrsq
    have hsSq : rs.2 ≤ rs.2 ^ 2 := by
      calc
        rs.2 = rs.2 * 1 := by simp
        _ ≤ rs.2 * rs.2 := by
              gcongr
              exact hsPrime.one_le
        _ = rs.2 ^ 2 := by rw [pow_two]
    have hsRange : rs.2 ∈ range (N + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le <|
        le_trans hsSq <|
          le_trans (Nat.le_mul_of_pos_left (rs.2 ^ 2) hrPrime.pos) hrsq
    refine Finset.mem_filter.mpr ⟨?_, hrc, hcs⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simpa [Finset.mem_product] using And.intro hrRange hsRange
    · exact ⟨hrPrime, hsPrime, hcop, hbr, hrsLe, hrsq⟩

theorem goldbachS5Closed_eq_sum_goldbachC10Pairs
    (A : Finset ℕ) (N : ℕ) (b c : ℝ) :
    goldbachS5Closed A N b c =
      ∑ rs ∈ goldbachC10Pairs N b c,
        literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) := by
  unfold goldbachS5Closed
  rw [goldbachS5Closed_carrier_eq_goldbachC10Pairs]

theorem goldbachC10Pair_cell_le_goldbachG10CorrectedCell_add_t16Slice
    (A : Finset ℕ) {N : ℕ} {b c : ℝ} {rs : ℕ × ℕ}
    (hrs : rs ∈ goldbachC10Pairs N b c) :
    literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) ≤
      literalH A (N * goldbachC10Prod rs) (goldbachC10Prod rs) (goldbachC10Cutoff N rs) +
        ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
          literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, hsPrime, _, _, _, _, _⟩
  let d : ℕ := goldbachC10Prod rs
  let M : ℕ := N * d
  let S : Finset ℕ :=
    (siftingPrimes M (goldbachC10Cutoff N rs)).filter
      (fun t : ℕ => (rs.2 : ℝ) ≤ (t : ℝ))
  have hboundary :
      literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) =
        literalH A M d (rs.2 : ℝ) := by
    symm
    simpa [M, d, goldbachC10Prod, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      literalH_mul_right_cutoff_prime_eq A (N * rs.1) (rs.1 * rs.2) rs.2 hsPrime
  by_cases hcut : goldbachC10Cutoff N rs ≤ (rs.2 : ℝ)
  · have hmono : literalH A M d (rs.2 : ℝ) ≤ literalH A M d (goldbachC10Cutoff N rs) := by
      exact goldbachG10Bridge_literalH_mono_cutoff A M d hcut
    have hsliceNonneg :
        0 ≤
          ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
            literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro t ht
      exact literalH_nonneg A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ)
    calc
      literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) = literalH A M d (rs.2 : ℝ) := hboundary
      _ ≤ literalH A M d (goldbachC10Cutoff N rs) := hmono
      _ ≤
          literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
              literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
            omega
  · have hsCutoff : (rs.2 : ℝ) ≤ goldbachC10Cutoff N rs := le_of_lt (lt_of_not_ge hcut)
    have hbuch :
        literalH A M d (rs.2 : ℝ) - literalH A M d (goldbachC10Cutoff N rs) =
          ∑ t ∈ S,
            literalH (A.filter fun n => d ∣ n) M t (t : ℝ) := by
      simpa [M, d, S] using literalH_buchstab_interval A M d hsCutoff
    have hbuchEq :
        literalH A M d (rs.2 : ℝ) =
          literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ S,
              literalH (A.filter fun n => d ∣ n) M t (t : ℝ) := by
      omega
    have hsumEq :
        ∑ t ∈ S, literalH (A.filter fun n => d ∣ n) M t (t : ℝ) =
          ∑ t ∈ S, literalH A M (d * t) (t : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      simpa [M, d, S, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        goldbachG10Bridge_buchstab_summand_eq A N (rs := rs) (t := t) ht
    have hsumLeSlice :
        ∑ t ∈ S, literalH A M (d * t) (t : ℝ) ≤
          ∑ t ∈ S, literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      have hst : (rs.2 : ℝ) ≤ (t : ℝ) := (Finset.mem_filter.mp ht).2
      simpa [M, d, goldbachC10Prod, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        goldbachG10Bridge_correctedTriple_le_t16Cell A N rs.1 rs.2 t hsPrime hst
    have hsubset :
        S ⊆ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs) :=
      goldbachG10Bridge_buchstab_carrier_subset (N := N) (rs := rs)
    have hsumLeTarget :
        ∑ t ∈ S, literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) ≤
          ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
            literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro t htS htNot
      exact literalH_nonneg A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ)
    calc
      literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ) = literalH A M d (rs.2 : ℝ) := hboundary
      _ = literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ S, literalH (A.filter fun n => d ∣ n) M t (t : ℝ) := hbuchEq
      _ = literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ S, literalH A M (d * t) (t : ℝ) := by rw [hsumEq]
      _ ≤ literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ S, literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hsumLeSlice (literalH A M d (goldbachC10Cutoff N rs))
      _ ≤ literalH A M d (goldbachC10Cutoff N rs) +
            ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
              literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hsumLeTarget (literalH A M d (goldbachC10Cutoff N rs))

theorem goldbachS5Closed_le_goldbachG10Corrected_add_goldbachWeightT16
    (A : Finset ℕ) (N : ℕ) (b c : ℝ) (_hb : 2 ≤ b) (_hbc : b ≤ c) :
    goldbachS5Closed A N b c ≤ goldbachG10Corrected A N b c + goldbachWeightT16 A N b c := by
  rw [goldbachS5Closed_eq_sum_goldbachC10Pairs, goldbachG10Corrected, goldbachWeightT16]
  calc
    ∑ rs ∈ goldbachC10Pairs N b c, literalH A (N * rs.1) (rs.1 * rs.2) (rs.2 : ℝ)
      ≤
        ∑ rs ∈ goldbachC10Pairs N b c,
          (literalH A (N * goldbachC10Prod rs) (goldbachC10Prod rs) (goldbachC10Cutoff N rs) +
            ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
              literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro rs hrs
          exact goldbachC10Pair_cell_le_goldbachG10CorrectedCell_add_t16Slice
            (A := A) (N := N) (b := b) (c := c) (rs := rs) hrs
    _ =
        (∑ rs ∈ goldbachC10Pairs N b c,
          literalH A (N * goldbachC10Prod rs) (goldbachC10Prod rs) (goldbachC10Cutoff N rs)) +
        ∑ rs ∈ goldbachC10Pairs N b c,
          ∑ t ∈ goldbachClosedPrimes N (rs.2 : ℝ) (goldbachC10Cutoff N rs),
            literalH A (N * rs.1) (rs.1 * rs.2 * t) (rs.2 : ℝ) := by
          rw [Finset.sum_add_distrib]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig