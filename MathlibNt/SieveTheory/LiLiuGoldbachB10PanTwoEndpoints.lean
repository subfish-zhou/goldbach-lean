import MathlibNt.SieveTheory.LiLiuGoldbachB10PanPrefixes
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate

open scoped BigOperators

open Finset
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB10PanTwoEndpoints (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem B10PanTwoEndpoints_residue_mem_unitResidues
    {N d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d := by
  rw [AnalyticNumberTheory.Sieve.unitResidues]
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_range.mpr (Nat.mod_lt N (lt_of_lt_of_le Nat.zero_lt_one hd))
  · exact (ZMod.coprime_mod_iff_coprime N d).2 hdN.symm

private theorem B10PanTwoEndpoints_intervalMaxL_nonneg
    (main : ℝ → ℝ) (Y A₁ A₂ d : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  by_cases hS : (AnalyticNumberTheory.Sieve.unitResidues d).Nonempty
  · rw [dif_pos hS]
    have hmem :
        ((AnalyticNumberTheory.Sieve.unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|)).max'
            (Finset.image_nonempty.mpr hS) ∈
          (AnalyticNumberTheory.Sieve.unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|) :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
    rw [← hl]
    exact abs_nonneg _
  · rw [dif_neg hS]

private theorem B10PanTwoEndpoints_abs_intervalSum_le_maxL
    {N Y A₁ A₂ d : ℕ} {main : ℝ → ℝ} {f : ℕ → ℝ}
    (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d (N % d) f| ≤
      liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  have hl : N % d ∈ AnalyticNumberTheory.Sieve.unitResidues d :=
    B10PanTwoEndpoints_residue_mem_unitResidues hd hdN
  have hS : (AnalyticNumberTheory.Sieve.unitResidues d).Nonempty := ⟨N % d, hl⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  exact Finset.le_max'
    ((AnalyticNumberTheory.Sieve.unitResidues d).image
      (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|))
    _
    (Finset.mem_image.mpr ⟨N % d, hl, rfl⟩)

private theorem B10PanTwoEndpoints_remainderIndex_subset_cutoff
    {N M D : ℕ} {B : ℝ}
    (hD : D ≤ panModulusCutoff M B) :
    (Icc 1 D).filter (fun d => Nat.Coprime d N) ⊆ Icc 1 (panModulusCutoff M B) := by
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdIcc, _⟩
  rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hdD⟩
  exact Finset.mem_Icc.mpr ⟨hd1, hdD.trans hD⟩

/-- Two-endpoint aggregate bound for the actual finite `B10` Pan remainder,
consuming the existing bounded-coefficient Pan aggregate theorem at `N` and at
the lower endpoint `Y = ⌊εN⌋`.  The geometric support hypotheses remain
explicit. -/
theorem goldbachB10PanPrefixRemainder_twoEndpoints_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ K : ℕ,
      ∀ {N Y D A₁ A₂ : ℕ} {ε b c : ℝ},
        Y = ⌊ε * (N : ℝ)⌋₊ →
        K ≤ N →
        K ≤ Y →
        0 < ε →
        ε < 1 →
        (∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) →
        (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        (A₂ : ℝ) ≤ (Y : ℝ) ^ (2 / 3 : ℝ) →
        Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
        Real.log (Y : ℝ) ^ (2 * B) ≤ A₁ →
        D ≤ panModulusCutoff N B →
        D ≤ panModulusCutoff Y B →
        ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N),
          |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c| ≤
            C * ((N : ℝ) / Real.log (N : ℝ) ^ U +
              (Y : ℝ) / Real.log (Y : ℝ) ^ U) := by
  obtain ⟨C, hC, B, hB, K, hagg⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  refine ⟨C, hC, B, hB, K, ?_⟩
  intro N Y D A₁ A₂ ε b c hY hKN hKY hε0 hε1 hsupp hA₂N hA₂Y hA₁N hA₁Y hDN hDY
  let S : Finset ℕ := (Icc 1 D).filter (fun d => Nat.Coprime d N)
  let EN : ℕ → ℝ := fun d =>
    liuMainPanCoprimeIntervalMaxL
      (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d
      (goldbachC10CoeffReal N b c)
  let EY : ℕ → ℝ := fun d =>
    liuMainPanCoprimeIntervalMaxL
      (liuLogarithmicIntegral goldbachB10PanKappa0) Y A₁ A₂ d
      (goldbachC10CoeffReal N b c)
  have hf : ∀ a, |goldbachC10CoeffReal N b c a| ≤ 1 :=
    abs_goldbachC10CoeffReal_le_one N b c
  have haggN :
      ∑ d ∈ Icc 1 (panModulusCutoff N B), EN d ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
    simpa [EN, goldbachB10PanKappa0] using
      hagg N hKN A₁ A₂ (goldbachC10CoeffReal N b c) hA₂N hA₁N hf
  have haggY :
      ∑ d ∈ Icc 1 (panModulusCutoff Y B), EY d ≤
        C * (Y : ℝ) / Real.log (Y : ℝ) ^ U := by
    simpa [EY, goldbachB10PanKappa0] using
      hagg Y hKY A₁ A₂ (goldbachC10CoeffReal N b c) hA₂Y hA₁Y hf
  have hpoint :
      ∀ d ∈ S, |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c| ≤ EN d + EY d := by
    intro d hdS
    rcases Finset.mem_filter.mp hdS with ⟨hdIcc, hdN⟩
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    have hrem :=
      abs_goldbachB10PanPrefixRemainder_le
        (N := N) (d := d) (A₁ := A₁) (A₂ := A₂) (ε := ε) (b := b) (c := c)
        hd hdN hε0 hε1 hsupp
    have hmaxN :
        |liuMainPanCoprimeIntervalSum
            (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d (N % d)
            (goldbachC10CoeffReal N b c)| ≤ EN d := by
      simpa [EN] using
        (B10PanTwoEndpoints_abs_intervalSum_le_maxL
          (N := N) (Y := N)
          (A₁ := A₁) (A₂ := A₂) (d := d)
          (main := liuLogarithmicIntegral goldbachB10PanKappa0)
          (f := goldbachC10CoeffReal N b c) hd hdN)
    have hmaxY :
        |liuMainPanCoprimeIntervalSum
            (liuLogarithmicIntegral goldbachB10PanKappa0) ⌊ε * (N : ℝ)⌋₊
            A₁ A₂ d (N % d) (goldbachC10CoeffReal N b c)| ≤ EY d := by
      simpa [EY, hY] using
        (B10PanTwoEndpoints_abs_intervalSum_le_maxL
          (N := N) (Y := ⌊ε * (N : ℝ)⌋₊)
          (A₁ := A₁) (A₂ := A₂) (d := d)
          (main := liuLogarithmicIntegral goldbachB10PanKappa0)
          (f := goldbachC10CoeffReal N b c) hd hdN)
    exact hrem.trans (add_le_add hmaxN hmaxY)
  have hsubsetN : S ⊆ Icc 1 (panModulusCutoff N B) :=
    B10PanTwoEndpoints_remainderIndex_subset_cutoff (N := N) (M := N) hDN
  have hsubsetY : S ⊆ Icc 1 (panModulusCutoff Y B) :=
    B10PanTwoEndpoints_remainderIndex_subset_cutoff (N := N) (M := Y) hDY
  have hsumN :
      ∑ d ∈ S, EN d ≤ ∑ d ∈ Icc 1 (panModulusCutoff N B), EN d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubsetN ?_
    intro d _ hdNot
    exact by
      simp only [EN]
      exact B10PanTwoEndpoints_intervalMaxL_nonneg
        (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d
        (goldbachC10CoeffReal N b c)
  have hsumY :
      ∑ d ∈ S, EY d ≤ ∑ d ∈ Icc 1 (panModulusCutoff Y B), EY d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubsetY ?_
    intro d _ hdNot
    exact by
      simp only [EY]
      exact B10PanTwoEndpoints_intervalMaxL_nonneg
        (liuLogarithmicIntegral goldbachB10PanKappa0) Y A₁ A₂ d
        (goldbachC10CoeffReal N b c)
  calc
    ∑ d ∈ S, |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c|
        ≤ ∑ d ∈ S, (EN d + EY d) := by
            exact Finset.sum_le_sum hpoint
    _ = (∑ d ∈ S, EN d) + ∑ d ∈ S, EY d := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ d ∈ Icc 1 (panModulusCutoff N B), EN d) +
          ∑ d ∈ Icc 1 (panModulusCutoff Y B), EY d := by
            exact add_le_add hsumN hsumY
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U +
          C * (Y : ℝ) / Real.log (Y : ℝ) ^ U := by
            exact add_le_add haggN haggY
    _ = C * ((N : ℝ) / Real.log (N : ℝ) ^ U +
          (Y : ℝ) / Real.log (Y : ℝ) ^ U) := by
            ring

/-- Direct floor-endpoint form of the two-endpoint aggregate bound. -/
theorem goldbachB10PanPrefixRemainder_floor_twoEndpoints_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ K : ℕ,
      ∀ {N D A₁ A₂ : ℕ} {ε b c : ℝ},
        K ≤ N →
        K ≤ ⌊ε * (N : ℝ)⌋₊ →
        0 < ε →
        ε < 1 →
        (∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) →
        (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        (A₂ : ℝ) ≤ ((⌊ε * (N : ℝ)⌋₊ : ℕ) : ℝ) ^ (2 / 3 : ℝ) →
        Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
        Real.log (((⌊ε * (N : ℝ)⌋₊ : ℕ) : ℝ)) ^ (2 * B) ≤ A₁ →
        D ≤ panModulusCutoff N B →
        D ≤ panModulusCutoff ⌊ε * (N : ℝ)⌋₊ B →
        ∑ d ∈ (Icc 1 D).filter (fun d => Nat.Coprime d N),
          |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c| ≤
            C * ((N : ℝ) / Real.log (N : ℝ) ^ U +
              ((⌊ε * (N : ℝ)⌋₊ : ℕ) : ℝ) /
                Real.log (((⌊ε * (N : ℝ)⌋₊ : ℕ) : ℝ)) ^ U) := by
  obtain ⟨C, hC, B, hB, K, htwo⟩ :=
    goldbachB10PanPrefixRemainder_twoEndpoints_log_saving U hU
  refine ⟨C, hC, B, hB, K, ?_⟩
  intro N D A₁ A₂ ε b c hKN hKY hε0 hε1 hsupp hA₂N hA₂Y hA₁N hA₁Y hDN hDY
  exact htwo (N := N) (Y := ⌊ε * (N : ℝ)⌋₊) (D := D) (A₁ := A₁) (A₂ := A₂)
    (ε := ε) (b := b) (c := c) rfl hKN hKY hε0 hε1 hsupp hA₂N hA₂Y hA₁N hA₁Y hDN hDY

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig