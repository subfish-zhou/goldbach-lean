import MathlibNt.SieveTheory.LiLiuGoldbachG11MixedDensityPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridPlainMass

open Finset
open scoped BigOperators Classical
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11MixedLevel (N : ℕ) (δ ρ : ℝ) (k : ℕ × ℕ) : ℝ :=
  if ρ^k.1 ≤ (N : ℝ)^(1/10 : ℝ) then goldbachG11GridLowLevel N δ ρ k
  else goldbachG11OrdinaryLevel N δ

def goldbachG11GridAnalyticMain (N : ℕ) (ε ρ δ θ C K : ℝ) : ℝ :=
  ∑ k ∈ goldbachG11GridUsed N ε ρ,
    fouvryG9UpperFactor N (goldbachG11MixedLevel N δ ρ k) C K θ*
      fouvryG9BaseEuler N (Real.sqrt N)*goldbachG11EulerCorrection N*goldbachG11GridPlainMass N ε ρ k

/-- Both actual main terms are evaluated through the existing external-family
analytic theorem. No progression-density gate remains on the right. All its
large-level gates are proved before epsilon and the changing mesh are supplied. -/
theorem goldbachG11MixedDensity_analytic_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧ ∀ δ θ : ℝ,
    0 ≤ δ → δ < 1/4 → 0 < θ → θ < 1/8 →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ ε ρ : ℝ,
    1 < ρ → ρ ≤ 5/4 →
      goldbachG11MixedDensityMain N ε ρ δ θ (Real.sqrt N) ≤
        goldbachG11GridAnalyticMain N ε ρ δ θ C K := by
  obtain ⟨C,hC,K,hK,hden⟩ := goldbachG11_weighted_density_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro δ θ hδ hδu hθ hθu
  obtain ⟨Q₀,hQ₀,hfinite⟩ := hden θ hθ hθu
  obtain ⟨M,hw⟩ := g9WF_exists_internal_level_gate hδ (by linarith) hθ Q₀
  obtain ⟨Ng,hNg,hg⟩ := goldbachG11OrdinaryLevel_gates hδ (by linarith) hθ
  refine ⟨max Ng ⌈M⌉₊,hNg.trans (le_max_left _ _),?_⟩
  intro N hN hEven ε ρ hρ hρu
  obtain ⟨hNng,hNm⟩ := max_le_iff.mp hN
  have hn4 : 4 ≤ N := hNg.trans hNng
  have hn4R : (4 : ℝ) ≤ N := by exact_mod_cast hn4
  have hn : (0 : ℝ) < N := by linarith
  have hNM : M ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNm)
  have hbig := (hg N hNng).1
  have hbase : 0 ≤ fouvryG9BaseEuler N (Real.sqrt N) :=
    g9_baseEuler_nonneg _ (fun p hp => (fouvryG9SievePrimes_odd hEven _ p hp).2)
  have hcorr : 0 ≤ goldbachG11EulerCorrection N := by
    unfold goldbachG11EulerCorrection
    have hd : 0 ≤ (N : ℝ)^(4/53 : ℝ)-2 := by linarith
    positivity
  let P := fouvryG9SievePrimes N (Real.sqrt N)
  let F := fun k => fouvryG9UpperFactor N (goldbachG11MixedLevel N δ ρ k) C K θ*
    fouvryG9BaseEuler N (Real.sqrt N)*goldbachG11EulerCorrection N
  have hlo : ∀ k ∈ goldbachG11LowGridUsed N ε ρ,
      (∑ m ∈ goldbachG11GridLong N ε ρ k, ∑ p ∈ goldbachG11GridShort N ρ k,
        goldbachG11RectangleWeight N (m,p)*externalDensity true P
          (externalInternalLevel (goldbachG11GridLowLevel N δ ρ k) θ) θ (Real.sqrt N)
          (progressionDensity (m*p))) ≤ F k*goldbachG11GridPlainMass N ε ρ k := by
    intro k hk
    have hka := (mem_filter.mp hk).1
    have hkc := (mem_filter.mp hk).2
    let T := (2/3 : ℝ)*ρ^k.1
    have hT : 1 ≤ T := by
      have hh := goldbachG11Grid_short_scale_lower hρ hρu hka
      dsimp [T]
      linarith
    have hTu := goldbachG11LowGrid_short_upper hρ hk
    obtain ⟨_,_,hQ,_,hQN⟩ := hw N T hNM hT hTu
    have hzQ := (g9WF_sqrt_cutoff hn4R hT hTu hδ hδu).2
    have hf := hfinite N hn4 hEven hbig (goldbachG11GridLowLevel N δ ρ k) hQ hQN hzQ
    have ha : ∀ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
        goldbachG11RectangleWeight N v ≠ 0 → 0 < v.1*v.2 ∧
        (∀ p ∈ (v.1*v.2).primeFactors,(N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) ∧
        (v.1*v.2).primeFactors.card ≤ 21 := by
      rintro ⟨m,p⟩ hv hne
      obtain ⟨hm,hpV⟩ := mem_product.mp hv
      have hp : p.Prime := by
        by_contra h
        simp [goldbachG11RectangleWeight,primeSWBeta,h] at hne
      have hz := (goldbachG11GridShort_mem_iff hρ hρu hbig hka p).mp hpV
      exact goldbachG11_effectiveProduct_mul_prime_factors (mem_filter.mp hm).1 hp
        ((le_max_right _ _).trans hz.1)
    have hh := hf.2 (ℕ × ℕ) (goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k)
      (fun v => v.1*v.2) (goldbachG11RectangleWeight N)
      (fun v _ => goldbachG11RectangleWeight_nonneg N v) ha
    rw [sum_product] at hh
    have hmass : (∑ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
        goldbachG11RectangleWeight N v) ≤ goldbachG11GridPlainMass N ε ρ k :=
      sum_le_sum (fun v _ => goldbachG11RectangleWeight_le_allPrime N v)
    have hnF : 0 ≤ fouvryG9UpperFactor N (goldbachG11GridLowLevel N δ ρ k) C K θ*
        fouvryG9BaseEuler N (Real.sqrt N)*goldbachG11EulerCorrection N := mul_nonneg (mul_nonneg hf.1 hbase) hcorr
    have hout := hh.trans (mul_le_mul_of_nonneg_left hmass hnF)
    simpa only [F,goldbachG11MixedLevel,if_pos hkc] using hout
  have hTboundary : 1 ≤ (N : ℝ)^(1/10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  obtain ⟨_,_,hQ,_,hQN⟩ := hw N ((N : ℝ)^(1/10 : ℝ)) hNM hTboundary (le_refl _)
  have hzQ := (g9WF_sqrt_cutoff hn4R hTboundary (le_refl _) hδ hδu).2
  rw [goldbachG11OrdinaryLevel_eq_low_at_boundary hn δ] at hQ hQN hzQ
  have hf := hfinite N hn4 hEven hbig (goldbachG11OrdinaryLevel N δ) hQ hQN hzQ
  have hhi : ∀ k ∈ goldbachG11HighGridUsed N ε ρ,
      (∑ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
        goldbachG11AllPrimeWeight N v*externalDensity true P
          (externalInternalLevel (goldbachG11OrdinaryLevel N δ) θ) θ (Real.sqrt N)
          (progressionDensity v.1)) ≤ F k*goldbachG11GridPlainMass N ε ρ k := by
    intro k hk
    have ha : ∀ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
        goldbachG11AllPrimeWeight N v ≠ 0 → 0 < v.1 ∧
        (∀ p ∈ v.1.primeFactors,(N : ℝ)^(4/53 : ℝ) ≤ (p : ℝ)) ∧ v.1.primeFactors.card ≤ 21 := by
      intro v hv _
      have hm := (mem_filter.mp (mem_product.mp hv).1).1
      obtain ⟨hr,_heq,hcard⟩ := goldbachG11EffectiveProductSupport_primeFactors hm
      exact ⟨(goldbachG11ProductSupport_data (mem_filter.mp hm).1).1,hr,hcard.trans (by norm_num)⟩
    have hh := hf.2 (ℕ × ℕ) (goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k)
      Prod.fst (goldbachG11AllPrimeWeight N) (fun v _ => goldbachG11AllPrimeWeight_nonneg N v) ha
    simpa only [F,P,goldbachG11GridPlainMass,goldbachG11MixedLevel,if_neg (mem_filter.mp hk).2] using hh
  unfold goldbachG11MixedDensityMain goldbachG11GridAnalyticMain
  rw [goldbachG11OrdinaryDensityMain_eq_pairs hρ hρu hbig (goldbachG11HighGridUsed N ε ρ)
    (filter_subset _ _) (fun _ => fouvryG9SievePrimes N (Real.sqrt N)) (fun _ => Real.sqrt N)]
  rw [← goldbachG11Grid_low_high_sum]
  exact add_le_add (sum_le_sum hlo) (sum_le_sum hhi)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig