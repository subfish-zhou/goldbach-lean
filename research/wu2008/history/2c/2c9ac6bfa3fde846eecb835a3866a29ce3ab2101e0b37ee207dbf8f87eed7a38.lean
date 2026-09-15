import MathlibNt.Wu2004MeanValue.RosserConsumerPairs
import MathlibNt.Wu2004MeanValue.SieveAsymptoticsProduct
import MathlibNt.Wu2004MeanValue.SieveErrorPayment
import MathlibNt.Wu2004MeanValue.SieveMainPayment

/-!
# Actual switched-pair upper-sieve bounds

Source: the frozen manuscript's tail sieve calculation and block-bound.
The counts retain prime-pair multiplicities. The Rosser level is `Q/2`,
not `Q`, and its actual ratio tends to two. These are not bounds for the
original bad-prime count: no switching or dyadic-union bridge is asserted.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
open MathlibNt.SieveTheory.SwitchingPrinciple
open scoped BigOperators

private theorem eventually_sieve_geometry (B z₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      4 ≤ sieveAsymptoticQ B x ∧ z₀ ≤ sieveAsymptoticZ B x ∧
        3 / 2 ≤ sieveAsymptoticRatio B x ∧ sieveAsymptoticRatio B x ≤ 4 := by
  filter_upwards [(tendsto_sieveAsymptoticQ_atTop B).eventually
    (eventually_ge_atTop 4), (tendsto_sieveAsymptoticZ_atTop B).eventually
    (eventually_ge_atTop z₀), eventually_sieveAsymptoticRatio_mem B] with x hQ hz hs
  exact ⟨hQ, hz, hs.1, hs.2.trans (by norm_num)⟩

/-- The literal inclusive-tail switched multiset has the sharp source
coefficient `8 * integral + epsilon`. All constants precede the even integer. -/
theorem tailSiftedCount_sharp_upper (c τ η ε : ℝ) (hc : 0 < c)
    (hτ : 1 / 3 < τ) (hτh : τ < 1 / 2) (hη : 0 < η) (hη1 : η < 1)
    (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (tailSiftedCount N c τ η
        (Real.sqrt (Real.sqrt N / Real.log N ^ B)) : ℝ) ≤
      (8 * (∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε) *
        liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨δ, hδ, M, hM⟩ := tailMass_sieve_budget c τ η ε hc hτ hτh hη hη1 hε
  obtain ⟨B, hB, R, hR⟩ := tail_sequence_remainder_normalized c τ η δ hc hτ hη hη1 hδ
  obtain ⟨ρ, hρ, hproduct⟩ := exists_eventually_sieveDensityProduct_upperFactor δ hδ
  obtain ⟨z₀, _, hsieve⟩ := tailSiftedCount_upper_rosser ρ hρ
  have hgeometry := tendsto_natCast_atTop_atTop.eventually (eventually_sieve_geometry B z₀)
  have hprod := tendsto_natCast_atTop_atTop.eventually (hproduct B)
  have hdomain : ∀ᶠ N : ℕ in atTop, (2 / η) ^ 2 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨B, hB, eventually_atTop.mp ?_⟩
  filter_upwards [hgeometry, hprod, hdomain, eventually_ge_atTop M,
    eventually_ge_atTop R, eventually_ge_atTop (2 : ℕ)]
    with N hg hp hd hNM hNR hN2 hEven
  let Q := sieveAsymptoticQ B N
  have hQ : 4 ≤ Q := hg.1
  have hm := hM N hNM
  have hf := hsieve N c τ η Q hEven hη hη1.le hd hQ hg.2.1 hg.2.2.1 hg.2.2.2
  have he := hR N hNR Q (by linarith) le_rfl
  have hpN := mul_le_mul_of_nonneg_left (hp N hEven hN2) hm.1
  have hmain :
      tailMass N c τ η *
          (∏ p ∈ siftingPrimes N (Real.sqrt Q), (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log (Q / 2) / Real.log (Real.sqrt Q)) + ρ) ≤
        tailMass N c τ η * ((8 + δ) * liuSingularSeries N / Real.log N) := by
    simpa only [Q, sieveDensityProduct, sieveAsymptoticRatio, sieveAsymptoticZ,
      mul_assoc] using hpN
  exact hf.trans ((add_le_add hmain he).trans hm.2)

/-- Uniform actual open-block switched-pair count. The constants precede all
later `H,N,eta`; in particular no upper bound on `N/H` is imposed. -/
theorem blockSiftedCount_uniform_upper (a : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2) :
    ∃ B C H₀ : ℝ, 0 < B ∧ 0 < C ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ N : ℕ, Even N → 2 ≤ N → ∀ η : ℝ, η ≤ 1 →
      (blockSiftedCount H N a η
        (Real.sqrt (Real.sqrt (2 * H) / Real.log (2 * H) ^ B)) : ℝ) ≤
        C * liuSingularSeries N * H / Real.log H ^ 2 := by
  obtain ⟨C, hC, hM⟩ := blockMass_sieve_budget
  obtain ⟨B, hB, R, hR⟩ := block_sequence_remainder_normalized a 1 ha ha2 (by norm_num)
  obtain ⟨ρ, hρ, hproduct⟩ :=
    exists_eventually_sieveDensityProduct_upperFactor 1 (by norm_num)
  obtain ⟨z₀, _, hsieve⟩ := blockSiftedCount_upper_rosser ρ hρ
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_sieve_geometry B z₀).and (hproduct B))
  refine ⟨B, C, max 4 (max R T), hB, hC, ?_⟩
  intro H hH N hEven hN2 η hη
  have hH4 : 4 ≤ H := (le_max_left _ _).trans hH
  have hHR : R ≤ H := (le_max_left R T).trans ((le_max_right _ _).trans hH)
  have hHT : T ≤ H := (le_max_right R T).trans ((le_max_right _ _).trans hH)
  obtain ⟨hg, hp⟩ := hT (2 * H) (by linarith)
  let Q := sieveAsymptoticQ B (2 * H)
  have hQ : 4 ≤ Q := hg.1
  have hf := hsieve H N a η Q hEven hQ hg.2.1 hg.2.2.1 hg.2.2.2
  have he := hR H hHR N η hη Q (by linarith) le_rfl
  have hpN := mul_le_mul_of_nonneg_left (hp N hEven hN2) (blockMass_nonneg H N a η)
  have hmain :
      blockMass H N a η *
          (∏ p ∈ siftingPrimes N (Real.sqrt Q), (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log (Q / 2) / Real.log (Real.sqrt Q)) + ρ) ≤
        blockMass H N a η * (9 * liuSingularSeries N / Real.log (2 * H)) := by
    norm_num only at hpN
    simpa only [Q, sieveDensityProduct, sieveAsymptoticRatio, sieveAsymptoticZ,
      mul_assoc] using hpN
  have he' : (∑ d ∈ sieveDivisors N Q,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |blockRemainder H N a η d|) ≤
      liuSingularSeries N * H / Real.log H ^ 2 := by simpa only [one_mul] using he
  exact hf.trans ((add_le_add hmain he').trans (hM H hH4 N a η ha))

end Wu2004MeanValue
