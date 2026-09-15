import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectCellC2
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPrefixAssembly

noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- All actual rectangular prefixes, coprimality cells, signs and dyadic blocks.
Only the explicit dyadic cardinality remains for the analytic cost producer. -/
theorem direct_key_c2 (k m : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) (hηε : η < ε)
    (hbudget : 400*η ≤ ε/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ M ν : ℝ,
      1 ≤ M → ε ≤ ν → ν ≤ 1/10 → x = 4*M*x^ν →
      ∀ (N : Finset ℕ), (∀ n ∈ N, x^ν ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*x^ν) →
      ∀ (a : ℤ), a ≠ 0 → |(a : ℝ)| ≤ x →
      ∀ (K : WExtractedKey), K ∈ wExtractedKeyBox (x^η) →
      ∀ (b : ℕ) (β γ ζ : ℕ → ℝ),
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) →
      let U := wExtractedKeyFiber (wFloorCutoff M (x^η)) N
        (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) a (c2FiveSmallMask x η)
        (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K
      wAnalyticKeyPrefixMajorant U K (betaClean β a)
        (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a ≤
      C*(x^ν)^2*x^(η-ε/2)*((U.image wAnalyticDyadicKey).card : ℝ) := by
  obtain ⟨C,hC,hcell⟩ := direct_retained_cell_c2 k m hε hη hη1 hηε hbudget
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [eventually_wCoprimeLabel_image_card_le hη,
    eventually_ge_atTop (4 : ℝ)] with x hpartition hx
  intro M ν hM hεν hν hMT N hN a ha hax K hK b β γ ζ hβ hγ hζ
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hT0 : 0 < x^ν := Real.rpow_pos_of_pos hx0 ν
  have hNp : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact_mod_cast hT0.trans_le (hN n hn).1
  have hNT : ∀ n ∈ N, (n : ℝ) ≤ 2*x^ν := fun n hn => (hN n hn).2
  have hRS := (c2_factor_levels hx1 hε.le hεν hν).2.2.1
  let U := wExtractedKeyFiber (wFloorCutoff M (x^η)) N
    (Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊) a (c2FiveSmallMask x η)
    (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K
  have hQ : ∀ q ∈ Ioc 0 ⌊x^((5-5*ν)/9-ε)⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hpair := wCoprimePairBound_c2_le hx hε.le hεν hν hNT
  have hblock (j : Fin 5 → ℕ) (positive : Bool) :
      wBlockAmplitude K j * wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive)
        j (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a ≤
      x^η*(C*(x^ν)^2*x^(-(ε/2))) := by
    apply direct_block_prefix_assembly x (x^c2SExponent ν ε) N U K j positive
      (betaClean β a) (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
      (C*(x^ν)^2*x^(-(ε/2))) (x^η)
    · exact hpartition (wFloorCutoff M (x^η)) N _ a η _ _ b K
        (wAnalyticDyadicBlock U j positive) hNp hQ hpair (fun t ht => (mem_filter.mp ht).1)
    · positivity
    · intro c hc cap _hcap
      obtain ⟨t,ht,_⟩ := mem_image.mp hc
      have hne : (wAnalyticDyadicBlock (wExtractedKeyFiber (wFloorCutoff M (x^η)) N
          (Ioc 0 ⌊(x^c2RExponent ν ε)*(x^c2SExponent ν ε)⌋₊) a (c2FiveSmallMask x η)
          (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K) j positive).Nonempty := by
        simpa only [hRS] using (show (wAnalyticDyadicBlock U j positive).Nonempty from ⟨t,ht⟩)
      have hp := hcell x M ν hx hM hεν hν hMT N hN a ha hax K hK
        b j cap positive c β γ ζ hβ hγ hζ hne
      unfold wAnalyticPrefixSum
      rw [direct_prefix_coprime_commute]
      simpa only [wGramPrefix, hRS] using hp
  have hkey := direct_key_prefix_assembly U K (betaClean β a)
    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
    (x^η*(C*(x^ν)^2*x^(-(ε/2)))) ((U.image wAnalyticDyadicKey).card : ℝ)
    (by positivity) le_rfl (fun j _ positive => hblock j positive)
  apply hkey.trans_eq
  rw [Real.rpow_sub hx0]
  rw [Real.rpow_neg hx0.le]
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
