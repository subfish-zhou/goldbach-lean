import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectKeyC2
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectErrorScalar

noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The full actual retained contribution, including alpha, shell count, keys,
variation, coprime partition and five dyadic coordinates. -/
theorem direct_total_prefix_cost_c2 (i k m : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) (hηε : η < ε)
    (hbudget : 416*η ≤ ε/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ M ν : ℝ,
      1 ≤ M → ε ≤ ν → ν ≤ 1/10 → x = 4*M*x^ν →
      ∀ (N : Finset ℕ), (∀ n ∈ N, x^ν ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*x^ν) →
      ∀ (U : Finset ℕ) (α : ℕ → ℝ),
      (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      ∀ (a : ℤ), a ≠ 0 → |(a : ℝ)| ≤ x →
      ∀ (K : WExtractedKey), K ∈ wExtractedKeyBox (x^η) →
      ∀ (b : ℕ) (β γ ζ : ℕ → ℝ),
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) →
      let L := x^((5-5*ν)/9-ε)
      let V := wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊) a
        (c2FiveSmallMask x η) (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K
      3072*M*(∑ n ∈ U, α n^2)*(Nat.log 2 ⌈L^2/M*x^η⌉₊ + 1 : ℕ)*(x^η)^7*
        wAnalyticVariationConstant (x^η)*
        wAnalyticKeyPrefixMajorant V K (betaClean β a)
          (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a ≤
      C*x^2*x^(-(ε/4)) := by
  obtain ⟨Ck,hCk,hkey⟩ := direct_key_c2 k m hε hη hη1 hηε (by linarith)
  obtain ⟨Ca,hCa,halpha⟩ := direct_alpha_mass_subpower i hη
  obtain ⟨Cv,hCv,hcost⟩ := direct_analytic_prefactor_subpower hη.le hη1 hη
  refine ⟨192*Ca*Cv*Ck, by positivity, ?_⟩
  filter_upwards [hkey, eventually_ge_atTop (4 : ℝ)] with x hkx hx
  intro M ν hM hεν hν hMT N hN U α hU hα a ha hax K hK b β γ ζ hβ hγ hζ
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < x^ν := Real.rpow_pos_of_pos hx0 ν
  have hT1 : 1 ≤ x^ν := Real.one_le_rpow hx1 (by linarith)
  have hNp : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact_mod_cast hT0.trans_le (hN n hn).1
  have hNX : ∀ n ∈ N, (n : ℝ) ≤ x := by
    intro n hn
    have hh := (hN n hn).2
    nlinarith
  have hMx : 2*M ≤ x := by nlinarith
  let L := x^((5-5*ν)/9-ε)
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLx : L ≤ x := by
    calc
      _ ≤ x^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = _ := Real.rpow_one x
  let V := wExtractedKeyFiber (wFloorCutoff M (x^η)) N (Ioc 0 ⌊L⌋₊) a
    (c2FiveSmallMask x η) (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K
  let d : ℝ := (V.image wAnalyticDyadicKey).card
  let J : ℝ := (Nat.log 2 ⌈L^2/M*x^η⌉₊ + 1 : ℕ)
  let v := wAnalyticVariationConstant (x^η)
  let p := wAnalyticKeyPrefixMajorant V K (betaClean β a)
    (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ a
  have hp : p ≤ Ck*(x^ν)^2*x^(η-ε/2)*d :=
    hkx M ν hM hεν hν hMT N hN a ha hax K hK b β γ ζ hβ hγ hζ
  have hc : J*(x^η)^7*v*d ≤ Cv*x^(12*η+η) :=
    hcost x L M (by linarith) hL0 hLx hM N hNp hNX a (c2FiveSmallMask x η)
      (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K
  have hαb := halpha x M hx1 hM hMx U α hU hα
  have hv0 : 0 ≤ v := wAnalyticVariationConstant_nonneg (by positivity)
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hp0 : 0 ≤ p := wAnalyticKeyPrefixMajorant_nonneg _ _ _ _ _ _ _
  change 3072*M*(∑ n ∈ U, α n^2)*J*(x^η)^7*v*p ≤ _
  calc
    _ ≤ 3072*M*(Ca*M*x^η)*J*(x^η)^7*v*(Ck*(x^ν)^2*x^(η-ε/2)*d) := by gcongr
    _ = 3072*M*(Ca*M*x^η)*(J*(x^η)^7*v*d)*(Ck*(x^ν)^2*x^(η-ε/2)) := by ring
    _ ≤ 3072*M*(Ca*M*x^η)*(Cv*x^(12*η+η))*(Ck*(x^ν)^2*x^(η-ε/2)) := by gcongr
    _ = (192*Ca*Cv*Ck)*x^2*x^(15*η-ε/2) := by
      have hpow : x^η*x^(12*η+η)*x^(η-ε/2) = x^(15*η-ε/2) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1
        ring
      calc
        _ = (192*Ca*Cv*Ck)*(4*M*x^ν)^2*(x^η*x^(12*η+η)*x^(η-ε/2)) := by ring
        _ = _ := by rw [← hMT, hpow]
    _ ≤ _ := by
      gcongr
      linarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
