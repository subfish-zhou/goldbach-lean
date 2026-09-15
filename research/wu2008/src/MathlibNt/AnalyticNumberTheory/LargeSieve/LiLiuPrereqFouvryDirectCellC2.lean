import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayZero
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPayMainUniform
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryUniform
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalPayment

/-! The actual retained coprime cell, with all three energies and their
normalizations produced internally. No cancellation/envelope hypothesis. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_retained_cell_c2 (k m : ℕ) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1) (hηε : η < ε)
    (hbudget : 400*η ≤ ε/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M ν : ℝ),
      4 ≤ x → 1 ≤ M → ε ≤ ν → ν ≤ 1/10 → x = 4*M*x^ν →
      ∀ (N : Finset ℕ), (∀ n ∈ N, x^ν ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*x^ν) →
      ∀ (a : ℤ), a ≠ 0 → |(a : ℝ)| ≤ x →
      ∀ (K : WExtractedKey), K ∈ wExtractedKeyBox (x^η) →
      ∀ (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool) (c : Finset (ℕ × ℕ))
        (β γ ζ : ℕ → ℝ),
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ n, |γ n| ≤ (fouvryTau m n : ℝ)) →
      (∀ n, |ζ n| ≤ (fouvryTau m n : ℝ)) →
      (wAnalyticDyadicBlock (wExtractedKeyFiber (wFloorCutoff M (x^η)) N
        (Ioc 0 ⌊(x^c2RExponent ν ε)*(x^c2SExponent ν ε)⌋₊) a (c2FiveSmallMask x η)
        (x^c2RExponent ν ε) (x^c2SExponent ν ε) (highOmegaCutoff x) b K) j positive).Nonempty →
      wBlockAmplitude K j *
        ‖∑ t ∈ wCoprimeFiber x N (x^c2SExponent ν ε)
          (wGramPrefix N a x η (x^c2RExponent ν ε) (x^c2SExponent ν ε)
            M (x^η) K b j cap positive) c,
          (wExtractedCoefficient (betaClean β a)
            (factorConvolution γ (betaLowOmega ζ (highOmegaCutoff x))) γ ζ t.1 : ℂ) *
            wExtractedArithmeticPhase a t.2 t.1‖ ≤ C*(x^ν)^2*x^(-(ε/2)) := by
  obtain ⟨Cz,Cn,Cs,Ct,Cj,Ca,Cc,Co,hz,hn,hs,ht,hj,ha,hc,ho,hprod⟩ :=
    direct_retained_prefix_three_terms k m hη hη hη hη
  obtain ⟨Bz,hBz,hzero⟩ := directPayZero_uniform η η η Cz Cc Co
    hη.le hη.le hη.le hη1 hz.le hc.le ho.le
  obtain ⟨Bm,hBm,hmain⟩ := directPayMain_uniform η η η η Cn Ct Cj Ca Cc Co
    hη.le hη hη.le hη.le hη1 hn.le ht.le hj.le ha.le ho.le
  obtain ⟨Bs,hBs,hsec⟩ := directJoinedSecondary_uniform
    (κ := η) (δ := η) (ρ := η) (η := η) (Cnonzero := Cn)
    (Csecondary := Cs) (Ccoeff := Cc) (Couter := Co)
    hη.le hη hη.le hη.le hη1 hn.le hs.le ho.le
  refine ⟨Bz+Bs+Bm, by positivity, ?_⟩
  intro x M ν hx hM hεν hν hMT N hN a ha0 hax K hK b j cap positive c β γ ζ hβ hγ hζ hne
  obtain ⟨t,htmem⟩ := hne
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < x^ν := Real.rpow_pos_of_pos hx0 ν
  have hT1 : 1 ≤ x^ν := Real.one_le_rpow hx1 (by linarith)
  have hNT : ∀ n ∈ N, (n : ℝ) ≤ 2*x^ν := fun n hn => (hN n hn).2
  have hNp : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact_mod_cast hT0.trans_le (hN n hn).1
  have hNX : ∀ n ∈ N, (n : ℝ) ≤ x := by
    intro n hn
    have hh := (hN n hn).2
    nlinarith
  have hF : (⌊2*x^ν⌋₊ : ℝ) ≤ 2*x^ν := Nat.floor_le (by positivity)
  have hNF : ∀ n ∈ N, n ≤ ⌊2*x^ν⌋₊ := fun n hn => Nat.le_floor (hNT n hn)
  obtain ⟨hR,hS,hRS,_⟩ := c2_factor_levels hx1 hε.le hεν hν
  have hRSx : (x^c2RExponent ν ε)*(x^c2SExponent ν ε) ≤ x := by
    rw [hRS]
    calc
      _ ≤ x^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = _ := Real.rpow_one x
  have hRx : x^c2RExponent ν ε ≤ x :=
    (le_mul_of_one_le_right (by positivity) hS).trans hRSx
  have hSx : x^c2SExponent ν ε ≤ x :=
    (le_mul_of_one_le_left (by positivity) hR).trans hRSx
  have hp := hprod x hx1 N ⌊2*x^ν⌋₊ a x η (x^c2RExponent ν ε) (x^c2SExponent ν ε)
    M (x^η) (x^ν) ε K b j cap positive c β γ ζ ha0 (by positivity) (by positivity)
    hRx hSx hRSx (by linarith) (by positivity) (fun n hn => (hN n hn).1) hNT hNF hNX
    (by linarith) hηε (Real.rpow_le_rpow_of_exponent_le hx1 hεν) hβ hγ hζ
  have hzpay := hzero x M (x^ν) (x^c2RExponent ν ε) (x^c2SExponent ν ε)
    hx hM hT1 hMT hR hS hRSx N a b K ⌊2*x^ν⌋₊ j positive t hNp hNT hF hK htmem
  have hmpay := hmain x M (x^ν) (x^c2RExponent ν ε) (x^c2SExponent ν ε)
    hx hM hT1 hMT hR hS hRSx N hNp hNT a hax ⌊2*x^ν⌋₊ hF b K hK j cap positive t htmem
  have hspay := hsec x M (x^ν) (x^c2RExponent ν ε) (x^c2SExponent ν ε)
    hx hM hT1 hMT hR hS hRSx N hNp hNT a hax ⌊2*x^ν⌋₊ hF K hK j cap positive b t htmem
  have hzmono := c2_direct_zero_monomial hx1 hε.le hεν hν
    (show 100*(η+η+η) ≤ ε/4 by linarith)
  have hmmono := c2_direct_main_monomial hx1 hε.le hεν hν
    (show 100*(η+η+η+η) ≤ ε/4 by linarith)
  have hsmono := c2_direct_secondary_monomial hx1 hε.le hεν hν
    (show 100*(η+η+η+η) ≤ ε/4 by linarith)
  have hzfin := hzpay.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hzmono hBz.le)
  have hmfin := hmpay.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmmono hBm.le)
  have hsfin := hspay.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsmono hBs.le)
  have hzfin' := (div_le_iff₀ (sq_pos_of_pos hT0)).mp hzfin
  have hmfin' := (div_le_iff₀ (sq_pos_of_pos hT0)).mp hmfin
  have hsfin' := (div_le_iff₀ (sq_pos_of_pos hT0)).mp hsfin
  dsimp only at hp
  change _ ≤ wBlockAmplitude K j * Real.sqrt (directJoinedMass η Co x (x^ν) j) *
    (Real.sqrt (directJoinedZero η η Cz Cc x K ⌊2*x^ν⌋₊ j) +
     Real.sqrt (directJoinedSecondary η η η Cn Cs Cc x a (x^c2RExponent ν ε)
       (x^c2SExponent ν ε) K ⌊2*x^ν⌋₊ j cap) +
     Real.sqrt (directJoinedMain η η η Cn Ct Cj Ca Cc x a (x^c2RExponent ν ε)
       (x^c2SExponent ν ε) K ⌊2*x^ν⌋₊ j cap)) at hp
  apply hp.trans
  rw [mul_add, mul_add]
  nlinarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
