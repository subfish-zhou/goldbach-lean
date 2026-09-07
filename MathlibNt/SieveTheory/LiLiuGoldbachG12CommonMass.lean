import MathlibNt.SieveTheory.LiLiuGoldbachG11CommonMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDivisorDistribution

open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve AnalyticNumberTheory.Sieve

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal prime-window cardinality, obtained from the actual AP count at modulus one. -/
theorem goldbachG12LinkedPrimeWindow_card_eq_primeCount {N m : ℕ} {ε : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N) :
    ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ) =
      PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
        PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊ := by
  have hp (t : ℕ) : (primesInAP t 1 0 : ℝ) = PanPrincipal.primeCount t := by
    simp [primesInAP, PanPrincipal.primeCount, Nat.ModEq, Nat.mod_one, Finset.sum_boole]
  have hap : goldbachG11LinkedAPWindow N ε m 1 0 =
      goldbachG11LinkedPrimeWindow N ε m := by
    ext r
    simp [goldbachG11LinkedAPWindow, Nat.ModEq, Nat.mod_one]
  have h := goldbachG12LinkedAPWindow_card_eq_inverse (ε := ε) 1 0 hN hm (Nat.coprime_one_right m)
  simpa only [Nat.mod_one, hap, hp] using h

theorem goldbachG12PrimeWindowMainMass_eq_gated_add (N d : ℕ) (ε : ℝ) :
    goldbachG12PrimeWindowMainMass N ε =
      (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
        goldbachG12PrimeWindowWeight N ε m) +
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => ¬m.Coprime d),
        goldbachG12PrimeWindowWeight N ε m := by
  rw [goldbachG12PrimeWindowMainMass, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  by_cases h : m.Coprime d <;> simp [h]

/-- Actual output-divisor count minus one main mass independent of the modulus. -/
def goldbachG12CommonDivisorResidual (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
    goldbachG12PrimeWindowMainMass N ε / (d.totient : ℝ)

/-- Removing the coprime gate increases the main term, hence the minus sign. -/
theorem goldbachG12CommonDivisorResidual_eq {N : ℕ}
    (hN : 2 ≤ N) (ε : ℝ) (d : ℕ) :
    goldbachG12CommonDivisorResidual N ε d =
      goldbachG12LinkedDivisorResidual N ε d - goldbachG12PrimeWindowGateLoss N ε d := by
  have hmass :
      (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
        goldbachG12NormalizedCoefficient N m *
          (PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
            PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊)) =
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
        goldbachG12PrimeWindowWeight N ε m := by
    apply sum_congr rfl
    intro m hm
    rw [goldbachG12PrimeWindowWeight,
      goldbachG12LinkedPrimeWindow_card_eq_primeCount hN (mem_filter.mp hm).1]
  unfold goldbachG12CommonDivisorResidual goldbachG12LinkedDivisorResidual
    goldbachG12PrimeWindowGateLoss
  rw [hmass, goldbachG12PrimeWindowMainMass_eq_gated_add N d ε]
  ring

theorem goldbachG12CommonDivisorResidual_sum_le {N Q : ℕ}
    (hN : 2 ≤ N) (ε : ℝ) :
    (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12CommonDivisorResidual N ε d|) ≤
      (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12LinkedDivisorResidual N ε d|) +
      ∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d := by
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q,
        (|goldbachG12LinkedDivisorResidual N ε d| + goldbachG12PrimeWindowGateLoss N ε d) := by
      apply sum_le_sum
      intro d _
      rw [goldbachG12CommonDivisorResidual_eq hN]
      simpa only [abs_of_nonneg (goldbachG12PrimeWindowGateLoss_nonneg N d ε)] using
        (abs_sub (goldbachG12LinkedDivisorResidual N ε d) (goldbachG12PrimeWindowGateLoss N ε d))
    _ = (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12LinkedDivisorResidual N ε d|) +
        ∑ d ∈ goldbachG11LinkedModuli N Q, goldbachG12PrimeWindowGateLoss N ε d :=
      sum_add_distrib
    _ ≤ _ := add_le_add le_rfl
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun d _ _ => goldbachG12PrimeWindowGateLoss_nonneg N d ε))

/-- Unconditional common-main-mass distribution on the existing squarefree,
coprime-to-N modulus carrier; all thresholds precede epsilon and Q. -/
theorem goldbachG12CommonDivisorResidual_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12CommonDivisorResidual N ε d|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, M, hM4, hdist⟩ :=
    goldbachG12LinkedDivisorResidual_log_saving A hA
  obtain ⟨K, _, hgate⟩ := goldbachG12PrimeWindowGateLoss_log_saving A
  have hlogevent : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  obtain ⟨L, hL⟩ := eventually_atTop.mp hlogevent
  refine ⟨B, C + 1, hB, by positivity, max M (max K L),
    hM4.trans (le_max_left _ _), ?_⟩
  intro N hN ε Q hQ
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNK : K ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNL : L ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := by omega
  have hQN := goldbachG11LinkedLevel_le hN2 hB (hL N hNL) hQ
  calc
    _ ≤ (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG12LinkedDivisorResidual N ε d|) +
        ∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d :=
      goldbachG12CommonDivisorResidual_sum_le hN2 ε
    _ ≤ C * N / Real.log (N : ℝ) ^ A + N / Real.log (N : ℝ) ^ A :=
      add_le_add (hdist N hNM ε Q hQ) (hgate N hNK ε Q hQN)
    _ = (C + 1) * N / Real.log (N : ℝ) ^ A := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig