import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDivisorDistribution

open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve AnalyticNumberTheory.Sieve

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal prime-window cardinality, obtained from the actual AP count at modulus one. -/
theorem goldbachG11LinkedPrimeWindow_card_eq_primeCount {N m : ℕ} {ε : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ) =
      PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
        PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊ := by
  have hp (t : ℕ) : (primesInAP t 1 0 : ℝ) = PanPrincipal.primeCount t := by
    simp [primesInAP, PanPrincipal.primeCount, Nat.ModEq, Nat.mod_one, Finset.sum_boole]
  have hap : goldbachG11LinkedAPWindow N ε m 1 0 =
      goldbachG11LinkedPrimeWindow N ε m := by
    ext r
    simp [goldbachG11LinkedAPWindow, Nat.ModEq, Nat.mod_one]
  have h := goldbachG11LinkedAPWindow_card_eq_inverse 1 0 hN hm (Nat.coprime_one_right m)
  simpa only [Nat.mod_one, hap, hp] using h

theorem goldbachG11PrimeWindowMainMass_eq_gated_add (N d : ℕ) (ε : ℝ) :
    goldbachG11PrimeWindowMainMass N ε =
      (∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => m.Coprime d),
        goldbachG11PrimeWindowWeight N ε m) +
      ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => ¬m.Coprime d),
        goldbachG11PrimeWindowWeight N ε m := by
  rw [goldbachG11PrimeWindowMainMass, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  by_cases h : m.Coprime d <;> simp [h]

/-- Actual output-divisor count minus one main mass independent of the modulus. -/
def goldbachG11CommonDivisorResidual (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG11EffectiveProductSupport N ε,
    goldbachG11EffectiveProductCoefficient N ε m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
    goldbachG11PrimeWindowMainMass N ε / (d.totient : ℝ)

/-- Removing the coprime gate increases the main term, hence the minus sign. -/
theorem goldbachG11CommonDivisorResidual_eq {N : ℕ}
    (hN : 2 ≤ N) (ε : ℝ) (d : ℕ) :
    goldbachG11CommonDivisorResidual N ε d =
      goldbachG11LinkedDivisorResidual N ε d - goldbachG11PrimeWindowGateLoss N ε d := by
  have hmass :
      (∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => m.Coprime d),
        goldbachG11EffectiveProductCoefficient N ε m *
          (PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
            PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊)) =
      ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => m.Coprime d),
        goldbachG11PrimeWindowWeight N ε m := by
    apply sum_congr rfl
    intro m hm
    rw [goldbachG11PrimeWindowWeight,
      goldbachG11LinkedPrimeWindow_card_eq_primeCount hN (mem_filter.mp hm).1]
  unfold goldbachG11CommonDivisorResidual goldbachG11LinkedDivisorResidual
    goldbachG11PrimeWindowGateLoss
  rw [hmass, goldbachG11PrimeWindowMainMass_eq_gated_add N d ε]
  ring

theorem goldbachG11CommonDivisorResidual_sum_le {N Q : ℕ}
    (hN : 2 ≤ N) (ε : ℝ) :
    (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11CommonDivisorResidual N ε d|) ≤
      (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11LinkedDivisorResidual N ε d|) +
      ∑ d ∈ Icc 1 Q, goldbachG11PrimeWindowGateLoss N ε d := by
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q,
        (|goldbachG11LinkedDivisorResidual N ε d| + goldbachG11PrimeWindowGateLoss N ε d) := by
      apply sum_le_sum
      intro d _
      rw [goldbachG11CommonDivisorResidual_eq hN]
      simpa only [abs_of_nonneg (goldbachG11PrimeWindowGateLoss_nonneg N d ε)] using
        (abs_sub (goldbachG11LinkedDivisorResidual N ε d) (goldbachG11PrimeWindowGateLoss N ε d))
    _ = (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11LinkedDivisorResidual N ε d|) +
        ∑ d ∈ goldbachG11LinkedModuli N Q, goldbachG11PrimeWindowGateLoss N ε d :=
      sum_add_distrib
    _ ≤ _ := add_le_add le_rfl
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun d _ _ => goldbachG11PrimeWindowGateLoss_nonneg N d ε))

theorem goldbachG11LinkedLevel_le {N Q : ℕ} {B : ℝ}
    (hN : 2 ≤ N) (hB : 0 < B) (hl : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B) : Q ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N : ℝ)]
  have hr : (Q : ℝ) ≤ N :=
    hQ.trans ((div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hl hB.le)).trans hs)
  exact_mod_cast hr

/-- Unconditional common-main-mass distribution on the existing squarefree,
coprime-to-N modulus carrier; all thresholds precede epsilon and Q. -/
theorem goldbachG11CommonDivisorResidual_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11CommonDivisorResidual N ε d|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, M, hM4, hdist⟩ :=
    goldbachG11LinkedDivisorResidual_log_saving A hA
  obtain ⟨K, _, hgate⟩ := goldbachG11PrimeWindowGateLoss_log_saving A
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
    _ ≤ (∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11LinkedDivisorResidual N ε d|) +
        ∑ d ∈ Icc 1 Q, goldbachG11PrimeWindowGateLoss N ε d :=
      goldbachG11CommonDivisorResidual_sum_le hN2 ε
    _ ≤ C * N / Real.log (N : ℝ) ^ A + N / Real.log (N : ℝ) ^ A :=
      add_le_add (hdist N hNM ε Q hQ) (hgate N hNK ε Q hQN)
    _ = (C + 1) * N / Real.log (N : ℝ) ^ A := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig