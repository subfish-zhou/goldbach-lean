import MathlibNt.SieveTheory.LiLiuGoldbachG11GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP

open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG12ActiveProductSupport_primeFactors {N m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (∀ p ∈ m.primeFactors, (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ)) ∧
      m.primeFactors = largePrimeDivisors m ((N : ℝ) ^ (4 / 53 : ℝ)) ∧
      m.primeFactors.card ≤ 20 := by
  obtain ⟨hm0, hmN, _, _, _, hz, _⟩ := goldbachG12ActiveProductSupport_data hm
  have hf : ∀ p ∈ m.primeFactors, (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpp, hpm, _⟩ := Nat.mem_primeFactors.mp hp
    exact hz.trans (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le hpm)
  have heq : m.primeFactors = largePrimeDivisors m ((N : ℝ) ^ (4 / 53 : ℝ)) := by
    symm
    exact filter_eq_self.mpr hf
  refine ⟨hf, heq, ?_⟩
  rw [heq]
  exact largePrimeDivisors_card_le_twenty hm0 hmN
    (by norm_num : (1 : ℝ) / 21 < 4 / 53)

def goldbachG12PrimeWindowWeight (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  goldbachG12NormalizedCoefficient N m *
    (goldbachG11LinkedPrimeWindow N ε m).card

def goldbachG12PrimeWindowMainMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12PrimeWindowWeight N ε m

def goldbachG12PrimeWindowGateLoss (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => ¬m.Coprime d),
    goldbachG12PrimeWindowWeight N ε m) / (d.totient : ℝ)

theorem goldbachG12PrimeWindowWeight_nonneg (N m : ℕ) (ε : ℝ) :
    0 ≤ goldbachG12PrimeWindowWeight N ε m :=
  mul_nonneg (goldbachG12NormalizedCoefficient_bounds N m).1 (Nat.cast_nonneg _)

theorem goldbachG12PrimeWindowMainMass_nonneg (N : ℕ) (ε : ℝ) :
    0 ≤ goldbachG12PrimeWindowMainMass N ε :=
  sum_nonneg (fun m _ => goldbachG12PrimeWindowWeight_nonneg N m ε)

theorem goldbachG12PrimeWindowGateLoss_nonneg (N d : ℕ) (ε : ℝ) :
    0 ≤ goldbachG12PrimeWindowGateLoss N ε d :=
  div_nonneg (sum_nonneg (fun m _ => goldbachG12PrimeWindowWeight_nonneg N m ε))
    (Nat.cast_nonneg _)

theorem goldbachG12LinkedPrimeWindow_card_le {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ) ≤ (N : ℝ) / m := by
  have hm0 := (goldbachG12ActiveProductSupport_data hm).1
  have hsub : goldbachG11LinkedPrimeWindow N ε m ⊆ Icc 1 (N / m) := by
    intro r hr
    exact mem_Icc.mpr ⟨(mem_filter.mp hr).2.1.one_le,
      (Nat.le_div_iff_mul_le hm0).mpr (goldbachG12LinkedPrimeWindow_product_le hm hr)⟩
  have hc : (goldbachG11LinkedPrimeWindow N ε m).card ≤ N / m := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  calc
    _ ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ (N : ℝ) / m := by
      apply (le_div_iff₀ hmR).mpr
      exact_mod_cast Nat.div_mul_le_self N m

theorem goldbachG12PrimeWindowWeight_le {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    |goldbachG12PrimeWindowWeight N ε m| ≤ (N : ℝ) / m := by
  rw [abs_of_nonneg (goldbachG12PrimeWindowWeight_nonneg N m ε)]
  exact (mul_le_of_le_one_left (Nat.cast_nonneg _)
    (goldbachG12NormalizedCoefficient_bounds N m).2).trans
      (goldbachG12LinkedPrimeWindow_card_le hm)

theorem goldbachG12PrimeWindowGateLoss_sum_le {N Q : ℕ} (ε : ℝ)
    (hN : 2 ≤ N) (hQ : Q ≤ N) :
    (∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d) ≤
      (40 * N / (N : ℝ) ^ (4 / 53 : ℝ)) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hS : goldbachG12ActiveProductSupport N ⊆ Icc 1 N := by
    intro m hm
    have hd := goldbachG12ActiveProductSupport_data hm
    exact mem_Icc.mpr ⟨hd.1, hd.2.1.le⟩
  have h := G11FiniteGate.sum_gate_le_logCube (K := 20)
    (w := goldbachG12PrimeWindowWeight N ε) hN hQ
    (show 0 < (N : ℝ) ^ (4 / 53 : ℝ) from
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _)
    (Nat.cast_nonneg N) hS
    (fun m hm => (goldbachG12ActiveProductSupport_primeFactors hm).1)
    (fun m hm => (goldbachG12ActiveProductSupport_primeFactors hm).2.2)
    (fun m hm => goldbachG12PrimeWindowWeight_le hm)
  change (∑ d ∈ Icc 1 Q, |goldbachG12PrimeWindowGateLoss N ε d|) ≤ _ at h
  simpa only [abs_of_nonneg (goldbachG12PrimeWindowGateLoss_nonneg N _ ε),
    show (2 : ℝ) * (20 : ℕ) = 40 by norm_num] using h

/-- The threshold is chosen before both the window parameter and the modulus cutoff. -/
theorem goldbachG12PrimeWindowGateLoss_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ), Q ≤ N →
      (∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d) ≤
        N / Real.log (N : ℝ) ^ U := by
  have hgrowth : ∀ᶠ N : ℕ in atTop, (320 : ℝ) ≤ (N : ℝ) ^ (2 / 53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlogevent : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hevent : ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 1 ≤ Real.log (N : ℝ) ∧
      (320 : ℝ) ≤ (N : ℝ) ^ (2 / 53 : ℝ) ∧
      Real.log (N : ℝ) ^ (U + 3) ≤ (N : ℝ) ^ (2 / 53 : ℝ) := by
    filter_upwards [eventually_ge_atTop 4, hlogevent, hgrowth,
      PanPrincipal.eventually_log_rpow_le_rpow (U + 3) (2 / 53) (by norm_num)]
      with N hN hl hc hp
    exact ⟨hN, hl, hc, hp⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN ε Q hQ
  obtain ⟨hN4, hl1, hc, hp⟩ := hM N ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hz := Real.rpow_pos_of_pos hNpos (4 / 53 : ℝ)
  have hbudget : 320 * Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ U ≤
      (N : ℝ) ^ (4 / 53 : ℝ) := by
    calc
      _ = 320 * Real.log (N : ℝ) ^ (U + 3) := by
        rw [Real.rpow_add hl, Real.rpow_ofNat]
        ring
      _ ≤ (N : ℝ) ^ (2 / 53 : ℝ) * (N : ℝ) ^ (2 / 53 : ℝ) :=
        mul_le_mul hc hp (Real.rpow_nonneg hl.le _) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (4 / 53 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
  have hcube : (1 + Real.log (N : ℝ)) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * Real.log (N : ℝ)) ^ 3 := by gcongr; linarith
      _ = _ := by ring
  calc
    _ ≤ (40 * N / (N : ℝ) ^ (4 / 53 : ℝ)) *
        (1 + Real.log (N : ℝ)) ^ 3 :=
      goldbachG12PrimeWindowGateLoss_sum_le ε (by omega) hQ
    _ ≤ (40 * N / (N : ℝ) ^ (4 / 53 : ℝ)) *
        (8 * Real.log (N : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ ≤ N / Real.log (N : ℝ) ^ U := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hl U)).mpr
      calc
        _ = (N : ℝ) * (320 * Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ U) /
            (N : ℝ) ^ (4 / 53 : ℝ) := by ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (4 / 53 : ℝ) / (N : ℝ) ^ (4 / 53 : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hNpos.le) hz.le
        _ = N := mul_div_cancel_right₀ _ (ne_of_gt hz)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig