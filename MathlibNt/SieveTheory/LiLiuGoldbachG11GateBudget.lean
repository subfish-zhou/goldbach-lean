import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindowAP
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve

noncomputable section

namespace G11FiniteGate

theorem inv_totient_prime_le {p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : 0 < z) (hzp : z ≤ (p : ℝ)) :
    (p.totient : ℝ)⁻¹ ≤ 2 / z := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  calc
    ((p : ℝ) - 1)⁻¹ ≤ ((p : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by positivity) (by linarith)
    _ = 2 / (p : ℝ) := by field_simp
    _ ≤ 2 / z := div_le_div_of_nonneg_left (by norm_num) hz hzp

/-- Union bound over all distinct prime factors, including those of a composite cofactor. -/
theorem bad_inverseTotientMass_le {N Q m K : ℕ} {z : ℝ}
    (hQ : Q ≤ N) (hm : 0 < m) (hz : 0 < z)
    (hf : ∀ p ∈ m.primeFactors, z ≤ (p : ℝ))
    (hK : m.primeFactors.card ≤ K) :
    (∑ d ∈ Icc 1 Q, if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) ≤
      (2 * K / z) * conductorHarmonicFactor N ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Icc 1 Q,
        ∑ p ∈ m.primeFactors, if p ∣ d then (d.totient : ℝ)⁻¹ else 0 := by
      apply sum_le_sum
      intro d _
      by_cases hbad : ¬m.Coprime d
      · obtain ⟨p, hp, hpm, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
        rw [if_pos hbad]
        have hmem := Nat.mem_primeFactors.mpr ⟨hp, hpm, ne_of_gt hm⟩
        simpa only [if_pos hpd] using
          (single_le_sum (f := fun q => if q ∣ d then (d.totient : ℝ)⁻¹ else 0)
            (fun q (_ : q ∈ m.primeFactors) => by
            split_ifs <;> positivity) hmem :
            (if p ∣ d then (d.totient : ℝ)⁻¹ else 0) ≤ _)
      · rw [if_neg hbad]
        exact sum_nonneg (fun p _ => by split_ifs <;> positivity)
    _ = ∑ p ∈ m.primeFactors, directConductorWeight Q p := by
      rw [sum_comm]
      simp only [directConductorWeight, sum_filter]
    _ ≤ ∑ p ∈ m.primeFactors, conductorHarmonicFactor Q ^ 2 / (p.totient : ℝ) :=
      sum_le_sum (fun p _ => directConductorWeight_le Q p)
    _ ≤ ∑ _p ∈ m.primeFactors, conductorHarmonicFactor Q ^ 2 * (2 / z) := by
      apply sum_le_sum
      intro p hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (inv_totient_prime_le (Nat.mem_primeFactors.mp hp).1 hz (hf p hp)) (sq_nonneg _)
    _ = (m.primeFactors.card : ℝ) * (conductorHarmonicFactor Q ^ 2 * (2 / z)) := by
      simp
    _ ≤ (K : ℝ) * (conductorHarmonicFactor Q ^ 2 * (2 / z)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hK)
      positivity
    _ = (2 * K / z) * conductorHarmonicFactor Q ^ 2 := by ring
    _ ≤ (2 * K / z) * conductorHarmonicFactor N ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sq_le_sq₀ (conductorHarmonicFactor_nonneg Q)
        (conductorHarmonicFactor_nonneg N)).mpr (conductorHarmonicFactor_mono hQ)

theorem weightMass_le {N : ℕ} {S : Finset ℕ} {T : ℝ} {w : ℕ → ℝ}
    (hS : S ⊆ Icc 1 N) (hT : 0 ≤ T)
    (hw : ∀ m ∈ S, |w m| ≤ T / (m : ℝ)) :
    ∑ m ∈ S, |w m| ≤ T * conductorHarmonicFactor N := by
  calc
    _ ≤ ∑ m ∈ S, T / (m : ℝ) := sum_le_sum hw
    _ = T * ∑ m ∈ S, (m : ℝ)⁻¹ := by simp [div_eq_mul_inv, mul_sum]
    _ ≤ T * conductorHarmonicFactor N := by
      apply mul_le_mul_of_nonneg_left _ hT
      exact sum_le_sum_of_subset_of_nonneg hS (fun m _ _ => by positivity)

/-- A finite main-term gate budget, not a termwise estimate on AP errors. -/
theorem sum_gate_le_logCube {N Q K : ℕ} {S : Finset ℕ} {z T : ℝ} {w : ℕ → ℝ}
    (hN : 2 ≤ N) (hQ : Q ≤ N) (hz : 0 < z) (hT : 0 ≤ T)
    (hS : S ⊆ Icc 1 N)
    (hf : ∀ m ∈ S, ∀ p ∈ m.primeFactors, z ≤ (p : ℝ))
    (hK : ∀ m ∈ S, m.primeFactors.card ≤ K)
    (hw : ∀ m ∈ S, |w m| ≤ T / (m : ℝ)) :
    (∑ d ∈ Icc 1 Q, |(∑ m ∈ S.filter (fun m => ¬m.Coprime d), w m) /
      (d.totient : ℝ)|) ≤ (2 * K * T / z) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
    linarith
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, ∑ m ∈ S,
        (if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) * |w m| := by
      apply sum_le_sum
      intro d _
      calc
        _ = |∑ m ∈ S.filter (fun m => ¬m.Coprime d), w m| * (d.totient : ℝ)⁻¹ := by
          rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d.totient : ℝ)⁻¹)]
        _ ≤ (∑ m ∈ S.filter (fun m => ¬m.Coprime d), |w m|) *
            (d.totient : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (by positivity)
        _ = _ := by
          rw [sum_mul, sum_filter]
          apply sum_congr rfl
          intro m _
          split_ifs <;> ring
    _ = ∑ m ∈ S,
        (∑ d ∈ Icc 1 Q, if ¬m.Coprime d then (d.totient : ℝ)⁻¹ else 0) * |w m| := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ m ∈ S, ((2 * K / z) * conductorHarmonicFactor N ^ 2) * |w m| := by
      apply sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right
        (bad_inverseTotientMass_le hQ (mem_Icc.mp (hS hm)).1 hz (hf m hm) (hK m hm))
        (abs_nonneg _)
    _ = ((2 * K / z) * conductorHarmonicFactor N ^ 2) * ∑ m ∈ S, |w m| :=
      (mul_sum _ _ _).symm
    _ ≤ ((2 * K / z) * conductorHarmonicFactor N ^ 2) *
        (T * conductorHarmonicFactor N) :=
      mul_le_mul_of_nonneg_left (weightMass_le hS hT hw) (by positivity)
    _ = (2 * K * T / z) * conductorHarmonicFactor N ^ 3 := by ring
    _ ≤ (2 * K * T / z) * (1 + Real.log (N : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (conductorHarmonicFactor_nonneg N)
        (conductorHarmonicFactor_le N) 3

end G11FiniteGate

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11EffectiveProductSupport_primeFactors {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    (∀ p ∈ m.primeFactors, (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ)) ∧
      m.primeFactors = largePrimeDivisors m ((N : ℝ) ^ (4 / 53 : ℝ)) ∧
      m.primeFactors.card ≤ 20 := by
  obtain ⟨hm0, hmN, _, hz⟩ := goldbachG11ProductSupport_data (mem_filter.mp hm).1
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

def goldbachG11PrimeWindowWeight (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  goldbachG11EffectiveProductCoefficient N ε m *
    (goldbachG11LinkedPrimeWindow N ε m).card

def goldbachG11PrimeWindowMainMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG11EffectiveProductSupport N ε, goldbachG11PrimeWindowWeight N ε m

def goldbachG11PrimeWindowGateLoss (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => ¬m.Coprime d),
    goldbachG11PrimeWindowWeight N ε m) / (d.totient : ℝ)

theorem goldbachG11PrimeWindowWeight_nonneg (N m : ℕ) (ε : ℝ) :
    0 ≤ goldbachG11PrimeWindowWeight N ε m :=
  mul_nonneg (goldbachG11EffectiveProductCoefficient_bounds N m ε).1 (Nat.cast_nonneg _)

theorem goldbachG11PrimeWindowMainMass_nonneg (N : ℕ) (ε : ℝ) :
    0 ≤ goldbachG11PrimeWindowMainMass N ε :=
  sum_nonneg (fun m _ => goldbachG11PrimeWindowWeight_nonneg N m ε)

theorem goldbachG11PrimeWindowGateLoss_nonneg (N d : ℕ) (ε : ℝ) :
    0 ≤ goldbachG11PrimeWindowGateLoss N ε d :=
  div_nonneg (sum_nonneg (fun m _ => goldbachG11PrimeWindowWeight_nonneg N m ε))
    (Nat.cast_nonneg _)

theorem goldbachG11LinkedPrimeWindow_card_le {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    ((goldbachG11LinkedPrimeWindow N ε m).card : ℝ) ≤ (N : ℝ) / m := by
  have hm0 := (goldbachG11ProductSupport_data (mem_filter.mp hm).1).1
  have hsub : goldbachG11LinkedPrimeWindow N ε m ⊆ Icc 1 (N / m) := by
    intro r hr
    exact mem_Icc.mpr ⟨(mem_filter.mp hr).2.1.one_le,
      (Nat.le_div_iff_mul_le hm0).mpr (goldbachG11LinkedPrimeWindow_product_le hm hr)⟩
  have hc : (goldbachG11LinkedPrimeWindow N ε m).card ≤ N / m := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  calc
    _ ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ (N : ℝ) / m := by
      apply (le_div_iff₀ hmR).mpr
      exact_mod_cast Nat.div_mul_le_self N m

theorem goldbachG11PrimeWindowWeight_le {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    |goldbachG11PrimeWindowWeight N ε m| ≤ (N : ℝ) / m := by
  rw [abs_of_nonneg (goldbachG11PrimeWindowWeight_nonneg N m ε)]
  exact (mul_le_of_le_one_left (Nat.cast_nonneg _)
    (goldbachG11EffectiveProductCoefficient_bounds N m ε).2).trans
      (goldbachG11LinkedPrimeWindow_card_le hm)

theorem goldbachG11PrimeWindowGateLoss_sum_le {N Q : ℕ} (ε : ℝ)
    (hN : 2 ≤ N) (hQ : Q ≤ N) :
    (∑ d ∈ Icc 1 Q, goldbachG11PrimeWindowGateLoss N ε d) ≤
      (40 * N / (N : ℝ) ^ (4 / 53 : ℝ)) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hS : goldbachG11EffectiveProductSupport N ε ⊆ Icc 1 N := by
    intro m hm
    have hd := goldbachG11ProductSupport_data (mem_filter.mp hm).1
    exact mem_Icc.mpr ⟨hd.1, hd.2.1.le⟩
  have h := G11FiniteGate.sum_gate_le_logCube (K := 20)
    (w := goldbachG11PrimeWindowWeight N ε) hN hQ
    (show 0 < (N : ℝ) ^ (4 / 53 : ℝ) from
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _)
    (Nat.cast_nonneg N) hS
    (fun m hm => (goldbachG11EffectiveProductSupport_primeFactors hm).1)
    (fun m hm => (goldbachG11EffectiveProductSupport_primeFactors hm).2.2)
    (fun m hm => goldbachG11PrimeWindowWeight_le hm)
  change (∑ d ∈ Icc 1 Q, |goldbachG11PrimeWindowGateLoss N ε d|) ≤ _ at h
  simpa only [abs_of_nonneg (goldbachG11PrimeWindowGateLoss_nonneg N _ ε),
    show (2 : ℝ) * (20 : ℕ) = 40 by norm_num] using h

/-- The threshold is chosen before both the window parameter and the modulus cutoff. -/
theorem goldbachG11PrimeWindowGateLoss_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ), Q ≤ N →
      (∑ d ∈ Icc 1 Q, goldbachG11PrimeWindowGateLoss N ε d) ≤
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
      goldbachG11PrimeWindowGateLoss_sum_le ε (by omega) hQ
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