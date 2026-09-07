import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWBounds

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset Filter
open scoped Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.Richert1969
noncomputable section

/-- The existing Mertens totient bound also pays moduli beyond the endpoint.
The monotonicity step is applied to log(d)/d, not to the totient itself. -/
theorem primeSW_reciprocal_totient {N d : ℕ} (hN : 3 ≤ N) (hd : 0 < d) :
    (1 : ℝ) / d.totient ≤
      richertReciprocalTotientConstant * Real.log N / (min d N : ℕ) := by
  by_cases hdN : d ≤ N
  · rw [min_eq_left hdN]
    exact reciprocal_totient_le_richertConstant_log_div (by omega) hd hdN
  · rw [min_eq_right (by omega : N ≤ d)]
    have hd3 : 3 ≤ d := by omega
    have hNd : (N : ℝ) ≤ d := by exact_mod_cast (by omega : N ≤ d)
    have heN : Real.exp 1 ≤ (N : ℝ) :=
      (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 3)).trans
        (by exact_mod_cast hN)
    have hm := Real.log_div_self_antitoneOn heN (heN.trans hNd) hNd
    have ht := reciprocal_totient_le_richertConstant_log_div
      (N := d) (m := d) (by omega) hd le_rfl
    exact ht.trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm
        richertReciprocalTotientConstant_pos.le)

/-- The literal progression mass is bounded by N/d+1, with no prime-density premise. -/
theorem primeSW_AP_count_le {N d : ℕ} (hd : 0 < d) (b : ℕ)
    (S : Finset ℕ) (hS : S ⊆ range (N + 1)) (h : ℕ) :
    primeSWSum S (fun n => n.Coprime h ∧ Nat.ModEq d n b) ≤
      (N : ℝ) / d + 1 := by
  have hp := primeSWSum_mono S (range (N + 1))
    (fun n => n.Coprime h ∧ Nat.ModEq d n b) (fun n => Nat.ModEq d n b)
    hS (fun _ _ hp => hp.2)
  have he : primeSWSum (range (N + 1)) (fun n => Nat.ModEq d n b) =
      (BombieriVinogradov.primesInAP N d b : ℝ) := primeSWSum_eq_card _ _
  rw [he] at hp
  apply hp.trans
  have hc : (d : ℝ) * BombieriVinogradov.primesInAP N d b ≤ (N : ℝ) + d := by
    exact_mod_cast modulus_mul_primesInAP_le N d b hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : ((N : ℝ) + d) / d = (N : ℝ) / d + 1 := by
    rw [add_div, div_self hdR.ne']
  exact (show (BombieriVinogradov.primesInAP N d b : ℝ) ≤ ((N : ℝ) + d) / d from
    (le_div_iff₀ hdR).mpr (by nlinarith)).trans_eq he

/-- Large-modulus envelope for the original independently sieved discrepancy.
The main term is divided by phi(d), including when d exceeds the support. -/
theorem primeSW_large_modulus_envelope {N d : ℕ} (hN : 3 ≤ N) (hd : 0 < d)
    (S : Finset ℕ) (hS : S ⊆ range (N + 1)) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy S primeSWBeta d h b| ≤
      (N : ℝ) / d + 1 + ((N : ℝ) + 1) *
        (richertReciprocalTotientConstant * Real.log N / (min d N : ℕ)) := by
  rw [primeSW_discrepancy_eq]
  have hm : primeSWSum S (fun n => n.Coprime (d * h)) ≤ (N : ℝ) + 1 := by
    apply (primeSWSum_le_card _ _).trans
    have hc := card_le_card hS
    rw [card_range] at hc
    exact_mod_cast hc
  have hφ := primeSW_reciprocal_totient hN hd
  have hmφ : primeSWSum S (fun n => n.Coprime (d * h)) / d.totient ≤
      ((N : ℝ) + 1) *
        (richertReciprocalTotientConstant * Real.log N / (min d N : ℕ)) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hm hφ (by positivity) (by positivity)
  have h0 := primeSWSum_nonneg S (fun n => n.Coprime h ∧ Nat.ModEq d n b)
  have h1 : 0 ≤ primeSWSum S (fun n => n.Coprime (d * h)) / d.totient := by
    exact div_nonneg (primeSWSum_nonneg _ _) (Nat.cast_nonneg _)
  calc
    _ ≤ primeSWSum S (fun n => n.Coprime h ∧ Nat.ModEq d n b) +
        primeSWSum S (fun n => n.Coprime (d * h)) / d.totient := by
      simpa only [abs_of_nonneg h0, abs_of_nonneg h1] using
        abs_sub (primeSWSum S (fun n => n.Coprime h ∧ Nat.ModEq d n b))
          (primeSWSum S (fun n => n.Coprime (d * h)) / d.totient)
    _ ≤ _ := add_le_add (primeSW_AP_count_le hd b S hS h) hmφ

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
