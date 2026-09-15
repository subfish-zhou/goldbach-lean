import MathlibNt.Wu2008DoubleSieve.PhiMonotone

/-!
# Relative payment of the actual strict/closed Phi endpoint

For positive complements, a lost prime endpoint injects into positive
multiples of that prime in `[1,N/d]`. The loss is at most `N/(d*z)`.
The actual reciprocal box mass and polynomially growing cutoff then
pay the aggregate by `epsilon*Theta`, uniformly over all `s` in `[1,10]`.
This endpoint is unrelated to the whole-carrier S3 crossing correction.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem sourceSieveCount_eq_closed_add_loss (N d : ℕ) (z : ℝ) :
    sourceSieveCount N d (d * N) z =
      sourceSieveCountLE N d (d * N) z +
        ((sieveEndpointLoss N d (d * N) z).card : ℤ) := by
  unfold sourceSieveCount sourceSieveCountLE
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right d N),
    sourceSieveCarrierLE_of_dvd_modulus N (dvd_mul_right d N)]
  exact sieveCount_eq_closed_add_loss N d (d * N) z

/-- The selected divisor is retained in the denominator. No count at zero
is included: evenness and `N>=4` make every prime complement positive. -/
theorem sieveEndpointLoss_card_le_divisor {N d M : ℕ} {z : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd0 : 0 < d) (hz : 0 < z) :
    ((sieveEndpointLoss N d M z).card : ℝ) ≤ (N : ℝ) / ((d : ℝ) * z) := by
  have hcard : (sieveEndpointLoss N d M z).card ≤ (fixedPrimeEndpoint (N / d) z).card := by
    apply card_le_card_of_injOn (fun p => (N - p) / d)
    · intro p hp
      obtain ⟨hpN, hprime, hd, _, q, hq, _, hqz, hqn⟩ := mem_sieveEndpointLoss.mp hp
      have hn := complement_pos_of_even hN he hpN hprime
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨Nat.div_pos (Nat.le_of_dvd hn hd) hd0,
          Nat.div_le_div_right (Nat.sub_le N p)⟩, q, hq, hqz, hqn⟩
    · intro p hp q hq hpq
      have hp' := mem_sieveEndpointLoss.mp hp
      have hq' := mem_sieveEndpointLoss.mp hq
      have hpdiv := Nat.mul_div_cancel' hp'.2.2.1
      have hqdiv := Nat.mul_div_cancel' hq'.2.2.1
      have heq := congrArg (fun n : ℕ => d * n) hpq
      dsimp at heq
      rw [hpdiv, hqdiv] at heq
      omega
  calc
    _ ≤ ((fixedPrimeEndpoint (N / d) z).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((N / d : ℕ) : ℝ) / z := fixedPrimeEndpoint_card_le (N / d) hz
    _ ≤ ((N : ℝ) / d) / z :=
      div_le_div_of_nonneg_right Nat.cast_div_le hz.le
    _ = _ := by ring

theorem wuBoxPhi_sub_closed_eq {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (s : ℝ) :
    wuBoxPhi N δ W s - wuBoxPhiLE N δ W s =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ((sieveEndpointLoss N d (d * N) (wuLocalCutoff N δ d s)).card : ℝ) := by
  unfold wuBoxPhi convolutionSieveCount wuBoxPhiLE boxConvolutionSupport
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  have h := sourceSieveCount_eq_closed_add_loss N d (wuLocalCutoff N δ d s)
  have h' : (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d s) : ℝ) =
      (sourceSieveCountLE N d (d * N) (wuLocalCutoff N δ d s) : ℝ) +
        ((sieveEndpointLoss N d (d * N) (wuLocalCutoff N δ d s)).card : ℝ) := by
    exact_mod_cast h
  rw [h']
  ring

theorem wuBoxPhi_endpoint_le_mass {i N : ℕ} {δ s Z : ℝ}
    (W : Fin i → Finset ℕ) (hN : 4 ≤ N) (he : Even N) (hZ : 0 < Z)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hz : ∀ d ∈ boxConvolutionSupport W, Z ≤ wuLocalCutoff N δ d s) :
    wuBoxPhi N δ W s - wuBoxPhiLE N δ W s ≤
      (N : ℝ) / Z * boxConvolutionReciprocalMass W := by
  rw [wuBoxPhi_sub_closed_eq, boxConvolutionReciprocalMass, mul_sum]
  apply sum_le_sum
  intro d hmem
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd d hmem
  calc
    _ ≤ (convolutionCoeff W d : ℝ) *
        ((N : ℝ) / ((d : ℝ) * wuLocalCutoff N δ d s)) :=
      mul_le_mul_of_nonneg_left
        (sieveEndpointLoss_card_le_divisor hN he (hd d hmem) (hZ.trans_le (hz d hmem)))
        (Nat.cast_nonneg _)
    _ ≤ (convolutionCoeff W d : ℝ) * ((N : ℝ) / ((d : ℝ) * Z)) := by
      gcongr
      exact hz d hmem
    _ = _ := by ring

/-- Both strict and printed closed Phi have a uniformly paid difference.
This allows lower consumers to change convention without assuming endpoint
avoidance or hiding a nonuniform family of prime equalities. -/
theorem wu_boxPhi_endpoint_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ,
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          boxSquaredPrefixes ((N : ℝ) ^ (1 / 2 - δ)) V →
          ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
          0 ≤ wuBoxPhi N δ (convolutionWuWindows N Δ V) s -
              wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s ∧
            wuBoxPhi N δ (convolutionWuWindows N Δ V) s -
                wuBoxPhiLE N δ (convolutionWuWindows N Δ V) s ≤
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
                (convolutionWuWindows N Δ V) := by
  let α := wuLocalExponent k δ / 10
  have hα : 0 < α := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨c, hc, N1, hTheta⟩ := wu_boxTheta_lower k hδ hδhi
  obtain ⟨N2, hmass⟩ := wu_boxConvolution_mass_bounds k (pow_pos hδ (k + 1))
  have hbudget := box_eventually_log_power_budget (5 * k + 2)
    (show 0 < (6 : ℝ) ^ k / (ε * c) by positivity) hα
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop N1, eventually_ge_atTop N2,
    eventually_ge_atTop (4 : ℕ), hbudget] with N hN1 hN2 hN hpay
  intro he i hik Δ hlo hhi V hV hprefix s hs hs10
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos hNreal
  have hupper : ∀ j, V j ≤ N := boxSquaredPrefixes_upper
    (fun j => (one_le_rpow hNreal.le (pow_pos hδ _).le).trans (hV j)) hprefix
    (by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNreal.le
        (show 1 / 2 - δ ≤ 1 by linarith))
  have hmasshi := (hmass N hN2 i hik Δ hlo hhi V hV hupper).2
  have hsupport := fun d hd => wuLocal_support_bounds (by omega : 1 ≤ N) hδ hδhi hV
    ((boxSquaredPrefixes_iff _ _).mp hprefix) (d := d) (Δ := Δ) hd
  have hcut := fun d hd => wuLocalCutoff_lower (by omega : 1 ≤ N) hδ hδhi hs hs10
    (hsupport d hd).2.2
  have hb := wuBoxPhi_endpoint_le_mass (convolutionWuWindows N Δ V) hN he
    (show 0 < (N : ℝ) ^ α by positivity) (fun d hd => (hsupport d hd).1) hcut
  refine ⟨sub_nonneg.mpr (wuBoxPhiLE_le_strict N δ _ s), ?_⟩
  calc
    _ ≤ (N : ℝ) / (N : ℝ) ^ α *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := hb
    _ ≤ (N : ℝ) / (N : ℝ) ^ α * 6 ^ k :=
      mul_le_mul_of_nonneg_left hmasshi (by positivity)
    _ = 6 ^ k * (N : ℝ) / (N : ℝ) ^ α := by ring
    _ ≤ 6 ^ k * (N : ℝ) / ((6 ^ k / (ε * c)) * log (N : ℝ) ^ (5 * k + 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpay
    _ = ε * (c * (N : ℝ) / log N ^ (5 * k + 2)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hTheta N hN1 i hik Δ hlo hhi V hV hprefix) hε.le

end Wu2008DoubleSieve
