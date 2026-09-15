import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanError
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic payment of beta divisor deletion in the actual signed error

The thresholds precede the changing residue, scales, finite supports and signed
coefficients. All three divisor orders may be zero. The equality progression
is paid separately, without a nondivisibility, SW, Shiu or distribution input.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem betaPayment_eventually_log_mul_rpow_le (K : ℝ) (hK : 0 ≤ K) (B : ℕ)
    {b d : ℝ} (hbd : b < d) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ B * x ^ b ≤ x ^ d := by
  have hb := ((isLittleO_log_rpow_rpow_atTop (B : ℝ)
    (sub_pos.mpr hbd)).const_mul_left (K * 2 ^ B)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hx hx1 hlog
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hb' : K * 2 ^ B * Real.log x ^ B ≤ x ^ (d - b) := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (by positivity : 0 ≤ K * 2 ^ B * Real.log x ^ B),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hx
  calc
    _ ≤ K * (2 * Real.log x) ^ B * x ^ b := by
      gcongr
      linarith
    _ = (K * 2 ^ B * Real.log x ^ B) * x ^ b := by rw [mul_pow]; ring
    _ ≤ x ^ (d - b) * x ^ b :=
      mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hx0.le _)
    _ = x ^ d := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- Uniformity also covers bounded small integers, not just integers tending
to infinity along with the scale. -/
theorem betaPayment_eventually_tau_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 2 * x →
      (fouvryTau k n : ℝ) ≤ x ^ δ := by
  obtain ⟨C, hC, hbound⟩ :=
    fouvryTau_le_const_rpow (k := k + 1) (by omega)
      (show 0 < δ / 2 by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < δ / 2 by linarith)).eventually_ge_atTop
      (C * (2 : ℝ) ^ (δ / 2))] with x hx hconst
  intro n hn hnx
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ (fouvryTau (k + 1) n : ℝ) := by exact_mod_cast fouvryTau_le_succ k n
    _ ≤ C * (n : ℝ) ^ (δ / 2) := hbound n hn
    _ ≤ C * (2 * x) ^ (δ / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnx (by linarith)) hC.le
    _ = (C * (2 : ℝ) ^ (δ / 2)) * x ^ (δ / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le, mul_assoc]
    _ ≤ x ^ (δ / 2) * x ^ (δ / 2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx0.le _)
    _ = x ^ δ := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- A finite cardinality estimate for arbitrary, possibly sparse, dyadic
alpha supports. -/
theorem betaPayment_card_dyadic_le {M : ℝ} (hM : 1 ≤ M) (S : Finset ℕ)
    (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) :
    (S.card : ℝ) ≤ 2 * M := by
  have hsub : S ⊆ Ioc 0 ⌊2 * M⌋₊ := by
    intro m hm
    apply mem_Ioc.mpr
    refine ⟨?_, Nat.le_floor (hS m hm).2⟩
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hcard := card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show (S.card : ℝ) ≤ (⌊2 * M⌋₊ : ℝ) by exact_mod_cast hcard).trans
    (Nat.floor_le (by linarith))

/-- The actual signed error after deletion, before spending the power saving.
The equality `m*n=a` is included in this estimate. -/
theorem betaPayment_eventually_signedError_bound (i k j : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T → L ≤ x →
      ∀ S N Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
      Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ α β c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
      |signedError S N Q α (betaDivisorPart β a) c a| ≤
        4 * (M + L) * x ^ (3 * δ) := by
  have hlog (B : ℕ) : ∀ᶠ x : ℝ in atTop, (1 + Real.log x) ^ B ≤ x ^ δ := by
    simpa using betaPayment_eventually_log_mul_rpow_le 1 (by norm_num) B
      (b := 0) hδ
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    betaPayment_eventually_tau_le i hδ,
    betaPayment_eventually_tau_le (k + 1) hδ,
    betaPayment_eventually_tau_le (j + 1) hδ,
    hlog j, hlog (2 * j)] with x hx hτi hτk hτj hlogj hlog2j
  intro M T L hM hT hL he hLx S N Q hS hN hQ α β c hα hβ hc a ha hax
  have hx0 : 0 < x := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hMx : 2 * M ≤ x := by nlinarith
  have hmpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hnpos : ∀ n ∈ N, 0 < n := by
    intro n hn
    have : (0 : ℝ) < n := by have := (hN n hn).1; linarith
    exact_mod_cast this
  have hα' : ∀ m ∈ S, |α m| ≤ x ^ δ := by
    intro m hm
    exact (hα m hm).trans (hτi m (hmpos m hm) (by
      have := (hS m hm).2; linarith))
  have hmass : (∑ n ∈ N, |betaDivisorPart β a n|) ≤ x ^ δ := by
    apply (sum_abs_betaDivisorPart_le k N β ha hβ).trans
    apply hτk a.natAbs (Int.natAbs_pos.mpr ha)
    have ha' : (a.natAbs : ℝ) = |(a : ℝ)| := by simp
    rw [ha']
    linarith
  have hprog : ∀ n ∈ N, ∀ m ∈ S, (m : ℤ) * n ≠ a →
      (∑ q ∈ Q, if Int.ModEq q ((m : ℤ) * n) a then |c q| else 0) ≤ x ^ δ := by
    intro n hn m hm hne
    have hne' : (m : ℤ) * n - a ≠ 0 := sub_ne_zero.mpr hne
    apply (sum_modEq_abs_le_fouvryTau j Q c hc m n a hne').trans
    apply hτj _ (Int.natAbs_pos.mpr hne')
    have hmn : (m : ℝ) * n ≤ x := by
      have := mul_le_mul (hS m hm).2 (hN n hn).2 (Nat.cast_nonneg n) (by positivity)
      nlinarith
    calc
      _ = |(m : ℝ) * n - (a : ℝ)| := by simp
      _ ≤ |(m : ℝ) * n| + |(a : ℝ)| := abs_sub _ _
      _ ≤ 2 * x := by rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]; linarith
  have hHL : 0 ≤ 1 + Real.log L := by have := Real.log_nonneg hL; linarith
  have hHLx : 1 + Real.log L ≤ 1 + Real.log x := by
    have := Real.log_le_log (by linarith : 0 < L) hLx
    linarith
  have hcsum : (∑ q ∈ Q, |c q|) ≤ L * x ^ δ := by
    calc
      _ ≤ ∑ q ∈ Q, (fouvryTau (j + 1) q : ℝ) := by
        apply sum_le_sum
        intro q hq
        exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
      _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau (j + 1) q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ L * (1 + Real.log L) ^ j := by
        simpa using sum_fouvryTau_le_real (k := j + 1) (by omega) hL
      _ ≤ L * (1 + Real.log x) ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHL hHLx j) hL0
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogj hL0
  have hcphi : (∑ q ∈ Q, |c q| / (q.totient : ℝ)) ≤ x ^ δ := by
    calc
      _ ≤ ∑ q ∈ Q, (fouvryTau j q : ℝ) / q.totient := by
        apply sum_le_sum
        intro q hq
        exact div_le_div_of_nonneg_right (hc q hq) (Nat.cast_nonneg _)
      _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau j q : ℝ) / q.totient :=
        sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
      _ ≤ (1 + Real.log L) ^ (2 * j) := sum_fouvryTau_div_totient_le_real j hL
      _ ≤ (1 + Real.log x) ^ (2 * j) := pow_le_pow_left₀ hHL hHLx _
      _ ≤ _ := hlog2j
  have hcard := betaPayment_card_dyadic_le hM S hS
  have hp : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  calc
    _ ≤ x ^ δ * (∑ n ∈ N, |betaDivisorPart β a n|) *
        ((S.card : ℝ) * x ^ δ + ∑ q ∈ Q, |c q| +
          (S.card : ℝ) * ∑ q ∈ Q, |c q| / (q.totient : ℝ)) :=
      signedError_abs_le_split S N Q α (betaDivisorPart β a) c a hp hp hα' hnpos hprog
    _ ≤ x ^ δ * x ^ δ * (2 * M * x ^ δ + L * x ^ δ + 2 * M * x ^ δ) := by
      gcongr
    _ = (4 * M + L) * x ^ (3 * δ) := by
      have hp3 : x ^ δ * x ^ δ * x ^ δ = x ^ (3 * δ) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1
        ring
      calc
        _ = (4 * M + L) * (x ^ δ * x ^ δ * x ^ δ) := by ring
        _ = _ := by rw [hp3]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx0.le _)

/-- Power saving uniform in the complete changing input. In particular, the
residue may vary throughout `0 < |a| ≤ x`, including equality progressions. -/
theorem betaDivisorPart_signedError_power_saving (i k j : ℕ)
   {ε : ℝ} (hε : 0 < ε) :
   ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
     1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T →
     x ^ ε ≤ T → L ≤ x ^ (5 / 9 : ℝ) →
     ∀ S N Q : Finset ℕ,
     (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
     (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
     Q ⊆ Ioc 0 ⌊L⌋₊ →
     ∀ α β c : ℕ → ℝ,
     (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
     (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
     (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
     ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
     |signedError S N Q α (betaDivisorPart β a) c a| ≤
       x ^ (1 - min ε (4 / 9) / 2) := by
 let ρ : ℝ := min ε (4 / 9)
 have hρ : 0 < ρ := lt_min hε (by norm_num)
 have hρε : ρ ≤ ε := min_le_left _ _
 have hρ4 : ρ ≤ 4 / 9 := min_le_right _ _
 filter_upwards [eventually_ge_atTop (1 : ℝ),
   betaPayment_eventually_signedError_bound i k j (show 0 < ρ / 12 by linarith),
   betaPayment_eventually_log_mul_rpow_le 8 (by norm_num) 0
     (b := 1 - 3 * ρ / 4) (d := 1 - ρ / 2) (by linarith)]
   with x hx hb hpay
 intro M T L hM hT hL he hεT hLpower S N Q hS hN hQ α β c hα hβ hc a ha hax
 have hx0 : 0 < x := by linarith
 have hM0 : 0 ≤ M := by linarith
 have hLx : L ≤ x := by
   calc
     L ≤ x ^ (5 / 9 : ℝ) := hLpower
     _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
     _ = x := Real.rpow_one x
 have hρT : x ^ ρ ≤ T :=
   (Real.rpow_le_rpow_of_exponent_le hx hρε).trans hεT
 have hMpower : M ≤ x ^ (1 - ρ) := by
   rw [Real.rpow_sub hx0, Real.rpow_one]
   apply (le_div_iff₀ (Real.rpow_pos_of_pos hx0 _)).mpr
   have := mul_le_mul_of_nonneg_left hρT hM0
   nlinarith
 have hLpower' : L ≤ x ^ (1 - ρ) :=
   hLpower.trans (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
 calc
   _ ≤ 4 * (M + L) * x ^ (3 * (ρ / 12)) :=
     hb M T L hM hT hL he hLx S N Q hS hN hQ α β c hα hβ hc a ha hax
   _ ≤ 4 * (x ^ (1 - ρ) + x ^ (1 - ρ)) * x ^ (3 * (ρ / 12)) := by
     gcongr
   _ = 8 * x ^ (1 - 3 * ρ / 4) := by
     calc
       _ = 8 * (x ^ (1 - ρ) * x ^ (3 * (ρ / 12))) := by ring
       _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring
   _ ≤ x ^ (1 - ρ / 2) := by simpa using hpay

/-- The genuine C.2 preprocessing payment, not an assumed error estimate.
For fixed orders (including zero), saving order, and positive epsilon, one
threshold works simultaneously for all scales, supports, signed sequences and
nonzero residues in the full permitted range. The original-to-clean difference
and the triangle transfer are part of the same uniform conclusion. -/
theorem betaClean_signedError_log_payment (i k j A : ℕ)
   {ε : ℝ} (hε : 0 < ε) :
   ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
     1 ≤ M → 1 ≤ T → 1 ≤ L → x = 4 * M * T →
     x ^ ε ≤ T → L ≤ x ^ (5 / 9 : ℝ) →
     ∀ S N Q : Finset ℕ,
     (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
     (∀ n ∈ N, T ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T) →
     Q ⊆ Ioc 0 ⌊L⌋₊ →
     ∀ α β c : ℕ → ℝ,
     (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
     (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
     (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
     ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ x →
     |signedError S N Q α (betaDivisorPart β a) c a| ≤ x / Real.log x ^ A ∧
     |signedError S N Q α β c a - signedError S N Q α (betaClean β a) c a| ≤
       x / Real.log x ^ A ∧
     |signedError S N Q α β c a| ≤
       |signedError S N Q α (betaClean β a) c a| + x / Real.log x ^ A := by
 have hρ : 0 < min ε (4 / 9 : ℝ) := lt_min hε (by norm_num)
 filter_upwards [eventually_ge_atTop (2 : ℝ),
   betaDivisorPart_signedError_power_saving i k j hε,
   betaPayment_eventually_log_mul_rpow_le 1 (by norm_num) A
     (b := 1 - min ε (4 / 9) / 2) (d := 1) (by linarith)]
   with x hx hb hpay
 intro M T L hM hT hL he hεT hLpower S N Q hS hN hQ α β c hα hβ hc a ha hax
 have hx0 : 0 < x := by linarith
 have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
 have hbound := hb M T L hM hT hL he hεT hLpower
   S N Q hS hN hQ α β c hα hβ hc a ha hax
 have hpaid : |signedError S N Q α (betaDivisorPart β a) c a| ≤
     x / Real.log x ^ A := by
   apply (le_div_iff₀ (pow_pos hlog0 A)).mpr
   calc
     _ ≤ x ^ (1 - min ε (4 / 9) / 2) * (1 + Real.log x) ^ A :=
       mul_le_mul hbound
         (pow_le_pow_left₀ hlog0.le (by linarith) A)
         (pow_nonneg hlog0.le A) (Real.rpow_nonneg hx0.le _)
     _ ≤ x := by simpa only [one_mul, Real.rpow_one, mul_comm] using hpay
 have hsplit := signedError_eq_clean_add_divisorPart S N Q α β c a
 refine ⟨hpaid, ?_, ?_⟩
 · have hdiff : signedError S N Q α β c a -
       signedError S N Q α (betaClean β a) c a =
         signedError S N Q α (betaDivisorPart β a) c a := by linarith
   rw [hdiff]
   exact hpaid
 · calc
     _ = |signedError S N Q α (betaClean β a) c a +
         signedError S N Q α (betaDivisorPart β a) c a| := congrArg abs hsplit
     _ ≤ |signedError S N Q α (betaClean β a) c a| +
         |signedError S N Q α (betaDivisorPart β a) c a| := abs_add_le _ _
     _ ≤ _ := add_le_add le_rfl hpaid

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
