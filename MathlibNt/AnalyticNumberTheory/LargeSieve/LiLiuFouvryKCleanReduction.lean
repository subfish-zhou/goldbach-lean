import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKCleanSmooth
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeReduction

noncomputable section
open Classical Finset Filter
open scoped Topology
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Full zero-mode payment at the unchanged physical scale and higher endpoint. -/
theorem kClean_signedError_sq_le_nonzeroMode_c2
    {ι : Type*} {κ k ℓ j : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hj : 1 ≤ j) (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ i, 1 ≤ T i)
    (hN : ∀ i, ∀ n ∈ N i, T i ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T i)
    (hβ : ∀ i, ∀ n ∈ N i, |β i n| ≤ (fouvryTau k n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T i = x →
      x ^ ε ≤ T i → T i ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau ℓ m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      signedError S (N i) Q α (β i) c a ^ 2 ≤
        (∑ m ∈ S, α m ^ 2) * smoothWNonzeroMode M (N i) Q (β i) c a +
          x ^ 2 / Real.log x ^ A := by
  have hN' : ∀ i, N i ⊆ Ioc 0 ⌊2 * T i⌋₊ := by
    intro i n hn
    have hn' := hN i n hn
    refine mem_Ioc.mpr ⟨?_, Nat.le_floor hn'.2⟩
    have : (0 : ℝ) < n := by linarith [hT i]
    exact_mod_cast this
  have hT' : ∀ i, 1 ≤ 2 * T i := fun i => by linarith [hT i]
  filter_upwards [
    alpha_sq_mul_smoothWU_SWFamily_log_payment hk hℓ j (A + 1)
      (hSW.double_scale hT) hT' hN' hβ hε,
    kClean_dispersionUV_smooth_c2_dyadic_log_payment hℓ hk hj (A + 1),
    eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hzero huv hx hxlog
  intro i M L hM hL hMT hεT hTx hLx S Q hS hQ α c hα hc a
  have hMpos : 0 < M := by linarith
  have hLx' : L ≤ x := hLx.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (show (5 / 9 : ℝ) ≤ 1 by norm_num))
  have hzero' := hzero i M L hM hL
    (show M * (2 * T i) ≤ x by
      nlinarith [mul_nonneg hMpos.le (show 0 ≤ T i by linarith [hT i])])
    hLx' (show x ^ ε ≤ 2 * T i by linarith [hT i])
    S Q hS hQ α c hα hc a
  have huv' := huv M (T i) L hM (hT i) hL hMT hTx hLx
    S (dyadicCutoffNatSupport M) (N i) Q hS
    (scaledDyadicCutoff_mem_natSupport hMpos) (hN i) hQ α (β i) c hα (hβ i) hc a
  have hQ0 : ∀ q ∈ Q, q ≠ 0 := fun q hq => (mem_Ioc.mp (hQ hq)).1.ne'
  have hdisp := signedError_sq_le_dyadicCutoff_dispersion hMpos
    S (N i) Q α (β i) c a hS
  rw [dispersionW_eq_smoothWMain_add_nonzeroMode hMpos (N i) Q (β i) c a hQ0]
    at hdisp
  have hsum : 0 ≤ ∑ m ∈ S, α m ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have he : 2 * (x ^ 2 / Real.log x ^ (A + 1)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_succ (Real.log x) A, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < Real.log x)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (sub_nonneg.mpr hxlog)]
  have hmain := mul_le_mul_of_nonneg_left
    (le_abs_self (smoothWMain M (N i) Q (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  have hu := mul_le_mul_of_nonneg_left
    (le_abs_self (dispersionU (dyadicCutoffNatSupport M) (N i) Q
      (fun m => scaledDyadicCutoff M m) (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  have hv := mul_le_mul_of_nonneg_left
    (neg_le_abs (dispersionV (dyadicCutoffNatSupport M) (N i) Q
      (fun m => scaledDyadicCutoff M m) (β i) c a -
      smoothUMain M (N i) Q (β i) c a)) hsum
  nlinarith


/-- Uniform clean reduction for a fixed shift multiple; no deletion term remains. -/
theorem kClean_signedError_sq_le_clean_nonzeroMode_c2
    {ι : Type*} {κ k i j : ℕ} (A : ℕ)
    {T : ι → ℝ} {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ z, 1 ≤ T z)
    (hN : ∀ z, ∀ n ∈ N z, T z ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * T z)
    (hβ : ∀ z, ∀ n ∈ N z, |β z n| ≤ (fouvryTau k n : ℝ))
    {Cscale ε : ℝ} (hC : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ι, ∀ M L : ℝ,
      1 ≤ M → 1 ≤ L → 4 * M * T z = x →
      x ^ ε ≤ T z → T z ≤ x ^ (1 / 9 : ℝ) → L ≤ x ^ (5 / 9 : ℝ) →
      ∀ S Q : Finset ℕ,
      (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) →
      Q ⊆ Ioc 0 ⌊L⌋₊ → ∀ α c : ℕ → ℝ,
      (∀ m ∈ S, |α m| ≤ (fouvryTau i m : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) →
      ∀ a : ℤ, a ≠ 0 → |(a : ℝ)| ≤ Cscale * x →
      signedError S (N z) Q α (β z) c a ^ 2 ≤
        2 * (∑ m ∈ S, α m ^ 2) *
          smoothWNonzeroMode M (N z) Q (betaClean (β z) a) c a +
          x ^ 2 / Real.log x ^ A := by
  have hcleanβ : ∀ z : BetaCleanIndex T (ε / 2), ∀ n ∈ N z.index,
      |betaClean (β z.index) z.residue n| ≤ (fouvryTau (k + 1) n : ℝ) := by
    intro z n hn
    exact ((abs_betaClean_le _ _ _).trans (hβ z.index n hn)).trans
      (by exact_mod_cast fouvryTau_le_succ k n)
  have hreduce := kClean_signedError_sq_le_nonzeroMode_c2
    (k := k + 1) (ℓ := i + 1) (j := j + 1) (by omega) (by omega) (by omega)
    (A + 2) (hSW.betaClean hβ (show 0 < ε / 2 by positivity))
    (fun z : BetaCleanIndex T (ε / 2) => z.one_le_T)
    (fun z => hN z.index) hcleanβ (show 0 < ε / 2 by positivity)
  filter_upwards [hreduce, kClean_signedError_log_payment i k j (A + 2) hC hε,
    eventually_ge_atTop Cscale,
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with x hreduce hdelete hxC hlog
  intro z M L hM hL hscale hlow hhigh hlevel S Q hS hQ α c hα hc a ha hax
  have hx : 1 ≤ x := hC.trans hxC
  have hlowHalf : x ^ (ε / 2) ≤ T z :=
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith : ε / 2 ≤ ε)).trans hlow
  let z' : BetaCleanIndex T (ε / 2) :=
    ⟨z, a, Cscale * x, hT z, by nlinarith, ha, by simpa using hax,
      (kClean_aux_scale_rpow_le hC hxC hε).trans hlow⟩
  have hα' : ∀ m ∈ S, |α m| ≤ (fouvryTau (i + 1) m : ℝ) := by
    intro m hm
    exact (hα m hm).trans (by exact_mod_cast fouvryTau_le_succ i m)
  have hc' : ∀ q ∈ Q, |c q| ≤ (fouvryTau (j + 1) q : ℝ) := by
    intro q hq
    exact (hc q hq).trans (by exact_mod_cast fouvryTau_le_succ j q)
  have hclean := hreduce z' M L hM hL hscale hlowHalf hhigh hlevel
    S Q hS hQ α c hα' hc' a
  have hdeleted := (hdelete M (T z) L hM (hT z) hL hscale.symm hlow hlevel
    S (N z) Q hS (hN z) hQ α (β z) c hα (hβ z) hc a ha hax).1
  have hlog0 : 0 < Real.log x := by linarith
  have hB0 : 0 ≤ x / Real.log x ^ (A + 2) := by positivity
  have hdeletedSq :
      signedError S (N z) Q α (betaDivisorPart (β z) a) c a ^ 2 ≤
        (x / Real.log x ^ (A + 2)) ^ 2 := by
    nlinarith [sq_abs (signedError S (N z) Q α (betaDivisorPart (β z) a) c a),
      mul_nonneg (sub_nonneg.mpr hdeleted)
        (add_nonneg hB0 (abs_nonneg (signedError S (N z) Q α
          (betaDivisorPart (β z) a) c a)))]
  have hlogA : 1 ≤ Real.log x ^ (A + 2) :=
    one_le_pow₀ (by linarith : 1 ≤ Real.log x)
  have hdelpay : (x / Real.log x ^ (A + 2)) ^ 2 ≤
      x ^ 2 / Real.log x ^ (A + 2) := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg x) (pow_pos hlog0 _)
    nlinarith
  have hpay : 4 * (x ^ 2 / Real.log x ^ (A + 2)) ≤ x ^ 2 / Real.log x ^ A := by
    rw [pow_add, div_mul_eq_div_div, ← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hlog0)).mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ x ^ 2 / Real.log x ^ A)
      (show 0 ≤ Real.log x ^ 2 - 4 by nlinarith)]
  have hsplit := signedError_eq_clean_add_divisorPart S (N z) Q α (β z) c a
  have hsq : signedError S (N z) Q α (β z) c a ^ 2 ≤
      2 * signedError S (N z) Q α (betaClean (β z) a) c a ^ 2 +
        2 * signedError S (N z) Q α (betaDivisorPart (β z) a) c a ^ 2 := by
    rw [hsplit]
    nlinarith [sq_nonneg (signedError S (N z) Q α (betaClean (β z) a) c a -
      signedError S (N z) Q α (betaDivisorPart (β z) a) c a)]
  dsimp only [z'] at hclean
  linarith


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
