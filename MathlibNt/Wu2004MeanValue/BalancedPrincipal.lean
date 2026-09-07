import MathlibNt.Wu2004MeanValue.PrincipalWeighted

/-!
# Principal errors for balanced cofactor profiles

The cofactor may extend to `x^(1-eta)`. Applying the already proved real
prime-prefix estimate at `ceil(x/m)` retains the harmonic `1/m` gain.
The logarithmic comparison now costs `eta^(-A)`, not the square-root
specialization's `2^A`. No source-wise cancellation estimate is used here.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.LargeSieve

noncomputable section

theorem balanced_principal_moving_term_bound (A eta : ℝ)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ x ^ (1 - eta) →
      ∀ r : ℝ, 2 ≤ r → r ≤ x / m →
      |principalError r| ≤ (C * x / Real.log x ^ A) / m := by
  obtain ⟨K, hK, N₀, hbound⟩ := principal_real_prefix_bound A hA
  refine ⟨2 * K / eta ^ A, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [(tendsto_rpow_atTop heta).eventually
    (eventually_ge_atTop (N₀ : ℝ)), eventually_ge_atTop (Real.exp 1)]
    with x hpower hxexp
  intro m hm hmx r hr hrx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxexp
  have hx0 : 0 < x := by
    have := Real.exp_pos (1 : ℝ)
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hroot : x ^ eta ≤ x / m := by
    apply (le_div_iff₀ hm0).mpr
    calc
      _ ≤ x ^ eta * x ^ (1 - eta) :=
        mul_le_mul_of_nonneg_left hmx (Real.rpow_nonneg hx0.le _)
      _ = x := by rw [← Real.rpow_add hx0]; simp
  let T : ℕ := ⌈x / m⌉₊
  have hTlower : x / m ≤ (T : ℝ) := Nat.le_ceil _
  have hTroot : x ^ eta ≤ (T : ℝ) := hroot.trans hTlower
  have hTlarge : N₀ ≤ T := by exact_mod_cast hpower.trans hTroot
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hlogs : eta * Real.log x ≤ Real.log (T : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 eta) hTroot
    rwa [Real.log_rpow hx0] at h
  have hTlog : 0 < Real.log (T : ℝ) := (mul_pos heta hlog0).trans_le hlogs
  have hquot1 : 1 ≤ x / (m : ℝ) :=
    (Real.one_le_rpow hx1 heta.le).trans hroot
  have hTupper : (T : ℝ) ≤ 2 * x / m := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x / (m : ℝ) by positivity)
    change (T : ℝ) < x / (m : ℝ) + 1 at h
    calc
      _ ≤ 2 * (x / m) := by linarith
      _ = _ := by ring
  have hsaving : eta ^ A * Real.log x ^ A ≤ Real.log (T : ℝ) ^ A := by
    rw [← Real.mul_rpow heta.le hlog0.le]
    exact Real.rpow_le_rpow (by positivity) hlogs hA.le
  have hmul : (T : ℝ) * m ≤ 2 * x := (le_div_iff₀ hm0).mp hTupper
  refine (hbound T hTlarge r hr (hrx.trans hTlower)).trans ?_
  apply (le_div_iff₀ hm0).mpr
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hTlog A)).mpr
  have hscale := mul_le_mul_of_nonneg_left hsaving (show 0 ≤ 2 * K * x by positivity)
  have hsize := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ K * (eta ^ A * Real.log x ^ A) by positivity)
  rw [show 2 * K / eta ^ A * x * Real.log (T : ℝ) ^ A =
    (2 * K * x * Real.log (T : ℝ) ^ A) / eta ^ A by ring]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos heta A)).mpr
  nlinarith

theorem balanced_principal_moving_sum_bound (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ x ^ (1 - eta)) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      |∑ m ∈ S, f m * principalError (r m)| ≤ C * x / Real.log x ^ A := by
  obtain ⟨K, hK, x₀, hterm⟩ :=
    balanced_principal_moving_term_bound (A + 1) eta (by linarith) heta
  refine ⟨2 * (F + 1) * K, by positivity, max x₀ (Real.exp 1), ?_⟩
  intro x hx S f r hS hf hr
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxexp : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxexp
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hupper : x ^ (1 - eta) ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : 1 - eta ≤ 1)
  have hsubset : S ⊆ Icc 1 ⌊x⌋₊ := fun m hm =>
    mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor ((hS m hm).2.trans hupper)⟩
  have hharm : ∑ m ∈ S, (m : ℝ)⁻¹ ≤ 2 * Real.log x := by
    calc
      _ ≤ ∑ m ∈ Icc 1 ⌊x⌋₊, (m : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
      _ = (harmonic ⌊x⌋₊ : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx1
      _ ≤ _ := by linarith
  calc
    _ ≤ ∑ m ∈ S, |f m * principalError (r m)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, ((F + 1) * K * x / Real.log x ^ (A + 1)) * (m : ℝ)⁻¹ := by
      apply sum_le_sum
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (hS m hm).1
      have ht := hterm x hxx₀ m (hS m hm).1 (hS m hm).2 (r m) (hr m hm).1
        ((le_div_iff₀ hm0).mpr (by simpa only [mul_comm] using (hr m hm).2))
      rw [abs_mul]
      calc
        _ ≤ (F + 1) * ((K * x / Real.log x ^ (A + 1)) / m) :=
          mul_le_mul (by linarith [hf m hm]) ht (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = ((F + 1) * K * x / Real.log x ^ (A + 1)) *
        (∑ m ∈ S, (m : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ ((F + 1) * K * x / Real.log x ^ (A + 1)) * (2 * Real.log x) :=
      mul_le_mul_of_nonneg_left hharm (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_one]
      field_simp

theorem balanced_coprimePrincipalSum_log_saving (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ (d : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ),
      0 < d → (d : ℝ) ≤ x →
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ x ^ (1 - eta)) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ x) →
      |coprimePrincipalSum S f r d| ≤ C * x / Real.log x ^ A := by
  obtain ⟨J, hJ, x₁, hcore⟩ := balanced_principal_moving_sum_bound A eta F hA heta hF
  have hlim := (isLittleO_log_rpow_rpow_atTop (A + 1) heta).bound
    (show (0 : ℝ) < 1 by norm_num)
  refine ⟨J + F / Real.log 2, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlim, eventually_ge_atTop x₁, eventually_ge_atTop (Real.exp 1)]
    with x hlim hx₁ hxexp
  intro d S f r hd hdx hS hf hr
  have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxexp
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hxexp
  have hlog0 : 0 < Real.log x := by linarith
  have hpay : Real.log x ^ (A + 1) ≤ x ^ eta := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] using hlim
  have hcard : (S.card : ℝ) ≤ x ^ (1 - eta) := by
    have hsub : S ⊆ Icc 1 ⌊x ^ (1 - eta)⌋₊ := fun m hm =>
      mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
    have h := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    exact (by exact_mod_cast h : (S.card : ℝ) ≤ ⌊x ^ (1 - eta)⌋₊).trans
      (Nat.floor_le (Real.rpow_nonneg hx0.le _))
  have hdel : F * S.card * d.primeFactors.card ≤
      (F / Real.log 2) * x / Real.log x ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ ≤ F * x ^ (1 - eta) * ((Real.log 2)⁻¹ * Real.log x) *
          Real.log x ^ A := by
        gcongr
        exact PanLow.primeFactors_card_le_log_of_le hd hdx
      _ = (F / Real.log 2) * x ^ (1 - eta) * Real.log x ^ (A + 1) := by
        rw [Real.rpow_add hlog0, Real.rpow_one]
        ring
      _ ≤ (F / Real.log 2) * x ^ (1 - eta) * x ^ eta := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hx0]; simp
  calc
    _ ≤ |∑ m ∈ S, f m * principalError (r m)| +
        |coprimePrincipalSum S f r d - ∑ m ∈ S, f m * principalError (r m)| := by
      simpa only [add_sub_cancel] using
        abs_add_le (∑ m ∈ S, f m * principalError (r m))
          (coprimePrincipalSum S f r d - ∑ m ∈ S, f m * principalError (r m))
    _ ≤ J * x / Real.log x ^ A + (F / Real.log 2) * x / Real.log x ^ A :=
      add_le_add (hcore x hx₁ S f r hS hf hr)
        ((coprimePrincipalSum_sub_core_le S f r d F hd hF hf).trans hdel)
    _ = _ := by ring

end
end Wu2004MeanValue