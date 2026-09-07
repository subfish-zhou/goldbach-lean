import MathlibNt.Wu2004MeanValue.BalancedLargeAP
import MathlibNt.Wu2004MeanValue.BalancedAPWeight
import MathlibNt.Wu2004MeanValue.SourceMasks

/-!
# Actual weighted AP distribution for a balanced common profile

All constants precede the ambient integer, source, coefficient, real prime
profile, modulus cutoff and reduced residue selection. The lower bound
`r(m) ≥ x^eta` is not needed: the stronger domain `r(m) ≥ 2` suffices.
-/

namespace Wu2004MeanValue
open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.LargeSieve
noncomputable section

theorem balanced_common_profile_unit_natural (A eta : ℝ)
    (hA : 0 < A) (heta : 0 < eta) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ) (a : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ m ∈ S, (N : ℝ) ^ eta ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (1 - eta)) →
      (∀ m ∈ S, |f m| ≤ 1) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ N) →
      (∀ d ∈ Icc 1 Q, (a d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (a d)|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨b, J, hb, hJ, N₁, hunweighted⟩ :=
    balanced_large_actualAP_unweighted (2 * A + 11) eta (by linarith) heta
  obtain ⟨C, hC, hweight⟩ :=
    balanced_actualAP_weighted_log_saving_of_unweighted A 1 J (by norm_num) hJ.le
  have hlog : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  have hpower := ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hcut := PanPrincipal.eventually_log_rpow_le_rpow (2 * b + 1) (eta / 2) (by positivity)
  refine ⟨b + 1, C, by linarith, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlog, hpower, hcut, eventually_ge_atTop (max 3 N₁)]
    with N hlog hpower hcut hN
  dsimp only [Function.comp_apply] at hpower
  intro Q S f r a hQ hS hf hr ha
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  have hNexp : Real.exp 1 ≤ (N : ℝ) := by
    apply (Real.le_log_iff_exp_le hN0).mp
    linarith
  have hQroot : (Q : ℝ) ≤ Real.sqrt N :=
    hQ.trans (div_le_self (Real.sqrt_nonneg _)
      (Real.one_le_rpow (by linarith) (by linarith)))
  have hQx : (Q : ℝ) ≤ N :=
    hQroot.trans (Real.sqrt_le_self_iff.mpr (Or.inr hN1.le))
  let L : ℕ := ⌈Real.log (N : ℝ) ^ (2 * b)⌉₊
  let U : ℕ := ⌊(N : ℝ) ^ (1 - eta)⌋₊
  have hL : Real.log (N : ℝ) ^ (2 * b) ≤ (L : ℝ) := Nat.le_ceil _
  have hLsmall : (L : ℝ) < (N : ℝ) ^ eta := by
    calc
      _ ≤ Real.log (N : ℝ) ^ (2 * b + 1) := (ceil_log_source_cutoff N b hlog hb).2
      _ ≤ (N : ℝ) ^ (eta / 2) := hcut
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)
  have hU : (U : ℝ) ≤ (N : ℝ) ^ (1 - eta) :=
    Nat.floor_le (Real.rpow_nonneg hN0.le _)
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hm2 := hpower.trans (hS m hm).1
    exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hSinterval : S ⊆ Ioc L U := by
    intro m hm
    exact mem_Ioc.mpr ⟨by exact_mod_cast hLsmall.trans_le (hS m hm).1,
      Nat.le_floor (hS m hm).2⟩
  let rext : ℕ → ℝ := fun m => if m ∈ S then r m else 2
  have hrext : ∀ m ∈ Ioc L U, 2 ≤ rext m ∧ (m : ℝ) * rext m ≤ N := by
    intro m hm
    by_cases hmS : m ∈ S
    · simpa only [rext, if_pos hmS] using hr m hmS
    · rw [show rext m = 2 by simp only [rext, if_neg hmS]]
      refine ⟨le_rfl, ?_⟩
      have hmU : (m : ℝ) ≤ (N : ℝ) ^ (1 - eta) :=
        (by exact_mod_cast (mem_Ioc.mp hm).2 : (m : ℝ) ≤ U).trans hU
      calc
        _ ≤ (N : ℝ) ^ (1 - eta) * (N : ℝ) ^ eta :=
          mul_le_mul hmU hpower (by norm_num) (by positivity)
        _ = N := by rw [← Real.rpow_add hN0]; simp
  have heq (d v : ℕ) :
      actualAPSum S f r d v = actualAPSum (Ioc L U) (sourceMask S f) rext d v := by
    unfold actualAPSum
    calc
      _ = ∑ m ∈ S, if m.Coprime d then
          sourceMask S f m * ebar ((m : ℝ) * rext m) d v m else 0 := by
        apply sum_congr rfl
        intro m hm
        simp only [sourceMask, rext, if_pos hm]
      _ = _ := by
        apply sum_subset hSinterval
        intro m _ hm
        simp only [sourceMask, if_neg hm, zero_mul, ite_self]
  have hu := hunweighted N hN₁ (b + 1) (by linarith) Q L U
    (sourceMask S f) rext a hU hQ hL (abs_sourceMask_le S f 1 (by norm_num) hf) hrext ha
  have hu' : (∑ d ∈ Icc 1 Q, |actualAPSum S f r d (a d)|) ≤
      J * N / Real.log (N : ℝ) ^ (2 * A + 11) := by
    simpa only [heq] using hu
  exact hweight N Q S f r a hNexp hQx hSpos hf hr hu'

theorem balanced_common_profile_weighted_natural (A eta F : ℝ)
    (hA : 0 < A) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (Q : ℕ) (S : Finset ℕ) (f r : ℕ → ℝ) (a : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ m ∈ S, (N : ℝ) ^ eta ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (1 - eta)) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ N) →
      (∀ d ∈ Icc 1 Q, (a d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (a d)|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hbound⟩ := balanced_common_profile_unit_natural A eta hA heta
  have hF1 : 0 < F + 1 := by linarith
  refine ⟨B, (F + 1) * C, hB, by positivity, N₀, ?_⟩
  intro N hN Q S f r a hQ hS hf hr ha
  let g : ℕ → ℝ := fun m => f m / (F + 1)
  have hg : ∀ m ∈ S, |g m| ≤ 1 := by
    intro m hm
    dsimp only [g]
    rw [abs_div, abs_of_pos hF1]
    exact (div_le_one hF1).mpr (by linarith [hf m hm])
  have h := hbound N hN Q S g r a hQ hS hg hr ha
  have heq (d v : ℕ) : actualAPSum S f r d v = (F + 1) * actualAPSum S g r d v := by
    unfold actualAPSum
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    by_cases hm : m.Coprime d
    · simp only [if_pos hm, g]
      field_simp
    · simp only [if_neg hm, mul_zero]
  calc
    _ = (F + 1) * ∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S g r d (a d)| := by
      simp only [heq, abs_mul, abs_of_pos hF1, mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (F + 1) * (C * N / Real.log (N : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left h hF1.le
    _ = _ := by ring

end
end Wu2004MeanValue