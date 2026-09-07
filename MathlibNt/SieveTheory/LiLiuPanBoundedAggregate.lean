import MathlibNt.SieveTheory.LiLiuPanBoundedPrincipal
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPayment
import MathlibNt.SieveTheory.LiuPanUnweightedUnconditional

noncomputable section

open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

namespace MathlibNt.SieveTheory.LiuWeight

private theorem boundedAggregate_primitiveCofactorLedger_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ A₁ A₂ : ℕ, ∀ f : ℕ → ℝ,
        (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
        (∀ a, |f a| ≤ 1) →
        ∀ m ∈ Icc 1 (panModulusCutoff N B),
          liuPanPrimitiveCofactorLedger N A₁ A₂ (panModulusCutoff N B) m f ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨CL, hCL, NL, hlow⟩ := PanLow.nonprincipalLow_endpoint U (U + 6) hU (by linarith)
  obtain ⟨CH, hCH, hhighBase⟩ := chosen_high_source_log_saving
  obtain ⟨NH, hhigh⟩ := hhighBase (U + 6) (1 / 3) (by linarith) (by norm_num)
  have hB : 0 ≤ U + 6 := by linarith
  refine ⟨CL + CH + 6984, by positivity, U + 6, hB, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_pan_conductor_bounds (U + 6) hB,
    eventually_ge_atTop NL, eventually_ge_atTop NH, eventually_ge_atTop (2 : ℕ),
    eventually_high_remainder_le U] with N hb hNL hNH hN hrem
  intro A₁ A₂ f hA hA₁ hf m hm
  obtain ⟨_, hD1, hD, hDroot, _⟩ := hb
  have hLp : 0 < Real.log (N : ℝ) := by
    linarith
  have hmN : (m : ℝ) ≤ Real.sqrt N :=
    (by exact_mod_cast (mem_Icc.mp hm).2 : (m : ℝ) ≤ panModulusCutoff N (U + 6)).trans hDroot
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hAN : A₂ ≤ N := by
    exact_mod_cast hA.trans
      (Real.rpow_le_self_of_one_le hN1 (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hfC : ∀ a, ‖(f a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf a
  have hlow' := hlow N hNL m A₁ A₂ ⌊lowConductor N (U + 6)⌋₊
    (panSourceG (fun a => (f a : ℂ)) m)
    (mem_Icc.mp hm).1 hmN hA
    (Nat.floor_le (Real.rpow_nonneg hLp.le _)) (by
      intro a ha
      exact panSourceG_norm_le (fun a => (f a : ℂ)) hfC m a)
  have hlow'' :
      PanLow.nonprincipalLow (panSourceG (fun a => (f a : ℂ)) m) (panSourceD m)
        N A₁ A₂ ⌊lowConductor N (U + 6)⌋₊ ≤
          CL * N / Real.log (N : ℝ) ^ U := by
    have hDfun : panSourceD m =
        (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
      funext n
      simp [panSourceD, and_comm]
    rw [hDfun]
    exact hlow'
  have hhigh' := hhigh N hNH m A₁ A₂ (fun a => (f a : ℂ)) hAN
    (by convert hA using 1; norm_num) hA₁ hfC
  have hmain : CH * (N : ℝ) * Real.log (N : ℝ) ^ (6 - (U + 6)) =
      CH * N / Real.log (N : ℝ) ^ U := by
    rw [show 6 - (U + 6) = -U by ring, Real.rpow_neg hLp.le, div_eq_mul_inv]
  have hhigh'' :
      panIymHigh (panSourceG (fun a => (f a : ℂ)) m) (panSourceD m)
        N A₁ A₂ ⌊lowConductor N (U + 6)⌋₊ (panModulusCutoff N (U + 6)) ≤
          CH * N / Real.log (N : ℝ) ^ U +
            6984 * Real.log (N : ℝ) ^ 2 / N := by
    rw [panModulusCutoff_eq_upper, ← hmain]
    exact hhigh'
  rw [liuPanPrimitiveCofactorLedger_eq_source,
    PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD]
  calc
    _ ≤ CL * N / Real.log (N : ℝ) ^ U +
        (CH * N / Real.log (N : ℝ) ^ U +
          6984 * Real.log (N : ℝ) ^ 2 / N) := by
      exact add_le_add hlow'' hhigh''
    _ ≤ CL * N / Real.log (N : ℝ) ^ U +
        (CH * N / Real.log (N : ℝ) ^ U + 6984 * N / Real.log (N : ℝ) ^ U) := by
      exact add_le_add le_rfl (add_le_add le_rfl hrem)
    _ = _ := by
      ring

/-- Actual reduced-residue Pan aggregate for any bounded real coefficient.
The cutoff exponent is chosen before `N`, the window, and the coefficient. -/
theorem liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ A₁ A₂ : ℕ, ∀ f : ℕ → ℝ,
        (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
        (∀ a, |f a| ≤ 1) →
        ∑ d ∈ Icc 1 (panModulusCutoff N B),
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d f ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨K, hK, B, hB, Nk, hk⟩ :=
    boundedAggregate_primitiveCofactorLedger_log_saving (U + 2) (by linarith)
  obtain ⟨P, hP, Np, hp⟩ :=
    liuMainPanCoprimeIntervalMaxL_le_actualCharacterMass_with_paid_principal
      (U + 2) (by linarith)
  have he : ∀ᶠ N : ℕ in atTop,
      ∀ A₁ A₂ : ℕ, ∀ f : ℕ → ℝ,
        (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
        Real.log (N : ℝ) ^ (2 * B) ≤ A₁ →
        (∀ a, |f a| ≤ 1) →
        ∑ d ∈ Icc 1 (panModulusCutoff N B),
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d f ≤
          (4 * (K + P)) * (N : ℝ) / Real.log (N : ℝ) ^ U := by
    filter_upwards [eventually_pan_conductor_bounds B hB,
      eventually_ge_atTop Nk, eventually_ge_atTop Np] with N hb hNk hNp
    intro A₁ A₂ f hA hA₁ hf
    obtain ⟨hlog, _, _, hDroot, hDN⟩ := hb
    let D := panModulusCutoff N B
    let M := K * N / Real.log (N : ℝ) ^ (U + 2)
    let T := P * N / Real.log (N : ℝ) ^ (U + 2)
    have hM : 0 ≤ M := by
      dsimp [M]
      positivity
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hmass := liuPanActualNonprincipal_sum_le_log_sq N A₁ A₂ D f M hM hDN
      (hk N hNk A₁ A₂ f hA hA₁ hf)
    have hprincipal : T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ ≤
        T * (1 + Real.log (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hT
    have hfIoc : ∀ a ∈ Ioc A₁ A₂, |f a| ≤ 1 := by
      intro a _
      exact hf a
    calc
      _ ≤ ∑ q ∈ Icc 1 D,
          (liuPanActualNonprincipalMass N A₁ A₂ q f + T) / q.totient := by
        apply sum_le_sum
        intro q hq
        exact hp N hNp q A₁ A₂ f (mem_Icc.mp hq).1
          ((by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ D).trans hDroot) hA hfIoc
      _ = (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ * liuPanActualNonprincipalMass N A₁ A₂ q f) +
          T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ := by
        simp only [add_div, sum_add_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ M * (1 + Real.log (N : ℝ)) ^ 2 + T * (1 + Real.log (N : ℝ)) ^ 2 :=
        add_le_add hmass hprincipal
      _ = ((K + P) * N / Real.log (N : ℝ) ^ (U + 2)) * (1 + Real.log (N : ℝ)) ^ 2 := by
        dsimp [M, T]
        ring
      _ ≤ _ := pan_log_sq_payment N U (K + P) (by positivity) hlog
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  exact ⟨4 * (K + P), by positivity, B, hB, N₀, hN₀⟩

end MathlibNt.SieveTheory.LiuWeight