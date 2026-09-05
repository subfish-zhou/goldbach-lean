import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCofactorReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowEndpoint
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHighAggregate

noncomputable section
open Finset Filter
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

namespace AnalyticNumberTheory.LargeSieve.PanLow
/-- Exact partition after removing the principal conductor-one character. -/
theorem nonprincipalLow_eq_low_add_high (g d : ℕ → ℂ) (N A₁ A₂ D₁ D : ℕ)
    (h1 : 1 ≤ D₁) (hD : D₁ ≤ D) :
    nonprincipalLow g d N A₁ A₂ D =
      nonprincipalLow g d N A₁ A₂ D₁ + panIymHigh g d N A₁ A₂ D₁ D := by
  classical
  have hs : Icc 1 D = Icc 1 D₁ ∪ Ioc D₁ D := by
    ext q
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 D₁) (Ioc D₁ D) := by
    apply disjoint_left.mpr
    intro q hq hq'
    simp only [mem_Icc, mem_Ioc] at hq hq'
    omega
  unfold nonprincipalLow panIymHigh
  rw [hs, sum_union hd]
  congr 1
  apply sum_congr rfl
  intro q hq
  rw [nonprincipalPrimitiveCharacters_eq_univ (by have := (mem_Ioc.mp hq).1; omega)]
end AnalyticNumberTheory.LargeSieve.PanLow

namespace MathlibNt.SieveTheory.LiuWeight
/-- Both cofactor screens are exactly the canonical high-source screens. -/
theorem liuPanPrimitiveCofactorLedger_eq_source (N A₁ A₂ D m : ℕ) (f : ℕ → ℝ) :
    liuPanPrimitiveCofactorLedger N A₁ A₂ D m f =
      PanLow.nonprincipalLow (panSourceG (fun a => (f a : ℂ)) m) (panSourceD m)
        N A₁ A₂ D := by
  unfold liuPanPrimitiveCofactorLedger
  change PanLow.nonprincipalLow _ (fun p => if p.Prime ∧ p.Coprime m then 1 else 0) _ _ _ _ =
    PanLow.nonprincipalLow _ (fun p => if p.Coprime m ∧ p.Prime then 1 else 0) _ _ _ _
  simp only [and_comm]
  rfl

/-- Elementary eventual payment, used only for powers of log versus powers of N. -/
theorem eventually_pan_log_rpow_le_rpow (t r : ℝ) (hr : 0 < r) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ t ≤ (N : ℝ) ^ r := by
  have h := (isLittleO_log_rpow_rpow_atTop t hr).bound (show (0 : ℝ) < 1 by norm_num)
  have h' : ∀ᶠ x : ℝ in atTop, Real.log x ^ t ≤ x ^ r := by
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _), one_mul] using hx
  exact tendsto_natCast_atTop_atTop.eventually h'

theorem panModulusCutoff_eq_upper (N : ℕ) (B : ℝ) :
    panModulusCutoff N B = ⌊upperConductor N B⌋₊ := by
  simp only [panModulusCutoff, upperConductor, lowConductor, Real.sqrt_eq_rpow]

theorem eventually_pan_conductor_bounds (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧ 1 ≤ ⌊lowConductor N B⌋₊ ∧
      ⌊lowConductor N B⌋₊ ≤ panModulusCutoff N B ∧
      (panModulusCutoff N B : ℝ) ≤ Real.sqrt N ∧ panModulusCutoff N B ≤ N := by
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hl, eventually_pan_log_rpow_le_rpow (2 * B) (1 / 2) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with N hlog hp hN
  change 1 ≤ Real.log (N : ℝ) at hlog
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hd : 1 ≤ lowConductor N B := Real.one_le_rpow hlog hB
  have hdp : 0 < lowConductor N B := by linarith
  have hsq : lowConductor N B * lowConductor N B ≤ Real.sqrt N := by
    rw [lowConductor, ← Real.rpow_add hlogpos, ← two_mul, Real.sqrt_eq_rpow]
    exact hp
  have horder : lowConductor N B ≤ upperConductor N B := (le_div_iff₀ hdp).mpr hsq
  have hupper : upperConductor N B ≤ Real.sqrt N := div_le_self (Real.sqrt_nonneg _) hd
  have hfloor : (panModulusCutoff N B : ℝ) ≤ Real.sqrt N := by
    rw [panModulusCutoff_eq_upper]
    exact (Nat.floor_le (by unfold upperConductor; positivity)).trans hupper
  refine ⟨hlog, Nat.le_floor (by simpa using hd), ?_, hfloor, ?_⟩
  · rw [panModulusCutoff_eq_upper]
    exact Nat.floor_mono horder
  · have hn : Real.sqrt (N : ℝ) ≤ N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_self_of_one_le (by exact_mod_cast hN) (by norm_num)
    exact_mod_cast hfloor.trans hn

/-- Full primitive ledger, uniformly in the cofactor. No high or low estimate
is a theorem parameter. The exponent B is chosen before N and m. -/
theorem liuPanPrimitiveCofactorLedger_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ m ∈ Icc 1 (panModulusCutoff N B),
        liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N B)
          (liuPanSourceIntervalUpper N) (panModulusCutoff N B) m
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
            C * N / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, Np, hp⟩ := nonprincipal_liu_source_log_saving U hU
  have hB : 0 ≤ U + 6 := by linarith
  have he : ∀ᶠ N : ℕ in atTop,
      ∀ m ∈ Icc 1 (panModulusCutoff N (U + 6)),
        liuPanPrimitiveCofactorLedger N (liuPanSourceIntervalLower N (U + 6))
          (liuPanSourceIntervalUpper N) (panModulusCutoff N (U + 6)) m
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
            C * N / Real.log (N : ℝ) ^ U := by
    filter_upwards [eventually_pan_conductor_bounds (U + 6) hB,
      eventually_ge_atTop Np] with N hb hNp m hm
    obtain ⟨_, hD1, hD, hDN, _⟩ := hb
    have hmN : (m : ℝ) ≤ Real.sqrt N :=
      (by exact_mod_cast (mem_Icc.mp hm).2 : (m : ℝ) ≤ panModulusCutoff N (U + 6)).trans hDN
    have h := hp N hNp m (mem_Icc.mp hm).1 hmN
    rw [← panModulusCutoff_eq_upper] at h
    rw [liuPanPrimitiveCofactorLedger_eq_source,
      PanLow.nonprincipalLow_eq_low_add_high _ _ _ _ _ _ _ hD1 hD]
    exact h
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  exact ⟨C, hC, U + 6, hB, N₀, hN₀⟩
end MathlibNt.SieveTheory.LiuWeight