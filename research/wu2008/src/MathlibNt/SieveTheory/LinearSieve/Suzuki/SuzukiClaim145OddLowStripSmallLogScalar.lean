import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowS

open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The uniform scalar obligation in the source-small odd strip omitted by
Suzuki's printed Case partition.  The multiplicative constant is chosen after
`C1` and the source parameters, but before `K` and `D`; unlike the intermediate
eventual estimate, this statement covers every `K ≥ 2`. -/
def Claim145OddLowStripSmallLogScalarUniform
    (d Δ C1 Θ : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ (K : ℝ) (D : ℕ), 2 ≤ K → 2 ≤ D →
      Real.log (D : ℝ) ≤ C1 * K ^ Θ →
      let R := (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)
      2 * R ^ 2 * Real.log (D : ℝ) * sourceSigma (D : ℝ) d *
          (Real.log (D : ℝ)) ^ Δ ≤
        A * Real.exp (Real.sqrt K)

private theorem oddLowStrip_eventually_two_mul_localRatio_le_exp_half
    {C1 Θ : ℝ} (hC1 : 0 ≤ C1) (hΘ : 0 ≤ Θ) :
    ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D : ℝ, 2 ≤ D →
      Real.log D ≤ C1 * K ^ Θ →
      2 * ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) ≤
        Real.exp (Real.sqrt K / 2) := by
  let p : ℝ := Θ + 1
  have hp : 0 < p := by dsimp [p]; linarith
  let B0 : ℝ := 2 * C1 / Real.log 2 * (1 + 1 / Real.log 2)
  let B : ℝ := max 1 B0
  have hB : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hsmall := (isLittleO_log_rpow_rpow_atTop 1
    (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / (4 * p) by positivity)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      Real.tendsto_sqrt_atTop.eventually_ge_atTop (4 * Real.log B),
      hsmall] with K hK2 hlogK hrootB hsmallK
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hpLog : p * Real.log K ≤ Real.sqrt K / 4 := by
    change |Real.log K ^ (1 : ℝ)| ≤
      1 / (4 * p) * |K ^ (1 / 2 : ℝ)| at hsmallK
    rw [Real.rpow_one, abs_of_nonneg hlogK0,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hsmallK
    calc
      p * Real.log K ≤ p * (1 / (4 * p) * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hsmallK hp.le
      _ = Real.sqrt K / 4 := by field_simp
  have hlogB : Real.log B ≤ Real.sqrt K / 4 := by nlinarith
  refine ⟨hK2, ?_⟩
  intro D hD hsource
  have hD1 : 1 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hpowK : 0 < K ^ Θ := Real.rpow_pos_of_pos hK0 Θ
  have hlin : 1 + K / Real.log 2 ≤ K * (1 + 1 / Real.log 2) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    field_simp
    nlinarith
  have hraw :
      2 * ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) ≤
        B * K ^ p := by
    have hnonneg : 0 ≤ 1 + K / Real.log 2 := by positivity
    calc
      2 * ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) ≤
          2 * ((C1 * K ^ Θ / Real.log 2) * (1 + K / Real.log 2)) := by
            gcongr
      _ ≤ 2 * ((C1 * K ^ Θ / Real.log 2) *
          (K * (1 + 1 / Real.log 2))) := by gcongr
      _ = B0 * K ^ p := by
        dsimp [B0, p]
        rw [Real.rpow_add hK0, Real.rpow_one]
        ring
      _ ≤ B * K ^ p := by
        gcongr
        exact le_max_right _ _
  have hexp : B * K ^ p ≤ Real.exp (Real.sqrt K / 2) := by
    rw [Real.rpow_def_of_pos hK0]
    calc
      B * Real.exp (Real.log K * p) =
          Real.exp (Real.log B + p * Real.log K) := by
            rw [Real.exp_add, Real.exp_log hBpos]
            ring
      _ ≤ Real.exp (Real.sqrt K / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
  exact hraw.trans hexp

private theorem oddLowStrip_eventually_two_le_sqrt_div_log :
    ∀ᶠ K : ℝ in atTop,
      2 ≤ K ∧ 2 ≤ Real.sqrt K / Real.log K := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop 1
    (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1, hsmall]
      with K hK2 hlogK hsmallK
  have hK0 : 0 < K := by linarith
  have hlogK0 : 0 < Real.log K := zero_lt_one.trans_le hlogK
  have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hlogle : Real.log K ≤ Real.sqrt K / 2 := by
    change |Real.log K ^ (1 : ℝ)| ≤
      (1 / 2 : ℝ) * |K ^ (1 / 2 : ℝ)| at hsmallK
    rw [Real.rpow_one, abs_of_nonneg hlogK0.le,
      abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hsmallK
    linarith
  refine ⟨hK2, ?_⟩
  apply (le_div_iff₀ hlogK0).2
  linarith

/-- Uniform closure of the pure scalar obligation.  In fact the source
hypotheses permit the multiplicative constant `A = 1`; no finite range in `D`
is scanned. -/
theorem claim145_odd_lowStrip_smallLog_scalarUniform_one
    {d Δ C1 Θ : ℝ}
    (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧
      ∀ (K : ℝ) (D : ℕ), K0 ≤ K → 2 ≤ D →
        Real.log (D : ℝ) ≤ C1 * K ^ Θ →
        let R := (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)
        2 * R ^ 2 * Real.log (D : ℝ) * sourceSigma (D : ℝ) d *
            (Real.log (D : ℝ)) ^ Δ ≤ Real.exp (Real.sqrt K) := by
  have hpre := claim145_caseA_lowS_146_prefactor_eventually
    hC1 hΘ hd hsource hΔ0 hΔ1 (show (0 : ℝ) ≤ 0 by norm_num)
  have hratio := oddLowStrip_eventually_two_mul_localRatio_le_exp_half hC1 hΘ.le
  have hall : ∀ᶠ K : ℝ in atTop,
      (2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 2 ≤ s →
        s ≤ Real.sqrt K / Real.log K → Real.log D ≤ C1 * K ^ Θ →
        (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          (Real.log D) ^ (1 + Δ) * sourceSigma D d * Real.exp (0 * s) ≤
            Real.exp (Real.sqrt K / 2)) ∧
      (2 ≤ K ∧ ∀ D : ℝ, 2 ≤ D → Real.log D ≤ C1 * K ^ Θ →
        2 * ((Real.log D / Real.log 2) * (1 + K / Real.log 2)) ≤
          Real.exp (Real.sqrt K / 2)) ∧
      (2 ≤ K ∧ 2 ≤ Real.sqrt K / Real.log K) :=
    hpre.and (hratio.and oddLowStrip_eventually_two_le_sqrt_div_log)
  rcases eventually_atTop.1 hall with ⟨K0, hK0⟩
  refine ⟨K0, ?_, ?_⟩
  · exact (hK0 K0 le_rfl).1.1
  · intro K D hKK hD hsmall
    let L : ℝ := Real.log (D : ℝ)
    let R : ℝ := (L / Real.log 2) * (1 + K / Real.log 2)
    have hk := hK0 K hKK
    have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hpreK := hk.1.2 (D : ℝ) 2 hDreal (by norm_num)
      hk.2.2.2 hsmall
    have hratioK := hk.2.1.2 (D : ℝ) hDreal hsmall
    have hL : 0 < L := by
      dsimp [L]
      exact Real.log_pos (by exact_mod_cast (show 1 < D by omega))
    have hR0 : 0 ≤ R := by
      dsimp [R]
      have hKnonneg : 0 ≤ K := by linarith [hk.1.1]
      exact mul_nonneg (div_nonneg hL.le (Real.log_pos (by norm_num)).le)
        (by positivity)
    have hP0 : 0 ≤ R * L ^ (1 + Δ) * sourceSigma (D : ℝ) d := by
      exact mul_nonneg (mul_nonneg hR0
        (Real.rpow_nonneg hL.le _)) (sourceSigma_pos_of_nat_two_le hD).le
    have hmul := mul_le_mul hratioK (by simpa [L, R] using hpreK)
      hP0 (Real.exp_pos _).le
    have hpow : L ^ (1 + Δ) = L * L ^ Δ := by
      rw [Real.rpow_add hL]
      simp
    dsimp only
    rw [show Real.exp (Real.sqrt K / 2) * Real.exp (Real.sqrt K / 2) =
      Real.exp (Real.sqrt K) by rw [← Real.exp_add]; congr 1; ring] at hmul
    rw [hpow] at hmul
    dsimp [R, L] at hmul ⊢
    nlinarith

/-- All-`K` scalar closure.  Above the eventual threshold the coefficient-one
estimate applies.  Below it, monotonicity in `K` moves the left side to the
threshold, while the explicit coefficient `exp (sqrt K0)` absorbs that single
analytic endpoint.  Thus no finite scan of the bounded interval is used. -/
theorem claim145_odd_lowStrip_smallLog_scalarUniform
    {d Δ C1 Θ : ℝ}
    (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    Claim145OddLowStripSmallLogScalarUniform d Δ C1 Θ := by
  rcases claim145_odd_lowStrip_smallLog_scalarUniform_one
      hC1 hΘ hd hsource hΔ0 hΔ1 with ⟨K0, hK0, hscalar⟩
  let A : ℝ := Real.exp (Real.sqrt K0)
  refine ⟨A, (Real.exp_pos _).le, ?_⟩
  intro K D hK hD hsmall
  by_cases hlarge : K0 ≤ K
  · have hs := hscalar K D hlarge hD hsmall
    have hA1 : 1 ≤ A := by
      dsimp [A]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (Real.sqrt_nonneg K0)
    exact hs.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hA1 (Real.exp_pos (Real.sqrt K)).le)
  · have hKK0 : K ≤ K0 := le_of_not_ge hlarge
    have hpow : K ^ Θ ≤ K0 ^ Θ :=
      Real.rpow_le_rpow (by linarith) hKK0 hΘ.le
    have hsmall0 : Real.log (D : ℝ) ≤ C1 * K0 ^ Θ :=
      hsmall.trans (mul_le_mul_of_nonneg_left hpow hC1)
    have hs0 := hscalar K0 D le_rfl hD hsmall0
    let L : ℝ := Real.log (D : ℝ)
    let R : ℝ := (L / Real.log 2) * (1 + K / Real.log 2)
    let R0 : ℝ := (L / Real.log 2) * (1 + K0 / Real.log 2)
    have hL : 0 < L := by
      dsimp [L]
      exact Real.log_pos (by exact_mod_cast (show 1 < D by omega))
    have hR : R ≤ R0 := by
      dsimp [R, R0]
      gcongr
    have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
    have hRsq : R ^ 2 ≤ R0 ^ 2 := by
      have hR0nonneg : 0 ≤ R0 := hRnonneg.trans hR
      nlinarith
    have hleft :
        2 * R ^ 2 * L * sourceSigma (D : ℝ) d * L ^ Δ ≤
          2 * R0 ^ 2 * L * sourceSigma (D : ℝ) d * L ^ Δ := by
      gcongr
      exact (sourceSigma_pos_of_nat_two_le hD).le
    have hs0' :
        2 * R0 ^ 2 * L * sourceSigma (D : ℝ) d * L ^ Δ ≤
          Real.exp (Real.sqrt K0) := by
      simpa [R0, L] using hs0
    have hexpK : 1 ≤ Real.exp (Real.sqrt K) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (Real.sqrt_nonneg K)
    calc
      2 * R ^ 2 * L * sourceSigma (D : ℝ) d * L ^ Δ ≤
          2 * R0 ^ 2 * L * sourceSigma (D : ℝ) d * L ^ Δ := hleft
      _ ≤ Real.exp (Real.sqrt K0) := hs0'
      _ = A * 1 := by simp [A]
      _ ≤ A * Real.exp (Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hexpK (Real.exp_pos _).le


end MathlibNt.SieveTheory
