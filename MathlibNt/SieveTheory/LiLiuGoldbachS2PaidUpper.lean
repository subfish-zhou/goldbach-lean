import MathlibNt.SieveTheory.LiLiuGoldbachS2RosserFactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibNt.SieveTheory.LiLiuGoldbachB10PanGeometry

open Filter
open scoped BigOperators

open Finset
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

private theorem S2Paid_tendsto_logLog_div_log :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (((fun x : ℝ => Real.log x / x) ∘ fun N : ℕ => Real.log (N : ℝ)))
    atTop (nhds 0)
  exact hreal.comp hlog

private theorem S2Paid_quarterCutoff_large_eventually
    (K : ℝ) (_hK : 0 < K) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      K ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hpow :
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop K))
  refine ⟨max 4 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

private theorem S2Paid_logRatio_bounds_eventually
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := (N : ℝ) ^ ((1 : ℝ) / 4)
      let s := Real.log Δ / Real.log Z
      0 < Real.log Z ∧ 3 / 2 ≤ s ∧ 2 / (1 + τ / 2) ≤ s ∧ s ≤ 3 := by
  have hB1 : 0 < B + 1 := by linarith
  let κ : ℝ :=
    min (τ / (4 * (B + 1) * (1 + τ / 2)))
      (min (1 / (8 * (B + 1))) (1 / (4 * (B + 1))))
  have hκ : 0 < κ := by
    dsimp [κ]
    refine lt_min ?_ ?_
    · positivity
    · positivity
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (S2Paid_tendsto_logLog_div_log.eventually (Metric.ball_mem_nhds 0 hκ))
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z := (N : ℝ) ^ ((1 : ℝ) / 4)
  let s := Real.log Δ / Real.log Z
  have hN₁' : N₁ ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hratioAbs :
      |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| < κ := by
    simpa [Real.dist_eq, abs_div] using hN₁ N hN₁'
  have hsFormula :
      s =
        2 - 4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    dsimp [s, Δ, Z]
    rw [Real.log_div
      (by positivity : (N : ℝ) ^ ((1 : ℝ) / 2) ≠ 0)
      (ne_of_gt (Real.rpow_pos_of_pos hlogNpos _)),
      Real.log_rpow hNpos, Real.log_rpow hlogNpos, Real.log_rpow hNpos]
    field_simp [hlogNpos.ne']
    ring
  have hcorr :
      4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤
        τ / (1 + τ / 2) := by
    calc
      4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        ≤ 4 * (B + 1) * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| := by
            gcongr
            exact le_abs_self _
      _ ≤ 4 * (B + 1) * κ := by
            exact mul_le_mul_of_nonneg_left hratioAbs.le (by positivity)
      _ ≤ 4 * (B + 1) * (τ / (4 * (B + 1) * (1 + τ / 2))) := by
            exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = τ / (1 + τ / 2) := by
            field_simp [hB1.ne', (show (1 + τ / 2 : ℝ) ≠ 0 by positivity)]
  have hcorrHalf :
      4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ 1 / 2 := by
    calc
      4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
        ≤ 4 * (B + 1) * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| := by
            gcongr
            exact le_abs_self _
      _ ≤ 4 * (B + 1) * κ := by
            exact mul_le_mul_of_nonneg_left hratioAbs.le (by positivity)
      _ ≤ 4 * (B + 1) * (1 / (8 * (B + 1))) := by
            exact mul_le_mul_of_nonneg_left
              ((min_le_right _ _).trans (min_le_left _ _)) (by positivity)
      _ = 1 / 2 := by
            field_simp [hB1.ne']
            ring
  have hcorrAbs :
      |4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))| < 1 := by
    calc
      |4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))|
        = (4 * (B + 1)) *
            |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| := by
              rw [abs_mul, abs_of_nonneg (by positivity)]
      _ < (4 * (B + 1)) * κ := by
            exact mul_lt_mul_of_pos_left hratioAbs (by positivity)
      _ ≤ (4 * (B + 1)) * (1 / (4 * (B + 1))) := by
            exact mul_le_mul_of_nonneg_left
              (((min_le_right _ _).trans (min_le_right _ _))) (by positivity)
      _ = 1 := by field_simp [hB1.ne']
  have hcorrLower :
      -(1 : ℝ) ≤
        4 * (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    linarith [(abs_lt.mp hcorrAbs).1]
  have hlogZ :
      Real.log Z = Real.log (N : ℝ) / 4 := by
    dsimp [Z]
    rw [Real.log_rpow hNpos]
    ring
  have hlogZpos : 0 < Real.log Z := by
    rw [hlogZ]
    positivity
  have hsloThreeHalves : 3 / 2 ≤ s := by
    rw [hsFormula]
    linarith
  have hslo : 2 / (1 + τ / 2) ≤ s := by
    rw [hsFormula]
    have haux : 2 / (1 + τ / 2) = 2 - τ / (1 + τ / 2) := by
      field_simp [(show (1 + τ / 2 : ℝ) ≠ 0 by positivity)]
      ring
    rw [haux]
    linarith
  have hshi : s ≤ 3 := by
    rw [hsFormula]
    linarith
  exact ⟨hlogZpos, hsloThreeHalves, hslo, hshi⟩

/-- The actual switched `S2` sifted count with the genuine `Z = N^(1/4)` cutoff
and `Δ = N^(1/2) / log(N)^(B+1)` has its full Rosser remainder paid into the
available logarithmic saving. -/
theorem goldbachS2SwitchedSiftedCount_upper_paid
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ) / 15 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
        let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
        let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
        let S := goldbachS2SwitchedBoundingSieve N hEven T Z
        (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
          goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
  obtain ⟨C, hC, B, hB, Nrem, hNrem4, hrem⟩ :=
    goldbachS2SwitchedRemainder_log_saving (4 : ℝ) (by norm_num)
  let ρ : ℝ := τ * Real.exp Real.eulerMascheroniConstant / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  obtain ⟨z₀, hrosser⟩ :=
    goldbachS2SwitchedSiftedCount_le_rosserFactor_add_remainderModulusSum ρ hρ
  refine ⟨C, hC, B, hB, ?_⟩
  intro ε hε hεu
  have hε1 : ε < 1 := by linarith
  obtain ⟨Ncut, hNcut2, hcut⟩ :=
    B10PanGeometry_panModulusCutoff_comparison_eventually ε B hε hε1 hB
  have hK : 0 < max 2 z₀ := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  obtain ⟨NZ, hNZ4, hZlarge⟩ :=
    S2Paid_quarterCutoff_large_eventually (max 2 z₀) hK
  obtain ⟨Ns, hNs4, hsBounds⟩ :=
    S2Paid_logRatio_bounds_eventually B τ hB hτ
  refine ⟨max 4 (max Nrem (max Ncut (max NZ Ns))), le_max_left _ _, ?_⟩
  intro N hN hEven
  let Z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let s : ℝ := Real.log Δ / Real.log Z
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let S := goldbachS2SwitchedBoundingSieve N hEven T Z
  let V := AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpack : max Nrem (max Ncut (max NZ Ns)) ≤ N :=
    (le_max_right _ _).trans hN
  have hNrem : Nrem ≤ N := (le_max_left _ _).trans hNpack
  have hNpack' : max Ncut (max NZ Ns) ≤ N := (le_max_right _ _).trans hNpack
  have hNcut : Ncut ≤ N := (le_max_left _ _).trans hNpack'
  have hNpack'' : max NZ Ns ≤ N := (le_max_right _ _).trans hNpack'
  have hNZ : NZ ≤ N := (le_max_left _ _).trans hNpack''
  have hNs : Ns ≤ N := (le_max_right _ _).trans hNpack''
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hZbig : max 2 z₀ ≤ Z := by
    simpa [Z] using hZlarge N hNZ
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hz₀ : z₀ ≤ Z := (le_max_right _ _).trans hZbig
  have hsData : 0 < Real.log Z ∧ 3 / 2 ≤ s ∧ 2 / (1 + τ / 2) ≤ s ∧ s ≤ 3 := by
    simpa [Δ, Z, s] using hsBounds N hNs
  have hΔ : 0 < Δ := by
    dsimp [Δ]
    positivity
  have hraw :
      (goldbachS2SwitchedSiftedCount N T Z : ℝ) ≤
        goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) * V +
          ∑ d ∈ (Finset.Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
            |goldbachS2SwitchedRemainder N T d| := by
    simpa [Z, Δ, s, T, S, V, goldbachS2SwitchedBoundingSieve] using
      hrosser N hEven ε Z Δ s hz₀ hZ2 hΔ rfl hsData.2.1
        (hsData.2.2.2.trans (by norm_num)) hN1 hεu
        (le_rfl : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
  have hcutN :
      panModulusCutoff N (B + 1) ≤ panModulusCutoff N B := (hcut N hNcut).2
  have hsum :
      ∑ d ∈ (Finset.Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
        |goldbachS2SwitchedRemainder N T d| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
    have hsubset :
        (Finset.Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N) ⊆
          (Finset.Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N) := by
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hdIcc, hdNcop⟩
      rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hd2⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, ?_⟩, hdNcop⟩
      calc
        d ≤ Nat.floor Δ := hd2
        _ = panModulusCutoff N (B + 1) := by rfl
        _ ≤ panModulusCutoff N B := hcutN
    calc
      ∑ d ∈ (Finset.Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
          |goldbachS2SwitchedRemainder N T d|
        ≤ ∑ d ∈ (Finset.Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
            |goldbachS2SwitchedRemainder N T d| := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
                (fun _ _ _ => abs_nonneg _)
      _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
            simpa [T] using hrem ε hε hεu N hNrem
  have hVpos : 0 < V := by
    obtain ⟨c₁, hc₁, hlower⟩ := MertensTheorem.goldbachSieveProduct_lower_bound
    have hceilZ2 : 2 ≤ Nat.ceil Z := by
      exact_mod_cast (show (2 : ℝ) ≤ Z by linarith).trans (Nat.le_ceil Z)
    have hlogceilPos : 0 < Real.log (Nat.ceil Z : ℕ) := by
      exact Real.log_pos (by exact_mod_cast (show 1 < Nat.ceil Z by omega))
    have hlow : 0 < c₁ / Real.log (Nat.ceil Z : ℕ) := by
      exact div_pos hc₁ hlogceilPos
    have hprod :
        c₁ / Real.log (Nat.ceil Z : ℕ) ≤ goldbachS2PrimeProduct N Z := by
      simpa [goldbachS2PrimeProduct] using hlower N (Nat.ceil Z) hceilZ2 hEven hN4
    have hprodPos : 0 < goldbachS2PrimeProduct N Z := lt_of_lt_of_le hlow hprod
    have hEq :
        goldbachS2PrimeProduct N Z =
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
      simpa [S, V] using goldbachS2PrimeProduct_eq_sieveProductPrimeFactors N hEven T Z
    have hVpos' : 0 < AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
      rw [← hEq]
      exact hprodPos
    simpa [V] using hVpos'
  have hfactor :
      jurkatRichertUpperLinearSieveFactor s + ρ ≤
        Real.exp Real.eulerMascheroniConstant * (1 + τ) := by
    have hsPos : 0 < s := lt_of_lt_of_le (by positivity) hsData.2.1
    have hbranch :
        jurkatRichertUpperLinearSieveFactor s =
          2 * Real.exp Real.eulerMascheroniConstant / s := by
      unfold jurkatRichertUpperLinearSieveFactor
      rw [if_pos hsData.2.2.2]
    have hdiv :
        2 / s ≤ 1 + τ / 2 := by
      have hsden : 0 < 1 + τ / 2 := by positivity
      have haux : 2 ≤ s * (1 + τ / 2) := by
        calc
          2 = (2 / (1 + τ / 2)) * (1 + τ / 2) := by
                field_simp [hsden.ne']
          _ ≤ s * (1 + τ / 2) := by
                have hmul :=
                  mul_le_mul_of_nonneg_right hsData.2.2.1 (by positivity : 0 ≤ 1 + τ / 2)
                simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      exact (div_le_iff₀ hsPos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using haux)
    have hmain :
        2 * Real.exp Real.eulerMascheroniConstant / s ≤
          Real.exp Real.eulerMascheroniConstant * (1 + τ / 2) := by
      calc
        2 * Real.exp Real.eulerMascheroniConstant / s =
            Real.exp Real.eulerMascheroniConstant * (2 / s) := by ring
        _ ≤ Real.exp Real.eulerMascheroniConstant * (1 + τ / 2) := by
            exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    rw [hbranch]
    calc
      2 * Real.exp Real.eulerMascheroniConstant / s + ρ
        ≤ Real.exp Real.eulerMascheroniConstant * (1 + τ / 2) + ρ := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmain ρ
      _ = Real.exp Real.eulerMascheroniConstant * (1 + τ) := by
            dsimp [ρ]
            ring
  have hmainTerm :
      goldbachS2SwitchedMainMass N T *
          (jurkatRichertUpperLinearSieveFactor s + ρ) * V ≤
        goldbachS2SwitchedMainMass N T *
          (Real.exp Real.eulerMascheroniConstant * (1 + τ)) * V := by
    have hmass :
        goldbachS2SwitchedMainMass N T * (jurkatRichertUpperLinearSieveFactor s + ρ) ≤
          goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + τ)) :=
      mul_le_mul_of_nonneg_left hfactor (goldbachS2SwitchedMainMass_nonneg N T)
    simpa [V, mul_assoc] using mul_le_mul_of_nonneg_right hmass hVpos.le
  calc
    (goldbachS2SwitchedSiftedCount N T Z : ℝ)
      ≤ goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) * V +
          ∑ d ∈ (Finset.Icc 1 (Nat.floor Δ)).filter (fun d => Nat.Coprime d N),
            |goldbachS2SwitchedRemainder N T d| := hraw
    _ ≤ goldbachS2SwitchedMainMass N T *
            (jurkatRichertUpperLinearSieveFactor s + ρ) * V +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
            exact add_le_add le_rfl hsum
    _ ≤ goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + τ)) * V +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hmainTerm (C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ))
    _ = goldbachS2SwitchedMainMass N T *
            (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
          C * (N : ℝ) / Real.log (N : ℝ) ^ (4 : ℝ) := by
            rfl

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig