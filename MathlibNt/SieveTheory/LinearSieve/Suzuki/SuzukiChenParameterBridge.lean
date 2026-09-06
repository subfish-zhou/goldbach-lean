import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

/-!
# Chen--Suzuki floor/ceiling coordinate bridge

This module contains the parameter arithmetic only.  It is deliberately independent
of the sieve implementation, so the eventual estimates do not rely on a finite scan.
-/

open scoped BigOperators
open Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne


/-- Chen's natural level `D = floor(N^(1/2-epsilon))+1`. -/
noncomputable def chenLevel (N : ℕ) (ε : ℝ) : ℕ :=
  ⌊(N : ℝ) ^ (1 / 2 - ε)⌋₊ + 1

/-- Chen's upper Suzuki coordinate. -/
def chenS (ε : ℝ) : ℝ := 5 - 10 * ε

/-- The natural cutoff associated to Chen's upper Suzuki coordinate. -/
noncomputable def chenZ (N : ℕ) (ε : ℝ) : ℕ :=
  ⌈(chenLevel N ε : ℝ) ^ (1 / chenS ε)⌉₊

/-- Adding one after taking the natural floor strictly dominates the original
real number. -/
theorem lt_cast_floor_add_one (x : ℝ) :
    x < (⌊x⌋₊ + 1 : ℕ) := by
  exact_mod_cast Nat.lt_floor_add_one x

/-- The identity behind Chen's exponent choice:
`(1/2-epsilon)/(5-10 epsilon)=1/10`. -/
theorem chen_exponent_div_s {ε : ℝ} (hε : ε < 1 / 2) :
    (1 / 2 - ε) * (1 / chenS ε) = 1 / 10 := by
  have ha : 1 / 2 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  have hs_eq : chenS ε = 10 * (1 / 2 - ε) := by
    unfold chenS
    ring
  rw [hs_eq]
  have hden : 1 - 2 * ε ≠ 0 := by linarith
  field_simp [ha, hden]

/-- Exact, scan-free floor/rpow/ceiling bridge.  Every natural below Chen's
`N^(1/10)` cutoff is strictly below the Suzuki natural cutoff `z`. -/
theorem chen_lt_tenth_rpow_imp_lt_chenZ
    {N p : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (hp : (p : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ)) :
    p < chenZ N ε := by
  let a : ℝ := 1 / 2 - ε
  let s : ℝ := chenS ε
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNnonneg : 0 ≤ (N : ℝ) := hNpos.le
  have hs : 0 < s := by
    dsimp [s, chenS]
    linarith
  have hfloor : (N : ℝ) ^ a < (chenLevel N ε : ℝ) := by
    simpa [chenLevel, a] using lt_cast_floor_add_one ((N : ℝ) ^ a)
  have hpow : ((N : ℝ) ^ a) ^ (1 / s) <
      (chenLevel N ε : ℝ) ^ (1 / s) :=
    Real.rpow_lt_rpow (Real.rpow_nonneg hNnonneg _) hfloor (by positivity)
  have hid : ((N : ℝ) ^ a) ^ (1 / s) = (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_mul hNnonneg]
    congr 1
    dsimp [a, s]
    exact chen_exponent_div_s (by linarith)
  rw [hid] at hpow
  rw [chenZ, Nat.lt_ceil]
  exact hp.trans hpow

/-- The same bridge packaged as membership in an arbitrary supported carrier.
This is the precise shape needed when `P` is the production prime-factor carrier. -/
theorem mem_filter_lt_chenZ_of_lt_tenth_rpow
    {N p : ℕ} {ε : ℝ} (P : Finset ℕ)
    (hN : 1 ≤ N) (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (hpP : p ∈ P) (hp : (p : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ)) :
    p ∈ P.filter (fun q => q < chenZ N ε) := by
  exact mem_filter.mpr ⟨hpP, chen_lt_tenth_rpow_imp_lt_chenZ hN hε0 hε hp⟩

/-- A convenient explicit threshold for the fixed Claim-14.5 choice `d=16`. -/
noncomputable def chenSigmaThreshold : ℝ :=
  Real.exp (max ((5 : ℝ) ^ (16 : ℕ)) (Real.exp 1))

/-- Above the explicit threshold, the fixed Claim-14.5 coordinate `d=16`
dominates every Chen `s=5-10 epsilon` with nonnegative epsilon. -/
theorem chenS_le_sourceSigma_sixteen
    {D ε : ℝ} (hε0 : 0 ≤ ε) (hD : chenSigmaThreshold ≤ D) :
    chenS ε ≤ sourceSigma D 16 := by
  let B : ℝ := max ((5 : ℝ) ^ (16 : ℕ)) (Real.exp 1)
  have hBpos : 0 < B := (Real.exp_pos 1).trans_le (le_max_right _ _)
  have hDpos : 0 < D := (Real.exp_pos B).trans_le (by simpa [chenSigmaThreshold, B] using hD)
  have hlogD : B ≤ Real.log D := by
    apply (Real.le_log_iff_exp_le hDpos).2
    simpa [chenSigmaThreshold, B] using hD
  have hlogDpos : 0 < Real.log D := hBpos.trans_le hlogD
  have hfivepow : (5 : ℝ) ^ (16 : ℕ) ≤ Real.log D :=
    (le_max_left _ _).trans hlogD
  have hroot : (5 : ℝ) ≤ (Real.log D) ^ (1 / (16 : ℝ)) := by
    rw [show (1 / (16 : ℝ)) = (16 : ℝ)⁻¹ by ring]
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num) hlogDpos.le (by norm_num)]
    simpa [Real.rpow_natCast] using hfivepow
  have hDle : D ≤ 27 * D := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 27) hDpos.le
  have hlogmono : Real.log D ≤ Real.log (27 * D) :=
    Real.strictMonoOn_log.monotoneOn hDpos (mul_pos (by norm_num) hDpos) hDle
  have hexp_le_inner : Real.exp 1 ≤ Real.log (27 * D) :=
    (le_max_right _ _).trans (hlogD.trans hlogmono)
  have hloglog : 1 ≤ Real.log (Real.log (27 * D)) := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hexp_le_inner)]
    exact hexp_le_inner
  have hs5 : chenS ε ≤ 5 := by unfold chenS; linarith
  unfold sourceSigma
  have hroot0 : 0 ≤ (Real.log D) ^ (1 / (16 : ℝ)) :=
    Real.rpow_nonneg hlogDpos.le _
  apply hs5.trans (hroot.trans _)
  simpa only [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hloglog hroot0

/-- Eventual Chen-to-Suzuki coordinate gate, with a concrete natural threshold
and the source-valid fixed choice `d=16` (for example `16 > 7/(1-1/2)`). -/
theorem exists_chen_floor_level_sourceSigma_gate :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 10 →
      chenS ε ≤ sourceSigma (chenLevel N ε : ℝ) 16 := by
  let B : ℝ := max ((5 : ℝ) ^ (16 : ℕ)) (Real.exp 1)
  let X : ℝ := Real.exp ((5 / 2 : ℝ) * B)
  refine ⟨⌈X⌉₊, ?_⟩
  intro N hN ε hε0 hε
  have hXN : X ≤ (N : ℝ) := (Nat.ceil_le.mp hN)
  have hXpos : 0 < X := Real.exp_pos _
  have hNpos : 0 < (N : ℝ) := hXpos.trans_le hXN
  have hlogN : (5 / 2 : ℝ) * B ≤ Real.log (N : ℝ) := by
    exact (Real.le_log_iff_exp_le hNpos).2 hXN
  let a : ℝ := 1 / 2 - ε
  have ha : 2 / 5 ≤ a := by dsimp [a]; linarith
  have hN1 : 1 ≤ (N : ℝ) := by
    have hBpos : 0 < B := (Real.exp_pos 1).trans_le (le_max_right _ _)
    have : 0 < (5 / 2 : ℝ) * B := mul_pos (by norm_num) hBpos
    exact (Real.one_lt_exp_iff.mpr this).le.trans hXN
  have hpowmono : (N : ℝ) ^ (2 / 5 : ℝ) ≤ (N : ℝ) ^ a :=
    Real.rpow_le_rpow_of_exponent_le hN1 ha
  have hbase : Real.exp B ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    rw [Real.rpow_def_of_pos hNpos]
    rw [Real.exp_le_exp]
    nlinarith [hlogN]
  have hfloor : (N : ℝ) ^ a < (chenLevel N ε : ℝ) := by
    simpa [chenLevel, a] using lt_cast_floor_add_one ((N : ℝ) ^ a)
  apply chenS_le_sourceSigma_sixteen hε0
  have : Real.exp B < (chenLevel N ε : ℝ) := hbase.trans_lt (hpowmono.trans_lt hfloor)
  simpa [chenSigmaThreshold, B] using this.le

/-- The fixed value used above satisfies Claim 14.5's source inequality at
`Delta=1/2`. -/
theorem sixteen_claim14_5_admissible :
    7 / (1 - (1 / 2 : ℝ)) < (16 : ℝ) := by norm_num


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
