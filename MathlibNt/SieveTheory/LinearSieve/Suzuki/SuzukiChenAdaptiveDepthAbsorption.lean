import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenParameterBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open Set Filter Topology

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- At the legal source choice `Δ = 1/2`, the Suzuki error is absorbed uniformly
in the recursion depth.  This uses the literal `errorEnvelope`: depth only chooses
one of the two Section-13 hat layers. -/
theorem eventually_all_depth_suzuki_error_half
    (H : Section13HatLayers) {β C K s : ℝ}
    (hH : Section13HatContract H β) (hC : 0 ≤ C) (hs : 0 < s)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ D : ℝ in atTop, ∀ depth : ℕ,
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H depth D 16 s *
          (Real.log D) ^ (-(1 / 2 : ℝ)) ∧
      C * Real.exp (Real.sqrt K) * errorEnvelope H depth D 16 s *
          (Real.log D) ^ (-(1 / 2 : ℝ)) < ρ := by
  have hlog : Tendsto (fun D : ℝ => Real.log D) atTop atTop := Real.tendsto_log_atTop
  have hratio : Tendsto (fun D : ℝ => s ^ (16 : ℝ) / Real.log D) atTop (𝓝 0) :=
    hlog.const_div_atTop (s ^ (16 : ℝ))
  have hbase : Tendsto (fun D : ℝ => 1 + s ^ (16 : ℝ) / Real.log D) atTop (𝓝 1) := by
    simpa using (hratio.const_add 1)
  have hperturb : Tendsto
      (fun D : ℝ => (1 + s ^ (16 : ℝ) / Real.log D) ^ s) atTop (𝓝 1) := by
    simpa using hbase.rpow_const (Or.inl one_ne_zero)
  have hsqrt : Tendsto (fun D : ℝ => Real.sqrt (Real.log D)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hdecay' : Tendsto (fun D : ℝ => 1 / Real.sqrt (Real.log D)) atTop (𝓝 0) :=
    hsqrt.const_div_atTop 1
  have hlog_nonneg : ∀ᶠ D : ℝ in atTop, 0 ≤ Real.log D :=
    (eventually_ge_atTop (1 : ℝ)).mono fun D hD => Real.log_nonneg hD
  have hdecay : Tendsto (fun D : ℝ => (Real.log D) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    apply tendsto_congr' (hlog_nonneg.mono ?_) |>.mpr hdecay'
    intro D hD
    rw [Real.rpow_neg hD, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hsign : ∀ sign : ErrorSign, Tendsto
      (fun D : ℝ =>
        C * Real.exp (Real.sqrt K) *
          ((1 + s ^ (16 : ℝ) / Real.log D) ^ s * s * H.T sign s) *
            (Real.log D) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    intro sign
    have hp := hperturb.mul_const s |>.mul_const (H.T sign s)
    have hp' := (hp.const_mul (C * Real.exp (Real.sqrt K))).mul hdecay
    simpa only [mul_zero] using hp'
  have hplus := (tendsto_order.1 (hsign .plus)).2 ρ hρ
  have hminus := (tendsto_order.1 (hsign .minus)).2 ρ hρ
  filter_upwards [hplus, hminus, eventually_gt_atTop (1 : ℝ)] with D hDp hDm hD
  intro depth
  have hE : 0 ≤ errorEnvelope H depth D 16 s :=
    errorEnvelope_nonneg H depth hD hs.le
      (hH.positive (ErrorSign.ofDepth depth) s hs).le
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD.le
  have hnonneg :
      0 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H depth D 16 s *
        (Real.log D) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hE)
      (Real.rpow_nonneg hlog0 _)
  refine ⟨hnonneg, ?_⟩
  rcases Nat.even_or_odd depth with heven | hodd
  · rw [errorEnvelope_even heven]
    simpa [Real.rpow_natCast, Section13HatLayers.T] using hDm
  · rw [errorEnvelope_odd hodd]
    simpa [Real.rpow_natCast, Section13HatLayers.T] using hDp

/-- Chen's floor level tends to infinity for every `ε < 1/2`.  The proof keeps
the floor explicit and uses the fixed lower exponent `2/5` in the Chen range. -/
theorem tendsto_chenLevel_atTop {ε : ℝ} (hε : ε < 1 / 10) :
    Tendsto (fun N : ℕ => (chenLevel N ε : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro X
  let Y : ℝ := max 1 X
  let Z : ℝ := Y ^ (5 / 2 : ℝ)
  filter_upwards [eventually_ge_atTop ⌈Z⌉₊] with N hN
  have hYpos : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  have hZN : Z ≤ (N : ℝ) := Nat.ceil_le.mp hN
  have hNpos : 0 < (N : ℝ) := (Real.rpow_pos_of_pos hYpos _).trans_le hZN
  have hpow : Z ^ (2 / 5 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hYpos.le _) hZN (by norm_num)
  have hZY : Z ^ (2 / 5 : ℝ) = Y := by
    dsimp [Z]
    rw [← Real.rpow_mul hYpos.le]
    norm_num
  have ha : (2 / 5 : ℝ) ≤ 1 / 2 - ε := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hN0 : N ≠ 0 := by
      intro h
      subst N
      norm_num at hNpos
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN0)
  have hmono : (N : ℝ) ^ (2 / 5 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 ha
  have hfloor : (N : ℝ) ^ (1 / 2 - ε) < (chenLevel N ε : ℝ) := by
    simpa [chenLevel] using lt_cast_floor_add_one ((N : ℝ) ^ (1 / 2 - ε))
  exact (le_max_right 1 X).trans ((hZY ▸ hpow).trans (hmono.trans hfloor.le))

/-- The fixed choices used in the production theorem are simultaneously legal:
`Δ = Θ = 1/2`, `d = 16`, and Chen's `s = 5 - 10ε` stays positive. -/
theorem chen_half_parameters_admissible {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 10) :
    0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧
      7 / (1 - (1 / 2 : ℝ)) < (16 : ℝ) ∧
      0 < chenS ε ∧ chenS ε ≤ 5 := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> unfold chenS <;> linarith

/-- Production Chen-parameter absorption, uniform in *all* depths.  In
particular, the depth may grow with the supported prime carrier.  No uniform
comparison proposition is assumed: parity is eliminated directly from the
literal Section-13 `errorEnvelope`. -/
theorem chen_eventually_all_depth_suzuki_error_absorption
    (H : Section13HatLayers) {β C K ε : ℝ}
    (hH : Section13HatContract H β) (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ depth : ℕ,
      C * Real.exp (Real.sqrt K) *
          errorEnvelope H depth (chenLevel N ε : ℝ) 16 (chenS ε) *
            (Real.log (chenLevel N ε : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ := by
  have hadm := chen_half_parameters_admissible hε0 hε
  have hD := eventually_all_depth_suzuki_error_half
    (H := H) (C := C) (K := K) (s := chenS ε) hH hC hadm.2.2.2.1 ρ hρ
  have hN := (tendsto_chenLevel_atTop hε).eventually hD
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hN
  exact ⟨N₀, fun N hN depth => (hN₀ N hN depth).2⟩

/-- Adaptive-depth corollary: `Nadapt` is completely arbitrary and hence may
track the growing finite carrier. -/
theorem chen_eventually_adaptive_depth_suzuki_error_absorption
    (H : Section13HatLayers) {β C K ε : ℝ}
    (hH : Section13HatContract H β) (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 10)
    (Nadapt : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * Real.exp (Real.sqrt K) *
          errorEnvelope H (Nadapt N) (chenLevel N ε : ℝ) 16 (chenS ε) *
            (Real.log (chenLevel N ε : ℝ)) ^ (-(1 / 2 : ℝ)) < ρ := by
  obtain ⟨N₀, hN₀⟩ := chen_eventually_all_depth_suzuki_error_absorption
    H hH hC hε0 hε ρ hρ
  exact ⟨N₀, fun N hN => hN₀ N hN (Nadapt N)⟩


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
