import MathlibNt.SieveTheory.LiLiuGoldbachPi10Sifted
import MathlibNt.SieveTheory.LiLiuGoldbachWeightLogScale

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual twelve-term expression with a labelled sifted B10 source.
Only the tenth source changes; no output or factor labels are deduplicated. -/
noncomputable def goldbachWeightTwelveSiftedRHS
    (A : Finset ℕ) (N : ℕ) (ε z b c T Z : ℝ) : ℤ :=
  goldbachWeightTwelveBase A N z b c T - goldbachB10SiftedCount N ε b c Z

/-- A uniform analytic-scale lower bound from the actual sifted labelled source.
The fixed theta is strictly below one; the threshold precedes every Z and
all sieve exponents. This supplies no analytic bound on the sifted main term. -/
theorem goldbachWeight_twelve_sifted_log_scale_eventually
    (ε δ θ : ℝ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) (hδ : 0 < δ)
    (_hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α β γ Z : ℝ,
      (1 : ℝ) / 18 < α → α < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      1 ≤ Z → Z ≤ (N : ℝ) ^ θ →
      (goldbachWeightTwelveSiftedRHS (goldbachDifferenceCarrier N ε) N ε
        ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) Z : ℝ) -
        δ * (N : ℝ) / (Real.log N) ^ 2 ≤ 4 * (D19 N : ℝ) := by
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨Ns, hs⟩ := goldbachWeight_twelve_switched_log_scale_eventually ε (δ / 2) hε hεu hδ2
  obtain ⟨Ne, hNe2, he⟩ := goldbach_power_error_le_log_scale_eventually
    400 (1 - θ) (δ / 2) (by norm_num) (by linarith) hδ2
  refine ⟨max Ns Ne, ?_⟩
  intro N hN hEven α β γ Z hα hαβ hβγ hγ hγu hZ1 hZθ
  have hNs : Ns ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNe2.trans hNe
  have hmain := hs N hNs hEven α β γ hα hαβ hβγ hγ hγu
  have hsmall : 400 * (N : ℝ) ^ θ ≤ (δ / 2) * (N : ℝ) / (Real.log N) ^ 2 := by
    simpa only [sub_sub_cancel] using he N hNe (1 - θ) le_rfl
  have hfloor : (⌊Z⌋₊ : ℝ) ≤ (N : ℝ) ^ θ :=
    (Nat.floor_le (by linarith : 0 ≤ Z)).trans hZθ
  have hswitch := (Int.cast_le (R := ℝ)).mpr
    (goldbachPi10_le_goldbachB10SiftedCount_add_fourHundred_floor
      (c := (N : ℝ) ^ γ) (Z := Z) hN2 hε (lt_trans hα hαβ) hZ1)
  dsimp only [goldbachWeightTwelveSwitchedRHS] at hmain
  dsimp only [goldbachWeightTwelveSiftedRHS]
  push_cast at hmain hswitch ⊢
  have hscale : δ * (N : ℝ) / (Real.log N) ^ 2 =
      2 * ((δ / 2) * (N : ℝ) / (Real.log N) ^ 2) := by ring
  linarith only [hmain, hsmall, hfloor, hswitch, hscale]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
