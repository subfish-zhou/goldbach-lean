import MathlibNt.SieveTheory.LiLiuGoldbachT16Coverage
import MathlibNt.SieveTheory.LiLiuGoldbachWeightTriplePartition
import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruplePaid
import MathlibNt.SieveTheory.LiLiuGoldbachFiniteBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG10SwitchBudget
import MathlibNt.SieveTheory.LiLiuGoldbachCubeCutoff

open Filter
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal three-resource coverage, with the actual shared endpoint. -/
theorem goldbachWeight_three_triples_le_s6_add_b6
    (A : Finset ℕ) (N : ℕ) {α β γ : ℝ}
    (hN : 2 ≤ N) (hz : 2 ≤ (N : ℝ) ^ α) (hαβ : α ≤ β)
    (hβ : (1 : ℝ) / 18 < β) (hβγ : β < (1 - 3 * β) / 3)
    (hγ : (1 - 3 * β) / 3 < γ) (hγu : γ < (1 : ℝ) / 3) :
    goldbachWeightT14 A N ((N : ℝ) ^ α) ((N : ℝ) ^ β) +
      goldbachWeightT15 A N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ) +
      goldbachWeightT16 A N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
    goldbachS6Closed A N ((N : ℝ) ^ α) ((N : ℝ) ^ ((1 : ℝ) / 3)) +
      goldbachB6 A N ((N : ℝ) ^ α) ((N : ℝ) ^ β) := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzb := Real.rpow_le_rpow_of_exponent_le hbase hαβ
  have hbc := Real.rpow_le_rpow_of_exponent_le hbase (lt_trans hβγ hγ).le
  have hcu := Real.rpow_le_rpow_of_exponent_le hbase hγu.le
  have ht16 : goldbachWeightT16 A N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) ≤
      goldbachWeightUpperMiddle A N ((N : ℝ) ^ α) ((N : ℝ) ^ β)
        ((N : ℝ) ^ ((1 : ℝ) / 3)) := by
    simpa only [goldbachWeightUpperMiddle] using
      goldbachWeightT16_le_explicitClosedPrimeTripleSum A N hN hαβ hβ hβγ hγ hγu
  have hp := goldbachWeightT14_add_goldbachWeightT15_add_goldbachWeightUpperMiddle_le_goldbachS6Closed_add_goldbachB6
    A N ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
      ((N : ℝ) ^ ((1 : ℝ) / 3)) hz hzb hbc hcu
  omega

/-- The common eleven terms, with their literal finite carriers. The omitted
negative term is separately either corrected G10 or the labelled prime source. -/
noncomputable def goldbachWeightTwelveBase (A : Finset ℕ) (N : ℕ) (z b c T : ℝ) : ℤ :=
  3 * goldbachS1 A N z + goldbachS1 A N b - 4 * goldbachS2 A N T -
    goldbachS3Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) - goldbachS3Closed A N z c +
    goldbachWeightG6 A N z b + goldbachWeightG7 A N z b c - 2 * goldbachS4 A N c -
    goldbachS5Closed A N z ((N : ℝ) ^ ((1 : ℝ) / 3)) -
    goldbachWeightG11 A N z b - goldbachWeightG12 A N z b c

/-- The corrected twelve-term expression; this is not the printed G10 expression. -/
noncomputable def goldbachWeightTwelveCorrectedRHS
    (A : Finset ℕ) (N : ℕ) (z b c T : ℝ) : ℤ :=
  goldbachWeightTwelveBase A N z b c T - goldbachG10Corrected A N b c

/-- The twelve-term expression with the genuine labelled prime source in place
of corrected G10. No analytic estimate of that source is built into this definition. -/
noncomputable def goldbachWeightTwelveSwitchedRHS
    (A : Finset ℕ) (N : ℕ) (ε z b c T : ℝ) : ℤ :=
  goldbachWeightTwelveBase A N z b c T - goldbachPi10 N ε b c

/-- The actual D19 lower bound for the corrected twelve-term formula, with
all finite losses paid. This is a signed lower bound, not a positivity theorem. -/
theorem goldbachWeight_twelve_corrected_lower_bound_eventually
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α β γ : ℝ,
      (1 : ℝ) / 18 < α → α < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      (goldbachWeightTwelveCorrectedRHS (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
        1334 * (N : ℝ) ^ (1 - α) ≤ 4 * (D19 N : ℝ) := by
  obtain ⟨Nb, hb⟩ := goldbachbig_finite_lower_bound_eventually ε hε hεu
  obtain ⟨Nq, hq⟩ := goldbachWeight_quadruple_paid_eventually ε hε
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Nb, eventually_ge_atTop Nq,
    eventually_ge_atTop (2 : ℕ), hpowers] with N hNb hNq hN hpow
  intro hEven α β γ hα hαβ hβγ hγ hγu
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  have hα21 : (1 : ℝ) / 21 < α := by linarith
  have hβ21 : (1 : ℝ) / 21 < β := by linarith
  have hβ18 : (1 : ℝ) / 18 < β := lt_trans hα hαβ
  have hβγlt : β < γ := lt_trans hβγ hγ
  have hαu : α < (1 : ℝ) / 3 := lt_trans (lt_trans hαβ hβγlt) hγu
  have hz : 2 ≤ (N : ℝ) ^ α :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase hα21.le)
  have hzb := Real.rpow_le_rpow_of_exponent_le hbase hαβ.le
  have hbc := Real.rpow_le_rpow_of_exponent_le hbase hβγlt.le
  have hGa := hb N hNb hEven α ((1 : ℝ) / 3) hα21 hαu le_rfl
  have hGb := hb N hNb hEven β γ hβ21 hβγlt hγu.le
  have hQ := hq N hNq α β γ hα21 hαβ.le hβγlt.le
  have hS5 := (Int.cast_le (R := ℝ)).mpr
    (goldbachS5Closed_le_goldbachG10Corrected_add_goldbachWeightT16
      (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        (hz.trans hzb) hbc)
  have hCover := (Int.cast_le (R := ℝ)).mpr
    (goldbachWeight_three_triples_le_s6_add_b6 (goldbachDifferenceCarrier N ε) N
      hN hz hαβ.le hβ18 hβγ hγ hγu)
  have hA : ∀ n ∈ goldbachDifferenceCarrier N ε, 1 ≤ n ∧ n < N := by
    intro n hn
    have hnB := goldbachG10DifferenceCarrier_bounds hε hn
    exact ⟨hnB.1, hnB.2.1⟩
  have hB : (goldbachB6 (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ α) ((N : ℝ) ^ β) : ℝ) ≤ 400 * (N : ℝ) ^ (1 - α) := by
    calc
      _ ≤ 400 * (N : ℝ) / ((N : ℝ) ^ α) :=
        goldbachB6_le_four_hundred_mul_div_z (goldbachDifferenceCarrier N ε) N
          (by omega) hA hα21 rfl hzb
      _ = 400 * (N : ℝ) ^ (1 - α) := by
        rw [Real.rpow_sub hN0, Real.rpow_one]
        ring
  have hNonneg : 0 ≤ (goldbachS6Closed (goldbachDifferenceCarrier N ε) N
      ((N : ℝ) ^ β) ((N : ℝ) ^ γ) : ℝ) := by
    have hi : 0 ≤ goldbachS6Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ β) ((N : ℝ) ^ γ) := by
      unfold goldbachS6Closed
      exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun r _ =>
        Finset.sum_nonneg fun s _ => literalH_nonneg _ _ _ _
    exact_mod_cast hi
  have hpβ : (N : ℝ) ^ (1 - β) ≤ (N : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  simp only [goldbachS4_cube_cutoff_eq_zero] at hGa
  dsimp only [goldbachWeightTwelveCorrectedRHS, goldbachWeightTwelveBase]
  push_cast at hGa hGb hS5 hCover ⊢
  linarith

/-- The same actual lower bound with labelled Pi10 and its additional finite
payment. This still does not assert an analytic bound or positive main term. -/
theorem goldbachWeight_twelve_switched_lower_bound_eventually
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α β γ : ℝ,
      (1 : ℝ) / 18 < α → α < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      (goldbachWeightTwelveSwitchedRHS (goldbachDifferenceCarrier N ε) N ε
        ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
        2214 * (N : ℝ) ^ (1 - α) ≤ 4 * (D19 N : ℝ) := by
  obtain ⟨Nc, hc⟩ := goldbachWeight_twelve_corrected_lower_bound_eventually ε hε hεu
  obtain ⟨Np, hp⟩ := goldbachG10Corrected_eventually_le_pi10_add_880 ε hε
  refine ⟨max (max Nc Np) 2, ?_⟩
  intro N hN hEven α β γ hα hαβ hβγ hγ hγu
  have hNc : Nc ≤ N := (le_max_left Nc Np).trans ((le_max_left (max Nc Np) 2).trans hN)
  have hNp : Np ≤ N := (le_max_right Nc Np).trans ((le_max_left (max Nc Np) 2).trans hN)
  have hN2 : 2 ≤ N := (le_max_right (max Nc Np) 2).trans hN
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmain := hc N hNc hEven α β γ hα hαβ hβγ hγ hγu
  have hswitch := hp N hNp β γ (lt_trans hα hαβ) hβγ hγ hγu
  have hpβ : (N : ℝ) ^ (1 - β) ≤ (N : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  dsimp only [goldbachWeightTwelveCorrectedRHS] at hmain
  dsimp only [goldbachWeightTwelveSwitchedRHS]
  push_cast at hmain ⊢
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig