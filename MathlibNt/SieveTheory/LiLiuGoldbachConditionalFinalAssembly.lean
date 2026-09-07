import MathlibNt.SieveTheory.LiLiuGoldbachPreG11FinalLedger

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact budget for the proposed G11 coefficient, not a proof of its count bound. -/
theorem goldbach_paperG11_budget_identity :
    (661251229/200000000 : ℝ) + 10191/100000 = 681633229/200000000 := by
  norm_num

section ConditionalInputs

variable (g r : ℝ)
/- Pending input: an upper estimate of the ACTUAL G11 count, with its original carrier. -/
variable (hG11 : ∀ δ : ℝ, 0 < δ →
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        (g+δ)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2))
/- Pending input: a lower estimate of the literal signed remainder at some legal cutoff.
The cutoff may depend on N and epsilon; no estimate of its constituent terms is assumed here. -/
variable (hRemaining : ∀ δ : ℝ, 0 < δ →
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ Z : ℝ, 1 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
        (r-δ)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
          (goldbachWeightG11PaidBase N ε : ℝ) -
            (goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ))

include hG11 hRemaining

/-- CONDITIONAL assembly only. Both missing analytic inputs remain explicit parameters.
All three epsilon windows and all thresholds are reconciled before using the chosen Z. -/
theorem goldbachD19_small_epsilon_lower_with_error_of_actual_estimates
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ((r-g-(661251229/200000000 : ℝ)-δ)/4)*
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            (D19 N : ℝ) := by
  let η : ℝ := δ/3
  have hη : 0 < η := div_pos hδ (by norm_num)
  obtain ⟨εb, hεb, hεbu, hb⟩ := goldbachWeight_preG11_allRetained_small_epsilon η hη
  obtain ⟨εg, hεg, hg⟩ := hG11 η hη
  obtain ⟨εr, hεr, hr⟩ := hRemaining η hη
  refine ⟨min εb (min εg εr), lt_min hεb (lt_min hεg hεr),
    (min_le_left _ _).trans hεbu, ?_⟩
  intro ε hε hεlt
  have heb : ε < εb := hεlt.trans_le (min_le_left _ _)
  have heg : ε < εg := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have her : ε < εr := hεlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Nb, hNb, hbN⟩ := hb ε hε heb
  obtain ⟨Ng, hgN⟩ := hg ε hε heg
  obtain ⟨Nr, hrN⟩ := hr ε hε her
  refine ⟨max Nb (max Ng Nr), by omega, ?_⟩
  intro N hN hEven
  obtain ⟨Z, hZ, hZu, hrem⟩ := hrN N (by omega) hEven
  have hbase := hbN N (by omega) hEven Z hZ hZu
  have hg11 := hgN N (by omega) hEven
  dsimp [η] at hbase hg11 hrem
  nlinarith [hbase, hg11, hrem]

/-- A convenient positive-margin specialization; the preceding theorem retains arbitrary error. -/
theorem goldbachD19_small_epsilon_lower_of_actual_estimates
    (hgap : 0 < r-g-(661251229/200000000 : ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ((r-g-(661251229/200000000 : ℝ))/8)*
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
            (D19 N : ℝ) := by
  have h := goldbachD19_small_epsilon_lower_with_error_of_actual_estimates
    g r hG11 hRemaining ((r-g-(661251229/200000000 : ℝ))/2)
      (div_pos hgap (by norm_num))
  have he : (r-g-(661251229/200000000 : ℝ)-(r-g-(661251229/200000000 : ℝ))/2)/4 =
      (r-g-(661251229/200000000 : ℝ))/8 := by ring
  simpa only [he] using h

/-- Eliminate the auxiliary epsilon, retaining a quantitative lower bound on distinct p. -/
theorem goldbachD19_eventually_lower_of_actual_estimates
    (hgap : 0 < r-g-(661251229/200000000 : ℝ)) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ((r-g-(661251229/200000000 : ℝ))/8)*
        (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        (D19 N : ℝ) := by
  obtain ⟨ε₀, hε₀, _hε₀u, h⟩ :=
    goldbachD19_small_epsilon_lower_of_actual_estimates g r hG11 hRemaining hgap
  exact h (ε₀/2) (by positivity) (by linarith)

/-- Literal p+r*q representation; not ordinary P2 and not a count of witness triples. -/
theorem goldbach19_eventually_representation_of_actual_estimates
    (hgap : 0 < r-g-(661251229/200000000 : ℝ)) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p r q : ℕ, p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^10 ≤ q^9 := by
  obtain ⟨N₀, hN₀, h⟩ :=
    goldbachD19_eventually_lower_of_actual_estimates g r hG11 hRemaining hgap
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs : 0 < SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_pos (mul_pos (SingularSeries.liuSingularSeries_pos N) (by linarith))
      (pow_pos (Real.log_pos hn) _)
  have hd : (0 : ℝ) < D19 N :=
    (mul_pos (div_pos hgap (by norm_num)) hs).trans_le (h N hN hEven)
  exact (D19_pos_iff N).mp (by exact_mod_cast hd)

/-- Plug-in endpoint for 0.10191 OR ANY SMALLER proved actual G11 upper coefficient.
The quantitative conclusion automatically keeps the gain when g is smaller. -/
theorem goldbachD19_eventually_lower_of_g11_le_10191
    (hg : g ≤ (10191/100000 : ℝ)) (hr : (681633229/200000000 : ℝ) < r) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ((r-g-(661251229/200000000 : ℝ))/8)*
        (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
        (D19 N : ℝ) := by
  exact goldbachD19_eventually_lower_of_actual_estimates g r hG11 hRemaining (by linarith)

/-- The same author-or-better plug-in endpoint for the original 1.9 representation. -/
theorem goldbach19_eventually_representation_of_g11_le_10191
    (hg : g ≤ (10191/100000 : ℝ)) (hr : (681633229/200000000 : ℝ) < r) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p r q : ℕ, p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^10 ≤ q^9 := by
  exact goldbach19_eventually_representation_of_actual_estimates g r hG11 hRemaining
    (by linarith)

end ConditionalInputs

/-- Existing unconditional G11 theorem actually inhabits the generic input interface.
It supplies 0.10385101, NOT the pending author value 0.10191. -/
theorem goldbachG11_uniformScalar_fits_finalAssembly :
    ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
          (goldbachWeightG11 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
            ((10385101/100000000 : ℝ)+δ)*
              (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  intro δ hδ
  obtain ⟨Ng, _hNg, hg⟩ := goldbachWeightG11_le_uniformScalar_numeric_fixed
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε _hεlt
  refine ⟨Ng, ?_⟩
  intro N hN hEven
  have hs : 0 ≤ SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2 :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hg N hN hEven ε hε.le).trans
    (mul_le_mul_of_nonneg_right (by linarith) hs)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig