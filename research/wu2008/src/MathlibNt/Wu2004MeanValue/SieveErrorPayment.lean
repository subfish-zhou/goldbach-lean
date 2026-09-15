import MathlibNt.Wu2004MeanValue.ManuscriptRemainders
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# Paying the actual sequence errors in the source normalization

The frozen positive universal Euler product is a lower bound for every
`liuSingularSeries N`. Thus a fixed inverse-log cube saving pays any prescribed
margin at the sieve scale, uniformly in the later integer `N`.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
open scoped BigOperators

theorem eventually_logCube_le_singular_margin (E ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      E * x / Real.log x ^ (3 : ℝ) ≤
        ε * liuSingularSeries N * x / Real.log x ^ 2 := by
  have hU := liuUniversalProduct_pos
  have hlog : ∀ᶠ x : ℝ in atTop,
      max 1 (E / (ε * liuUniversalProduct)) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with x hx hx1 N
  have hl : 0 < Real.log x := by
    have := (le_max_left 1 (E / (ε * liuUniversalProduct))).trans hx
    linarith
  have hE : E ≤ ε * liuUniversalProduct * Real.log x := by
    have h := (le_max_right 1 (E / (ε * liuUniversalProduct))).trans hx
    exact (div_le_iff₀ (mul_pos hε hU)).mp h |>.trans_eq (mul_comm _ _)
  have hEN : E ≤ ε * liuSingularSeries N * Real.log x :=
    hE.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (liuUniversalProduct_le_liuSingularSeries N) hε.le)
      hl.le)
  rw [show Real.log x ^ (3 : ℝ) = Real.log x ^ (3 : ℕ) by
    exact Real.rpow_natCast _ _]
  calc
    E * x / Real.log x ^ 3 ≤
        (ε * liuSingularSeries N * Real.log x) * x / Real.log x ^ 3 := by
      gcongr
    _ = _ := by field_simp

/-- The inclusive tail's actual common-X remainder, including its paid lower
atom, is negligible in the source-normalized sieve scale. -/
theorem tail_sequence_remainder_normalized (c τ η ε : ℝ)
    (hc : 0 < c) (hτ : 1 / 3 < τ) (hη : 0 < η) (hη1 : η < 1)
    (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt N / Real.log N ^ B →
      (∑ d ∈ sieveDivisors N D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |tailRemainder N c τ η d|) ≤
          ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨B, C, hB, _, R, hR⟩ :=
    tail_sequence_remainder_muSquare 3 c τ η (by norm_num) hc hτ hη hη1
  have hpay := tendsto_natCast_atTop_atTop.eventually
    (eventually_logCube_le_singular_margin C ε hε)
  have hlarge : ∀ᶠ N : ℕ in atTop, R ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
  refine ⟨B, hB, eventually_atTop.mp ?_⟩
  filter_upwards [hpay, hlarge] with N hNp hNr D hD hcut
  exact (hR N hNr D hD hcut).trans (hNp N)

/-- The open block's actual common-X error, including its paid upper atom,
is negligible uniformly in every later `N` and `eta`. -/
theorem block_sequence_remainder_normalized (a ε : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∃ H₀ : ℝ, ∀ H : ℝ, H₀ ≤ H →
      ∀ (N : ℕ) (η : ℝ), η ≤ 1 →
      ∀ D : ℝ, 0 ≤ D → D ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      (∑ d ∈ sieveDivisors N D, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
        |blockRemainder H N a η d|) ≤
          ε * liuSingularSeries N * H / Real.log H ^ 2 := by
  obtain ⟨B, C, hB, _, R, hR⟩ :=
    block_sequence_remainder_muSquare 3 a (by norm_num) ha ha2
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_logCube_le_singular_margin C (ε / 2) (by positivity))
  refine ⟨B, hB, max 2 (max R T), ?_⟩
  intro H hH N η hη D hD hcut
  have hH2 : 2 ≤ H := (le_max_left _ _).trans hH
  have hHR : R ≤ H := (le_max_left R T).trans ((le_max_right _ _).trans hH)
  have hHT : T ≤ H := (le_max_right R T).trans ((le_max_right _ _).trans hH)
  have hl : 0 < Real.log H := Real.log_pos (by linarith)
  have hl2 : Real.log H ≤ Real.log (2 * H) :=
    Real.log_le_log (by linarith) (by linarith)
  calc
    _ ≤ C * (2 * H) / Real.log (2 * H) ^ (3 : ℝ) :=
      hR H hHR N η hη D hD hcut
    _ ≤ (ε / 2) * liuSingularSeries N * (2 * H) / Real.log (2 * H) ^ 2 :=
      hT (2 * H) (by linarith) N
    _ = ε * liuSingularSeries N * H / Real.log (2 * H) ^ 2 := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hε.le (liuSingularSeries_pos N).le) (by linarith))
        (sq_pos_of_pos hl)
      exact pow_le_pow_left₀ hl.le hl2 2

end Wu2004MeanValue
