import MathlibNt.SieveTheory.LiLiuGoldbachStrictTriple
import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual finite error: noncoprime differences, square diagonal,
repeated triples, and the closed upper endpoint. No size bound is built in. -/
noncomputable def goldbachFiniteError (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  2 * goldbachBadCount A N + goldbachQ A N z y + goldbachR A N z y +
    goldbachB6 A N z y

theorem goldbachFiniteError_nonneg (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    0 ≤ goldbachFiniteError A N z y := by
  have hX : 0 ≤ goldbachBadCount A N := by
    unfold goldbachBadCount
    exact_mod_cast Nat.zero_le _
  have hQ : 0 ≤ goldbachQ A N z y := by
    unfold goldbachQ
    exact Finset.sum_nonneg (fun r _ => literalH_nonneg A N (r^2) r)
  have hR := goldbachR_nonneg A N z y
  have hB := goldbachB6_nonneg A N z y
  unfold goldbachFiniteError
  omega

/-- The closed-endpoint finite Goldbachbig lower bound for the actual D19
count. The error is explicit and nonnegative, but its power-saving size
and the positivity of the resulting lower bound are separate obligations. -/
theorem goldbach_closed_sieve_lower_bound_eventually (ε : ℝ) (hε : 0 < ε)
    (hεupper : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ κ σ : ℝ,
      (1 : ℝ) / 21 < κ → κ < σ → σ ≤ (1 : ℝ) / 3 →
      2 * goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ κ) -
        2 * goldbachS2 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) -
        2 * goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ σ) -
        goldbachS5Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) +
        goldbachS6Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) -
        goldbachFiniteError (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) ≤ 2 * (D19 N : ℤ) := by
  obtain ⟨N₀,hN₀⟩ := goldbach_strict_triple_lower_bound_eventually ε hε hεupper
  refine ⟨N₀, ?_⟩
  intro N hN hEven κ σ hκ hκσ hσ
  have h := hN₀ N hN hEven κ σ hκ hκσ hσ
  have hW := goldbachWStrict_eq_goldbachS6Closed_sub_goldbachR_sub_goldbachB6
    (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) ((N : ℝ)^σ)
  have h3 := goldbachS3HalfOpen_le_goldbachS3Closed
    (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) ((N : ℝ)^σ)
  have h5 := goldbachS5HalfOpen_le_goldbachS5Closed
    (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) ((N : ℝ)^σ)
  rw [hW] at h
  unfold goldbachFiniteError
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig