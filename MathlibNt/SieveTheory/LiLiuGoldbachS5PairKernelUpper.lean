import MathlibNt.SieveTheory.LiLiuGoldbachB9NormalizedMainMass
import MathlibNt.SieveTheory.LiLiuGoldbachB9MainMassTransport

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual S5Closed upper bound with only its actual finite prime-pair kernel left.
No integral or decimal estimate for that kernel is assumed or asserted. -/
theorem goldbachS5Closed_normalized_upper_pairKernel
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((8 + δ) * goldbachB9PairLogKernel N + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  let t : ℝ := min (δ / 10) 1
  have ht : 0 < t := lt_min (by positivity) zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htδ : 10 * t ≤ δ := by have h := min_le_left (δ / 10) (1 : ℝ); dsimp [t]; linarith
  have htδ' : t ≤ δ := by linarith
  have hcoef : (8 + t) * (1 + t) ≤ 8 + δ := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
  obtain ⟨Ns, hNs, hs⟩ := goldbachS5Closed_normalized_upper_mainMass t ε ht hε hεu
  obtain ⟨Nm, hNm, hm⟩ := goldbachB9PlusMainMass_le_pair_kernel t ht
  obtain ⟨Nx, _hNx, hx⟩ := goldbachB9PlusMainMass_nonneg_eventually
  refine ⟨max Ns (max Nm Nx), hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have hmN : Nm ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hxN : Nx ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN4 : 4 ≤ N := hNs.trans hsN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let C := SingularSeries.liuSingularSeries N
  let K := goldbachB9PairLogKernel N
  let M := C * (N : ℝ) / Real.log (N : ℝ)^2
  have hC : 0 < C := SingularSeries.liuSingularSeries_pos N
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmass := hm N hmN
  have hK : 0 ≤ K := by
    have hnonneg := (hx N hxN).trans hmass
    exact nonneg_of_mul_nonneg_right hnonneg (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (8 + t) * C / Real.log (N : ℝ) by positivity)
  have hupper :
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        (((8 + t) * (1 + t)) * K + t) * M := by
    calc
      _ ≤ (8 + t) * C * goldbachB9PlusMainMass N / Real.log (N : ℝ) + t * M := by
        simpa only [C, M, mul_div_assoc, mul_assoc] using hs N hsN hEven
      _ = ((8 + t) * C / Real.log (N : ℝ)) * goldbachB9PlusMainMass N + t * M := by ring
      _ ≤ ((8 + t) * C / Real.log (N : ℝ)) *
          ((1 + t) * ((N : ℝ) / Real.log (N : ℝ)) * K) + t * M :=
        add_le_add hscaled (le_rfl : t * M ≤ t * M)
      _ = _ := by dsimp [M, K]; ring
  apply hupper.trans
  apply mul_le_mul_of_nonneg_right _ hM
  have hmul := mul_le_mul_of_nonneg_right hcoef hK
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig