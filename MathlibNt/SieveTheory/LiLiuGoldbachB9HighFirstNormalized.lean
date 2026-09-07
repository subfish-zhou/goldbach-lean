import MathlibNt.SieveTheory.LiLiuGoldbachB9HighFirstDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachB9NormalizedMainMass

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem highFirst_coefficient {τ δ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτδ : 120 * τ ≤ δ) :
    8 * (1 + τ) ^ 4 ≤ 8 + δ := by
  have h2 : τ ^ 2 ≤ τ := by nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hτ1)]
  have h3 : τ ^ 3 ≤ τ := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hτ0]
  have h4 : τ ^ 4 ≤ τ := by
    have hh := pow_le_pow_left₀ (sq_nonneg τ) h2 2
    nlinarith
  nlinarith

private theorem highFirst_paid_error (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        η * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  have hηU : 0 < η * SingularSeries.liuUniversalProduct :=
    mul_pos hη SingularSeries.liuUniversalProduct_pos
  have hlogs := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (C / (η * SingularSeries.liuUniversalProduct))))
  filter_upwards [hlogs] with N hN
  have hl : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hN)
  have hC : C / Real.log (N : ℝ) ≤ η * SingularSeries.liuUniversalProduct := by
    apply (div_le_iff₀ hl).mpr
    simpa [mul_comm] using (div_le_iff₀ hηU).mp ((le_max_right _ _).trans hN)
  calc
    _ = (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      rw [Real.rpow_ofNat]
      field_simp
    _ ≤ (η * SingularSeries.liuUniversalProduct) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ (η * SingularSeries.liuSingularSeries N) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hη.le) (by positivity)
    _ = _ := by ring

/-- The actual high BoundingSieve, uniform Euler product and relative Li estimate.
Only the scalar cutoff geometry is borrowed from the full-domain consumer. -/
theorem goldbachB9HighFirstSiftedCount_normalized_kernel
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      let Z := Real.sqrt ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1))
      2 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
        (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) ≤
        ((8 + δ) * goldbachK9High N + η) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  let τ : ℝ := min (δ / 120) 1
  have hτ : 0 < τ := lt_min (by positivity) zero_lt_one
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτδ : 120 * τ ≤ δ := by
    have h := min_le_left (δ / 120) (1 : ℝ)
    dsimp [τ]
    linarith
  obtain ⟨C, _hC, B, hB, Nr, _hNr, hr⟩ :=
    goldbachB9HighFirst_upperErrSum_log_saving 3 (by norm_num)
  obtain ⟨z₀, hfactor⟩ := goldbachB10SiftedCount_le_rosserFactor_add_upperErrSum
    (τ * Real.exp Real.eulerMascheroniConstant) (mul_pos hτ (Real.exp_pos _))
  obtain ⟨Z₀, _hZ₀, hprod⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries τ hτ
  obtain ⟨Ng, hNg, hg⟩ :=
    goldbachB9Plus_normalized_cutoff_geometry B (max z₀ Z₀) τ hB hτ hτ1
  obtain ⟨Nx, _hNx, hx⟩ := goldbachX9High_nonneg_eventually
  obtain ⟨Nk, _hNk, hk⟩ := goldbachX9High_le_kernel_eventually τ hτ
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ hEven : Even N,
      let Z := Real.sqrt ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1))
      2 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
        (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (1 / 10 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) ≤
        ((8 + δ) * goldbachK9High N + η) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop Nr, eventually_ge_atTop Ng,
      eventually_ge_atTop Nx, eventually_ge_atTop Nk, highFirst_paid_error C η hη]
      with N hrN hgN hxN hkN herr
    intro hEven
    have hN4 : 4 ≤ N := hNg.trans hgN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
    let Z := Real.sqrt Δ
    let X := goldbachX9High N
    let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z X
    have hΔ : 0 < Δ := by dsimp [Δ]; positivity
    obtain ⟨hZbig, _hquarter, hZsqrt, hs, hlogZ, hratio⟩ := hg N hgN
    have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
    have hz₀ : z₀ ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZbig)
    have hZ₀ : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZbig)
    have hX : 0 ≤ X := hx N hxN
    have hK : 0 ≤ goldbachK9High N := goldbachK9High_nonneg N (by omega)
    have hbound := hfactor N hEven 0 ((N : ℝ) ^ (1 / 10 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) Z Δ 2 X hz₀ hZ2 hΔ hs.symm
      (by norm_num) (by norm_num) hX
    have hV : sieveProductPrimeFactors S ≤
        2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
          SingularSeries.liuSingularSeries N / Real.log Z := by
      apply (le_div_iff₀ hlogZ).mpr
      rw [← goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven 0
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) Z X]
      exact hprod N hN4 hEven Z hZ₀
    have hfactor2 :
        jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant =
            Real.exp Real.eulerMascheroniConstant * (1 + τ) := by
      norm_num [jurkatRichertUpperLinearSieveFactor]
      ring
    have hinv : 1 / Real.log Z ≤ 4 * (1 + τ) / Real.log (N : ℝ) := by
      calc
        _ = (Real.log (N : ℝ) / Real.log Z) / Real.log (N : ℝ) := by
          field_simp [hlogN.ne', hlogZ.ne']
        _ ≤ _ := div_le_div_of_nonneg_right hratio hlogN.le
    have hc : 2 * (1 + τ) ^ 2 / Real.log Z ≤
        8 * (1 + τ) ^ 3 / Real.log (N : ℝ) := by
      calc
        _ = 2 * (1 + τ) ^ 2 * (1 / Real.log Z) := by ring
        _ ≤ 2 * (1 + τ) ^ 2 * (4 * (1 + τ) / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = _ := by ring
    have hmain :
        X * (jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant) * sieveProductPrimeFactors S ≤
          ((8 + δ) * goldbachK9High N) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      rw [hfactor2]
      have hexp : Real.exp Real.eulerMascheroniConstant *
          Real.exp (-Real.eulerMascheroniConstant) = 1 := by
        rw [← Real.exp_add]
        norm_num
      calc
        _ ≤ X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
            (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
              SingularSeries.liuSingularSeries N / Real.log Z) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
        _ = (SingularSeries.liuSingularSeries N * X) *
            (2 * (1 + τ) ^ 2 / Real.log Z) := by
          calc
            _ = (Real.exp Real.eulerMascheroniConstant *
                Real.exp (-Real.eulerMascheroniConstant)) *
                ((SingularSeries.liuSingularSeries N * X) *
                  (2 * (1 + τ) ^ 2 / Real.log Z)) := by ring
            _ = _ := by rw [hexp, one_mul]
        _ ≤ (SingularSeries.liuSingularSeries N * X) *
            (8 * (1 + τ) ^ 3 / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hc
            (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le hX)
        _ = (8 * (1 + τ) ^ 3 * SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) *
            X := by ring
        _ ≤ (8 * (1 + τ) ^ 3 * SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) *
            ((1 + τ) * ((N : ℝ) / Real.log (N : ℝ)) * goldbachK9High N) :=
          mul_le_mul_of_nonneg_left (hk N hkN) (by
            have := SingularSeries.liuSingularSeries_pos N
            positivity)
        _ = (8 * (1 + τ) ^ 4 * goldbachK9High N) *
            (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (highFirst_coefficient hτ.le hτ1 hτδ) hK)
          (by have := SingularSeries.liuSingularSeries_pos N; positivity)
    have hrem := (hr N hrN hEven Z).trans herr
    refine ⟨hZ2, hZsqrt, hbound.trans ?_⟩
    simpa only [add_mul, S, X, Δ, goldbachB10BoundingSieve] using add_le_add hmain hrem
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨B, hB, max 4 N₀, le_max_left _ _, fun N hN =>
    hN₀ N ((le_max_right _ _).trans hN)⟩

/-- Independent upper bound for actual high S5; no free analytic or sieve input remains. -/
theorem goldbachS5HighFirstClosed_normalized_upper
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (_hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
        ((8 + δ) * goldbachK9High N + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨B, _hB, Ns, hNs, hs⟩ :=
    goldbachB9HighFirstSiftedCount_normalized_kernel δ (δ / 2) hδ (by positivity)
  obtain ⟨Nt, _hNt, ht⟩ :=
    goldbachS5HighFirstClosed_le_sifted_normalized ε (δ / 2) hε (by positivity)
  refine ⟨max Ns Nt, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have htN : Nt ≤ N := (le_max_right _ _).trans hN
  let Z := Real.sqrt ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1))
  obtain ⟨hZ2, hZsqrt, hbound⟩ := hs N hsN hEven
  have htransport := ht N htN Z (by linarith) hZsqrt
  dsimp [Z] at htransport
  linarith only [hbound, htransport]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig