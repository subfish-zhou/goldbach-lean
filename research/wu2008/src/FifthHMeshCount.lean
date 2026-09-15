import FifthHMesh
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem fifthH_mesh_box_theta_lower {N : ℕ} {δ a c x y Δ : ℝ}
    (hN : 4 ≤ N)
    (hxy : x + y < truncatedSixthLowerC δ)
    (ha : (N : ℝ) ^ a ≤ (N : ℝ) ^ x / Δ)
    (hc : (N : ℝ) ^ c ≤ (N : ℝ) ^ y / Δ) :
    (4 * logarithmicIntegral N * wuSingularSeries N /
        ((truncatedSixthLowerC δ - a - c) * log N)) *
      (∑ p ∈ truncatedSixthLowerBoxPairs N Δ x y, 1 / ((p.1 : ℝ) * p.2)) ≤
      boxTheta N ((N : ℝ) ^ truncatedSixthLowerC δ)
        (convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x]) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := log_pos hNR
  have hC := wuSingularSeries_pos N (by omega)
  have hli : 0 ≤ logarithmicIntegral N :=
    (show (0 : ℝ) ≤ N / (2 * log N) by positivity).trans (box_trueLi_lower hN)
  have hW : convolutionWuWindows N Δ ![(N : ℝ) ^ y, (N : ℝ) ^ x] =
      ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
        primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)] := by
    funext j
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with hj | hj
    · have hj0 : j = 0 := Fin.ext hj
      subst j
      rfl
    · have hj1 : j = 1 := Fin.ext hj
      subst j
      rfl
  unfold boxTheta
  rw [hW]
  have hsum :
      wuSingularSeries N / ((truncatedSixthLowerC δ - a - c) * log N) *
        (∑ p ∈ truncatedSixthLowerBoxPairs N Δ x y, 1 / ((p.1 : ℝ) * p.2)) ≤
      ∑ e ∈ boxConvolutionSupport
        ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
          primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)],
        (convolutionCoeff
          ![primeWindow N ((N : ℝ) ^ y / Δ) ((N : ℝ) ^ y),
            primeWindow N ((N : ℝ) ^ x / Δ) ((N : ℝ) ^ x)] e : ℝ) *
          (wuSingularSeries (e * N) / ((Nat.totient e : ℝ) *
            log ((N : ℝ) ^ truncatedSixthLowerC δ / e))) := by
    rw [truncatedSixthLower_two_window_sum]
    unfold truncatedSixthLowerBoxPairs
    rw [mul_sum, sum_product, sum_product, sum_comm]
    apply sum_le_sum
    intro q hq
    apply sum_le_sum
    intro p hp
    have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1.pos
    have he0 : 0 < q * p := mul_pos hq'.1.pos hp'.1.pos
    have heR : (0 : ℝ) < (q * p : ℕ) := by exact_mod_cast he0
    have hlo : (N : ℝ) ^ (a + c) ≤ (q * p : ℕ) := by
      rw [Nat.cast_mul, rpow_add hN0, mul_comm (q : ℝ)]
      exact mul_le_mul (ha.trans hp'.2.2.1) (hc.trans hq'.2.2.1)
        (rpow_nonneg hN0.le _) hp0.le
    have hup : (q * p : ℕ) < (N : ℝ) ^ truncatedSixthLowerC δ := by
      have hprod : (q * p : ℕ) ≤ (N : ℝ) ^ (x + y) := by
        rw [Nat.cast_mul, rpow_add hN0, mul_comm (q : ℝ)]
        exact mul_le_mul hp'.2.2.2.le hq'.2.2.2.le hq0.le (rpow_nonneg hN0.le _)
      apply hprod.trans_lt (rpow_lt_rpow_of_exponent_lt hNR ?_)
      exact hxy
    have hlpos : 0 < log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)) :=
      log_pos ((one_lt_div heR).mpr hup)
    have hlup : log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)) ≤
        (truncatedSixthLowerC δ - a - c) * log N := by
      have hlogprod := log_le_log (rpow_pos_of_pos hN0 _) hlo
      rw [log_rpow hN0] at hlogprod
      rw [log_div (rpow_pos_of_pos hN0 _).ne' heR.ne', log_rpow hN0]
      nlinarith
    have htpos : (0 : ℝ) < Nat.totient (q * p) := by exact_mod_cast Nat.totient_pos.mpr he0
    have htot : (Nat.totient (q * p) : ℝ) ≤ (q * p : ℕ) := by exact_mod_cast Nat.totient_le (q * p)
    have hCmul := wuSingularSeries_le_mul (N := N) (d := q * p) (by omega) he0
    have hCmul0 : 0 ≤ wuSingularSeries (q * p * N) := (hC.trans_le hCmul).le
    calc
      _ = wuSingularSeries N / ((q * p : ℕ) *
          ((truncatedSixthLowerC δ - a - c) * log N)) := by
            push_cast
            simp only [div_eq_mul_inv, mul_inv]
            ring
      _ ≤ _ := by
        change _ ≤ wuSingularSeries (q * p * N) /
          ((Nat.totient (q * p) : ℝ) * log ((N : ℝ) ^ truncatedSixthLowerC δ / (q * p : ℕ)))
        gcongr
  have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hli)
  simpa only [div_eq_mul_inv, mul_assoc] using h

theorem fifthH_mesh_theta_lower {N : ℕ} {δ a b c d : ℝ}
    (hN : 4 ≤ N) (hab : a ≤ b) (hcd : c ≤ d)
    (hbd : b + d < truncatedSixthLowerC δ) :
    (4 * logarithmicIntegral N * wuSingularSeries N /
      ((truncatedSixthLowerC δ - a - c) * log N)) *
      truncatedSixthMassPackingReciprocal N a b c d ≤
      truncatedSixthMassPackingTheta N δ a b c d := by
  unfold truncatedSixthMassPackingReciprocal truncatedSixthMassPackingTheta
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  have hN1 : 1 < N := by omega
  have hx := truncatedSixthMass_grid_point_bounds hN1 hab (mem_range.mp hj1)
  have hy := truncatedSixthMass_grid_point_bounds hN1 hcd (mem_range.mp hj2)
  apply fifthH_mesh_box_theta_lower hN ((add_le_add hx.2 hy.2).trans_lt hbd)
  · rw [truncatedSixthMass_grid_lower_endpoint hN1]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le) hx.1
  · rw [truncatedSixthMass_grid_lower_endpoint hN1]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1.le) hy.1

theorem fifthH_mesh_theta_sharp {δ a b c d ε : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (ha0 : 0 < a) (hc0 : 0 < c)
    (hbd : b + d < truncatedSixthLowerC δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (truncatedSixthMassRectangleCoefficient δ a b c d - ε) * truncatedSixthMassScale N ≤
        truncatedSixthMassPackingTheta N δ a b c d := by
  have hL1 : 0 ≤ log (b / a) := log_nonneg ((one_le_div ha0).mpr hab)
  have hL2 : 0 ≤ log (d / c) := log_nonneg ((one_le_div hc0).mpr hcd)
  have hD : 0 < truncatedSixthLowerC δ - a - c := by
    linarith
  let K := truncatedSixthMassRectangleCoefficient δ a b c d
  have hK : 0 ≤ K := by dsimp [K, truncatedSixthMassRectangleCoefficient]; positivity
  let τ := ε / (4 * (K + 1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : τ * (4 * (K + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hKτ : K * τ < ε / 2 := by nlinarith
  have hrat : K - ε / 2 < K / (1 + τ) := by
    apply (lt_div_iff₀ (by positivity : 0 < 1 + τ)).mpr
    nlinarith
  obtain ⟨T, hT4, hli⟩ := omega3X_trueLi_sharp_lower hτ
  have hmass := (truncatedSixthMass_packing_reciprocal_tendsto ha0 hab hc0 hcd).const_mul
    (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)))
  have hlimit : 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
      (log (b / a) * log (d / c)) = K / (1 + τ) := by
    dsimp [K, truncatedSixthMassRectangleCoefficient]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hlimit] at hmass
  have he := hmass.eventually (lt_mem_nhds (show K - ε < K / (1 + τ) by linarith))
  filter_upwards [he, eventually_ge_atTop T] with N hm hN
  have hN4 := hT4.trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_pos N (by omega)
  have hR : 0 ≤ truncatedSixthMassPackingReciprocal N a b c d := by
    unfold truncatedSixthMassPackingReciprocal
    exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    positivity
  change K - ε < 4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
    truncatedSixthMassPackingReciprocal N a b c d at hm
  calc
    _ ≤ (4 / ((1 + τ) * (truncatedSixthLowerC δ - a - c)) *
        truncatedSixthMassPackingReciprocal N a b c d) * truncatedSixthMassScale N :=
      mul_le_mul_of_nonneg_right hm.le hscale
    _ = (4 * wuSingularSeries N /
        ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) *
        truncatedSixthMassPackingReciprocal N a b c d) * ((N : ℝ) / log N) := by
      dsimp [truncatedSixthMassScale]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ ≤ (4 * wuSingularSeries N /
        ((1 + τ) * (truncatedSixthLowerC δ - a - c) * log N) *
        truncatedSixthMassPackingReciprocal N a b c d) * ((1 + τ) * logarithmicIntegral N) :=
      mul_le_mul_of_nonneg_left (hli N hN) (by positivity)
    _ = (4 * logarithmicIntegral N * wuSingularSeries N /
        ((truncatedSixthLowerC δ - a - c) * log N)) *
        truncatedSixthMassPackingReciprocal N a b c d := by field_simp
    _ ≤ _ := fifthH_mesh_theta_lower hN4 hab hcd hbd

/-- A genuinely new original exponent-cell bound.  Its s is the old upper
corner parameter, fixed before T.  No covering, source-box, mass or count
bound is an input.  Terminal strips are paid by `fifthH_mesh_theta_sharp`. -/
theorem fifthH_inner_cell_count {δ η ε : ℝ} {n : ℕ} {j : ℕ × ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hε : 0 < ε)
    (hj : j ∈ fifthPairInner n) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (max 0 (wuLowerCoefficient (truncatedSixthLowerS δ
          (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2)) +
        (wuImprovementLimit false δ (truncatedSixthLowerS δ
          (truncatedSixthClosureHi n j.1) (truncatedSixthClosureHi n j.2)) - η)) *
        truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N ≤
      truncatedSixthClosureCount N
        (truncatedSixthClosureLo n j.1) (truncatedSixthClosureHi n j.1)
        (truncatedSixthClosureLo n j.2) (truncatedSixthClosureHi n j.2) := by
  let s := truncatedSixthLowerS δ (truncatedSixthClosureHi n j.1)
    (truncatedSixthClosureHi n j.2)
  let L := wuLowerCoefficient s + (wuImprovementLimit false δ s - η)
  change ∀ᶠ N : ℕ in atTop, Even N →
    (max 0 L * truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N ≤ _
  by_cases hL : L ≤ 0
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN _
    rw [max_eq_left hL, zero_mul, zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le)
      (truncatedSixthClosure_scale_nonneg hN)).trans
      (truncatedSixthClosure_count_nonneg _ _ _ _ _)
  · have hL0 : 0 < L := lt_of_not_ge hL
    have hg := fifthPair_inner_geometry hj
    have hab := (truncatedSixthClosure_lo_lt_hi n j.1).le
    have hcd := (truncatedSixthClosure_lo_lt_hi n j.2).le
    have hs := fifthPair_triangle_bounds hδ.le hδhi (hg.1.trans hab)
      (hg.2.1.trans hcd) hg.2.2
    obtain ⟨T, hT4, hraw⟩ := fifthH_mesh_raw hδ hδhi hη hab hg.2.1 hcd hg.1
      hg.2.2 (by dsimp [s]; linarith [hs.2.2.1] : 1 ≤ s)
      (by dsimp [s]; linarith [hs.2.2.2.1] : s ≤ 10) (le_refl s)
    filter_upwards [eventually_ge_atTop T,
      fifthH_mesh_theta_sharp hab hcd
        (truncatedSixthLower_parameters.1.trans_le hg.1)
        (truncatedSixthLower_parameters.1.trans_le (hg.1.trans (hab.trans hg.2.1)))
        (fifthPair_inner_level hδ.le hδhi hj)
        (show 0 < ε / L by positivity)] with N hN hm he
    have hact := hraw N hN he
    have hmass := mul_le_mul_of_nonneg_left hm hL0.le
    have heq : L * ((truncatedSixthClosureRcoef δ n j - ε / L) *
        truncatedSixthMassScale N) =
        (L * truncatedSixthClosureRcoef δ n j - ε) * truncatedSixthMassScale N := by
      field_simp
    change L * ((truncatedSixthClosureRcoef δ n j - ε / L) *
      truncatedSixthMassScale N) ≤ _ at hmass
    rw [heq] at hmass
    rw [max_eq_right hL0.le]
    exact hmass.trans hact

end Wu2008DoubleSieve
