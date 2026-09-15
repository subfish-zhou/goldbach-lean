import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAHighSSourceLarge

open scoped Classical BigOperators
open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-- The high-coordinate cutoff `sqrt K / log K` eventually exceeds any fixed
Section-13 threshold.  The threshold is chosen before all later parameters. -/
theorem claim145_sqrt_div_log_eventually_ge (M : ℝ) :
    ∀ᶠ K : ℝ in atTop, max M 4 ≤ Real.sqrt K / Real.log K := by
  let A : ℝ := max M 4
  have hA : 0 ≤ A := by dsimp [A]; exact le_trans (by norm_num) (le_max_right M 4)
  have hlo :=
    (isLittleO_log_rpow_rpow_atTop 1 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / (A + 1) by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with K hloK hlogK1 hK0
  have hlogK : 0 < Real.log K := zero_lt_one.trans_le hlogK1
  change |Real.log K ^ (1 : ℝ)| ≤
    1 / (A + 1) * |K ^ (1 / 2 : ℝ)| at hloK
  rw [Real.rpow_one, abs_of_nonneg hlogK.le,
    abs_of_nonneg (Real.rpow_nonneg hK0.le _), ← Real.sqrt_eq_rpow] at hloK
  have hscaled := mul_le_mul_of_nonneg_left hloK hA
  have hfrac : A * (1 / (A + 1)) ≤ 1 := by
    rw [div_eq_mul_inv, ← mul_assoc]
    exact (div_le_one (by positivity : 0 < A + 1)).2 (by linarith)
  have hmain : A * Real.log K ≤ Real.sqrt K := by
    calc
      A * Real.log K ≤ (A * (1 / (A + 1))) * Real.sqrt K := by
        nlinarith
      _ ≤ 1 * Real.sqrt K :=
        mul_le_mul_of_nonneg_right hfrac (Real.sqrt_nonneg K)
      _ = Real.sqrt K := one_mul _
  exact (le_div_iff₀ hlogK).2 hmain

/-- Actual high-`s` producer for source Case A.  Proposition 13.1(ii) supplies
its uniform lower-profile constants first; one subsequent `K` threshold then
works for every `K`, depth `N`, natural cutoff `D`, and coordinate `s`. -/
theorem claim145_caseA_highS_actual_uniform_in_S
    (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ S : BoundingSieve,
      Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 1 := by
  obtain ⟨C, M, hC, hM3, hprop⟩ :=
    proposition131iiUniformQuantitativeLower_of_source hH
  have hsource := claim145_caseA_highS_sourceLarge_eventually hC1 hΘ
  have habsorb := claim145_caseA_highS_habsorb_eventually_uniform_in_S
    (d := d) (Δ := Δ) (C1 := C1) (Θ := Θ) (C := C)
      hC1 hΘ hΔ0 hΔ1 hgap
  let A : ℝ := Θ + 2 + |Real.log C1| + |Real.log (Real.log 2)|
  have hA : 0 < A := by
    dsimp [A]
    linarith [abs_nonneg (Real.log C1), abs_nonneg (Real.log (Real.log 2))]
  have hcoordinate := claim145_sqrt_div_log_eventually_ge (max M (Real.exp A / 3))
  have hclosed : ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧
      ∀ (S : BoundingSieve) (N D : ℕ) (s : ℝ),
        HasDimensionOneLocalProductBound S K →
        2 ≤ D → 2 ≤ s → Real.sqrt K / Real.log K ≤ s →
        Real.log (D : ℝ) ≤ C1 * K ^ Θ →
        ActualClaim145BoundAt S H N D d Δ K s 1 := by
    filter_upwards [hsource, habsorb, hcoordinate,
      eventually_ge_atTop (3 : ℝ)] with K hsourceK habsorbK hcoordinateK hK3
    refine ⟨hsourceK.1, ?_⟩
    intro S N D s hlocal hD hs hsqrt hsmall
    have hs4 : 4 ≤ s :=
      (le_max_right (max M (Real.exp A / 3)) 4).trans (hcoordinateK.trans hsqrt)
    have hMs : M ≤ s :=
      (le_max_left M (Real.exp A / 3)).trans
        ((le_max_left (max M (Real.exp A / 3)) 4).trans (hcoordinateK.trans hsqrt))
    have hexpAs : Real.exp A / 3 ≤ s :=
      (le_max_right M (Real.exp A / 3)).trans
        ((le_max_left (max M (Real.exp A / 3)) 4).trans (hcoordinateK.trans hsqrt))
    have hsourceLarge := hsourceK.2 D s hD hs hsqrt hsmall
    have hL1 : 1 ≤ suzukiSourceL (D : ℝ) K := by
      have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogD : Real.log 2 ≤ Real.log (D : ℝ) :=
        Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 2 by norm_num)
          (lt_of_lt_of_le (by norm_num) hDreal) hDreal
      have hfirst : 0 ≤ Real.log (Real.log (D : ℝ) / Real.log 2) := by
        exact Real.log_nonneg ((le_div_iff₀ hlog2).2 (by simpa using hlogD))
      have hlog2le : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hK0 : 0 ≤ K := by linarith
      have hKdiv : K ≤ K / Real.log 2 := by
        exact (le_div_iff₀ hlog2).2 (mul_le_of_le_one_right hK0 hlog2le)
      have hexp : Real.exp 1 ≤ 1 + K / Real.log 2 := by
        linarith [Real.exp_one_lt_three]
      have hsecond : 1 ≤ Real.log (1 + K / Real.log 2) := by
        simpa only [Real.log_exp] using
          Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
            ((Real.exp_pos 1).trans_le hexp) hexp
      unfold suzukiSourceL
      linarith
    have hLprod : suzukiSourceL (D : ℝ) K ≤
        Real.log (3 * K) * Real.log (3 * s) := by
      have hlogK1 : 1 ≤ Real.log K := by
        have hexpK : Real.exp 1 ≤ K := le_trans Real.exp_one_lt_three.le hK3
        simpa only [Real.log_exp] using
          Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
            ((Real.exp_pos 1).trans_le hexpK) hexpK
      have hLD := claim145_caseA_highS_sourceL_le_logK
        (D := (D : ℝ)) (K := K) (C1 := C1) (Θ := Θ)
        (by exact_mod_cast hD) hK3 hlogK1 hC1 hΘ hsmall
      have hexpAle : Real.exp A ≤ 3 * s := by nlinarith
      have hAlog : A ≤ Real.log (3 * s) := by
        simpa only [Real.log_exp] using
          Real.strictMonoOn_log.monotoneOn (Real.exp_pos A)
            ((Real.exp_pos A).trans_le hexpAle) hexpAle
      have hlogK0 : 0 ≤ Real.log K := zero_le_one.trans hlogK1
      have hlog3s0 : 0 ≤ Real.log (3 * s) :=
        Real.log_nonneg (by nlinarith)
      have hlogK3 : Real.log K ≤ Real.log (3 * K) := by
        have hKpos : 0 < K := by linarith
        exact Real.strictMonoOn_log.monotoneOn hKpos
          (show 0 < 3 * K by nlinarith) (by nlinarith)
      calc
        suzukiSourceL (D : ℝ) K ≤ A * Real.log K := by simpa [A] using hLD
        _ ≤ Real.log (3 * s) * Real.log K :=
          mul_le_mul_of_nonneg_right hAlog hlogK0
        _ ≤ Real.log (3 * s) * Real.log (3 * K) :=
          mul_le_mul_of_nonneg_left hlogK3 hlog3s0
        _ = Real.log (3 * K) * Real.log (3 * s) := by ring
    have hscalar := habsorbK.2 S (D : ℝ) s hlocal
      (by exact_mod_cast hD) hs4 hsqrt hsmall hL1 hsourceLarge hLprod
    exact suzukiLemma14_3_le_claim145Scale_of_scalar_at
      (σ := sourceSigma (D : ℝ) d) (C := C) (M := M) (C145 := 1)
      S H hlocal hD (sourceSigma_pos_of_nat_two_le hD) hs hMs
      (by linarith) (by norm_num) hprop hsourceLarge
      (by simpa only [one_mul] using hscalar)
  rcases eventually_atTop.1 hclosed with ⟨K0, hK0⟩
  refine ⟨max 2 K0, le_max_left _ _, ?_⟩
  intro S K N D s hK hlocal hD hs hsqrt hsmall
  exact (hK0 K ((le_max_right 2 K0).trans hK)).2 S N D s
    hlocal hD hs hsqrt hsmall

/-- Compatibility specialization of the uniform high-coordinate leaf. -/
theorem claim145_caseA_highS_actual
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧
      Claim145CaseALargeKHighSClosed S H d Δ C1 Θ K0 1 := by
  obtain ⟨K0, hK0, hall⟩ :=
    claim145_caseA_highS_actual_uniform_in_S H hH hC1 hΘ hΔ0 hΔ1 hgap
  exact ⟨K0, hK0, hall S⟩

/-- Public `Claim14_5Bound` spelling of the same actual producer. -/
theorem exists_claim145_caseA_highS_actual_claim14_5Bound
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 < C1) (hΘ : 0 ≤ Θ)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hgap : 0 < d - 2 * Θ) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∃ K0 : ℝ, 2 ≤ K0 ∧
        ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
          K0 ≤ K → HasDimensionOneLocalProductBound S K →
          2 ≤ D → 2 ≤ s → Real.sqrt K / Real.log K ≤ s →
          Real.log (D : ℝ) ≤ C1 * K ^ Θ →
          Claim14_5Bound
            (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
            S H N (D : ℝ) (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s C145 := by
  obtain ⟨K0, hK0, hclosed⟩ :=
    claim145_caseA_highS_actual S H hH hC1 hΘ hΔ0 hΔ1 hgap
  refine ⟨1, by norm_num, K0, hK0, ?_⟩
  intro K N D s hK hlocal hD hs hsqrt hsmall
  simpa only [ActualClaim145BoundAt, Claim14_5Bound, Nat.ceil_natCast] using
    hclosed K N D s hK hlocal hD hs hsqrt hsmall


end MathlibNt.SieveTheory
