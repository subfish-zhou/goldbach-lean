import MathlibNt.SieveTheory.Switching.ResidualBounds

/-!
# Screened residual comparison at arbitrary depth

The full screened residual comparison and continuous outer-mass estimates
yield integral majorants for fixed-depth boundary contributions.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- Fixed-depth residual comparisons for every positive screen.  Internally a
smaller screen below one is used when necessary; strengthening the screen then
gives the stated predicate. -/
theorem exists_upperRosserBoundaryScreenedResidualComparison
    (k : ℕ) (K ρ c s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (q : ℕ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        UpperRosserBoundaryScreenedResidualComparison S z q k ρ c s₁ := by
  let d : ℝ := min c (1 / 2)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hc (by norm_num)
  have hd1 : d < 1 :=
    (min_le_right c (1 / 2)).trans_lt (by norm_num)
  obtain ⟨z₀, hz₀, hcomparison⟩ :=
    exists_upperRosserBoundaryScreenedResidualComparison_of_lt_one
      k K ρ d s₁ hK hρ hd hd1
  refine ⟨z₀, hz₀, ?_⟩
  intro S z q hz hlocal
  exact UpperRosserBoundaryScreenedResidualComparison.mono
    (min_le_left c (1 / 2)) (hcomparison S z q hz hlocal)

/-- Uniform fixed-depth comparison on a positive bounded level range.  The
strict inherited face and its bound by one already force every prime in the
carrier below the ambient cutoff `z`. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMassAux_add
    (k : ℕ) (K ρ c s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s b : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ∈ Set.Ioc 0 s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) →
        (∀ p ∈ P, Real.log p / Real.log z < b) →
        c ≤ Real.log q / Real.log z → b ≤ 1 →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P k ≤
          LinearSieve.upperRosserBoundaryMassAux k s
            (Real.log q / Real.log z) b + ρ := by
  obtain ⟨z₀, hz₀, hcomparison⟩ :=
    exists_upperRosserBoundaryScreenedResidualComparison k K ρ c s₁ hK hρ hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s b q P hz hΔ hlocal hs hsRange hqprime hqs hP hqmin hupper
    hqscreen hb
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz)
  have hΔone : 1 < Δ := by
    have hlogΔpos : 0 < Real.log Δ :=
      (div_pos_iff_of_pos_right (Real.log_pos hz1)).mp (hs ▸ hsRange.1)
    exact (Real.log_pos_iff hΔ.le).mp hlogΔpos
  exact hcomparison S z q hz hlocal hΔone hs hsRange.2 hP hqs hqprime
    (fun p hp => Nat.prime_of_mem_primeFactors (hP hp)) hqmin hupper hqscreen hb

/-- Fixed-depth comparison at the lower screen forced by a nonzero outer
depth-`k` contribution. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMassAux_add_depth_screen
    (k : ℕ) (K ρ s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s b : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ∈ Set.Ioc 0 s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) →
        (∀ p ∈ P, Real.log p / Real.log z < b) →
        (1 / (2 * (3 : ℝ) ^ k) : ℝ) ≤ Real.log q / Real.log z → b ≤ 1 →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P k ≤
          LinearSieve.upperRosserBoundaryMassAux k s
            (Real.log q / Real.log z) b + ρ :=
  exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMassAux_add
    k K ρ (1 / (2 * (3 : ℝ) ^ k)) s₁ hK hρ (by positivity)

/-- The depth-dependent pointwise comparison at upper face `1` remains valid
when the carrier is only known to lie in the closed cutoff `p ≤ z`.  The proof
approaches `z` from above, where the inherited face is strict, and uses
positive-depth continuity; depth zero is exact. -/
theorem
    exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMass_add_depth_screen
    (k : ℕ) (K ρ s₁ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ) (q : ℕ) (P : Finset ℕ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        s = Real.log Δ / Real.log z → s ∈ Set.Ioc 0 s₁ →
        q.Prime → q ∉ P → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q ≤ p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        (1 / (2 * (3 : ℝ) ^ k) : ℝ) < Real.log q / Real.log z →
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q P k ≤
          LinearSieve.upperRosserBoundaryMass k s
            (Real.log q / Real.log z) + ρ := by
  cases k with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro S z Δ s q P hz hΔ hlocal hs hsRange hqprime hqs hP hqmin hPcut
        hqscreen
      have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz
      have hΔone : 1 < Δ := by
        have hlogΔpos : 0 < Real.log Δ :=
          (div_pos_iff_of_pos_right (Real.log_pos hz1)).mp (hs ▸ hsRange.1)
        exact (Real.log_pos_iff hΔ.le).mp hlogΔpos
      have hD : 1 < Nat.floor Δ + 1 := by
        have hone : ((1 : ℕ) : ℝ) ≤ Δ := by simpa using hΔone.le
        have : 1 ≤ Nat.floor Δ := Nat.le_floor hone
        omega
      have hbase :=
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_zero_le_boundaryMassAux
          (fun p => S.nu p / (1 - S.nu p))
          (z := z) (Δ := Δ) (s := s)
          (a := Real.log q / Real.log z) (b := 1)
          (D := Nat.floor Δ + 1) hz1 hΔ hs rfl hsRange.1.le rfl hD hqs
          hqprime hqmin
      calc
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p))
              (Nat.floor Δ + 1) q P 0 ≤
            LinearSieve.upperRosserBoundaryMass 0 s
              (Real.log q / Real.log z) := hbase
        _ ≤ LinearSieve.upperRosserBoundaryMass 0 s
              (Real.log q / Real.log z) + ρ := le_add_of_nonneg_right hρ.le
  | succ k =>
      obtain ⟨z₀, hz₀, hcomparison⟩ :=
        exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMassAux_add_depth_screen
          (k + 1) K ρ s₁ hK hρ
      refine ⟨z₀, hz₀, ?_⟩
      intro S z Δ s q P hz hΔ hlocal hs hsRange hqprime hqs hP hqmin hPcut
        hqscreen
      have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz)
      have hzpos : 0 < z := by linarith
      have hlogz : 0 < Real.log z := Real.log_pos hz1
      have hlogΔ : 0 < Real.log Δ :=
        (div_pos_iff_of_pos_right (hlogz)).mp (hs ▸ hsRange.1)
      let l : Filter ℝ := nhdsWithin z (Set.Ioi z)
      have hlevelT :
          Filter.Tendsto (fun Z : ℝ => Real.log Δ / Real.log Z) l (nhds s) := by
        have hcont :
            ContinuousAt (fun Z : ℝ => Real.log Δ / Real.log Z) z :=
          continuousAt_const.div₀ (Real.continuousAt_log hzpos.ne') hlogz.ne'
        change Filter.Tendsto (fun Z : ℝ => Real.log Δ / Real.log Z)
          (nhds z ⊓ Filter.principal (Set.Ioi z)) (nhds s)
        rw [hs]
        exact hcont.tendsto.mono_left inf_le_left
      have houterT :
          Filter.Tendsto (fun Z : ℝ => Real.log q / Real.log Z) l
            (nhds (Real.log q / Real.log z)) := by
        have hcont :
            ContinuousAt (fun Z : ℝ => Real.log q / Real.log Z) z :=
          continuousAt_const.div₀ (Real.continuousAt_log hzpos.ne') hlogz.ne'
        change Filter.Tendsto (fun Z : ℝ => Real.log q / Real.log Z)
          (nhds z ⊓ Filter.principal (Set.Ioi z))
          (nhds (Real.log q / Real.log z))
        exact hcont.tendsto.mono_left inf_le_left
      have hscreenEventually :
          ∀ᶠ Z in l,
            (1 / (2 * (3 : ℝ) ^ (k + 1)) : ℝ) ≤
              Real.log q / Real.log Z := by
        exact (houterT.eventually (Ioi_mem_nhds hqscreen)).mono
          (fun _ h => h.le)
      have hqapos : 0 < Real.log q / Real.log z :=
        (by positivity :
          (0 : ℝ) < 1 / (2 * (3 : ℝ) ^ (k + 1))).trans hqscreen
      have hpairT :
          Filter.Tendsto
            (fun Z : ℝ =>
              (Real.log Δ / Real.log Z, Real.log q / Real.log Z)) l
            (nhds (s, Real.log q / Real.log z)) := by
        simpa only [nhds_prod_eq] using hlevelT.prodMk houterT
      have hmassT :
          Filter.Tendsto
            (fun Z : ℝ =>
              LinearSieve.upperRosserBoundaryMass (k + 1)
                (Real.log Δ / Real.log Z) (Real.log q / Real.log Z)) l
            (nhds (LinearSieve.upperRosserBoundaryMass (k + 1) s
              (Real.log q / Real.log z))) := by
        unfold LinearSieve.upperRosserBoundaryMass
        exact
          (LinearSieve.continuousAt_upperRosserBoundaryMassAux_level_lower_succ
            k hqapos (show (1 : ℝ) ≤ 1 from le_rfl)).tendsto.comp hpairT
      have hboundEventually :
          ∀ᶠ Z in l,
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p))
                (Nat.floor Δ + 1) q P (k + 1) ≤
              LinearSieve.upperRosserBoundaryMass (k + 1)
                  (Real.log Δ / Real.log Z) (Real.log q / Real.log Z) + ρ := by
        filter_upwards [self_mem_nhdsWithin, hscreenEventually] with Z hZ hqscreenZ
        have hzZ : z₀ ≤ Z := hz.trans hZ.le
        have hZ1 : 1 < Z := hz1.trans hZ
        have hlogZ : 0 < Real.log Z := Real.log_pos hZ1
        have hlevelLe :
            Real.log Δ / Real.log Z ≤ s := by
          rw [hs]
          exact div_le_div_of_nonneg_left hlogΔ.le hlogz
            (Real.strictMonoOn_log.monotoneOn hzpos (hzpos.trans hZ) hZ.le)
        have hlevelRange :
            Real.log Δ / Real.log Z ∈ Set.Ioc 0 s₁ :=
          ⟨div_pos hlogΔ hlogZ, hlevelLe.trans hsRange.2⟩
        have hupper :
            ∀ p ∈ P, Real.log p / Real.log Z < (1 : ℝ) := by
          intro p hp
          have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
          have hppos : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
          have hpZ : (p : ℝ) < Z := (hPcut p hp).trans_lt hZ
          rw [div_lt_one hlogZ]
          exact (Real.strictMonoOn_log.lt_iff_lt hppos (hzpos.trans hZ)).2 hpZ
        simpa [LinearSieve.upperRosserBoundaryMass] using
          hcomparison S Z Δ (Real.log Δ / Real.log Z) 1 q P hzZ hΔ hlocal
            rfl hlevelRange hqprime hqs hP hqmin hupper hqscreenZ le_rfl
      exact le_of_tendsto_of_tendsto tendsto_const_nhds
        (hmassT.add tendsto_const_nhds) hboundEventually

/-- At every positive fixed depth, the continuous outer boundary mass admits a
uniform Stieltjes transfer on `3 / 2 ≤ s ≤ 4`.  Joint continuity on the compact
level/cutoff box supplies the common mesh modulus. -/
theorem
    exists_sum_nu_div_one_sub_mul_inv_mul_upperRosserBoundaryMass_succ_le_integral_add
    (k : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z s : ℝ) (T : Finset ℕ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T,
          Real.log p / Real.log z ∈
            Set.Icc (1 / (2 * (3 : ℝ) ^ (k + 1))) 1) →
        s ∈ Set.Icc (3 / 2 : ℝ) 4 →
        ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
          ((Real.log p / Real.log z)⁻¹ *
            LinearSieve.upperRosserBoundaryMass (k + 1) s
              (Real.log p / Real.log z)) ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass (k + 1) s a) + ρ := by
  let c : ℝ := 1 / (2 * (3 : ℝ) ^ (k + 1))
  let B : ℝ := c⁻¹ * (c⁻¹ * c⁻¹) ^ (k + 1)
  let F : ℝ × ℝ → ℝ := fun p =>
    p.2⁻¹ * LinearSieve.upperRosserBoundaryMass (k + 1) p.1 p.2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c < 1 := by
    dsimp [c]
    have hpow : (1 : ℝ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * 3 ^ (k + 1))]
    nlinarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hFcont : ContinuousOn F
      (Set.Icc (3 / 2 : ℝ) 4 ×ˢ Set.Icc c 1) := by
    have hinv : ContinuousOn (fun p : ℝ × ℝ => p.2⁻¹)
        (Set.Icc (3 / 2 : ℝ) 4 ×ˢ Set.Icc c 1) := by
      apply continuousOn_snd.inv₀
      intro p hp
      exact (hc.trans_le hp.2.1).ne'
    have hmass : ContinuousOn
        (fun p : ℝ × ℝ =>
          LinearSieve.upperRosserBoundaryMass (k + 1) p.1 p.2)
        (Set.Icc (3 / 2 : ℝ) 4 ×ˢ Set.Icc c 1) := by
      simpa [LinearSieve.upperRosserBoundaryMass] using
        (LinearSieve.continuousOn_upperRosserBoundaryMassAux_level_lower_succ
          k (b := 1) (r₀ := (3 / 2 : ℝ)) (r₁ := 4) (c := c) le_rfl hc)
    exact hinv.mul hmass
  let ε : ℝ := ρ * c / 12
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have huniform :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hFcont
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform ε hε
  obtain ⟨z₀, hz₀, houter⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add_screened_of_uniform_modulus
      K ρ B c δ hK hρ hB hc hc1 hδ
  refine ⟨z₀, hz₀, ?_⟩
  intro S z s T hz hlocal hT hcoord hs
  let f : ℝ → ℝ := fun a =>
    a⁻¹ * LinearSieve.upperRosserBoundaryMass (k + 1) s a
  have hf : ∀ x ∈ Set.Icc c 1, 0 ≤ f x := by
    intro x hx
    exact mul_nonneg (inv_nonneg.mpr (hc.le.trans hx.1))
      (LinearSieve.upperRosserBoundaryMass_nonneg (k + 1)
        (hc.le.trans hx.1))
  have hfB : ∀ x ∈ Set.Icc c 1, f x ≤ B := by
    intro x hx
    have hxpos : 0 < x := hc.trans_le hx.1
    have hxinv : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 hx.1
    dsimp [f, B]
    calc
      x⁻¹ * LinearSieve.upperRosserBoundaryMass (k + 1) s x ≤
          x⁻¹ * (x⁻¹ * x⁻¹) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left
          (LinearSieve.upperRosserBoundaryMass_le_inv_sq_pow
            (k + 1) hxpos)
          (inv_nonneg.mpr hxpos.le)
      _ ≤ c⁻¹ * (c⁻¹ * c⁻¹) ^ (k + 1) := by
        gcongr
  have hfmod : ∀ x ∈ Set.Icc c 1, ∀ y ∈ Set.Icc c 1,
      |x - y| < δ → |f x - f y| < ρ * c / 12 := by
    intro x hx y hy hxy
    have hdist : dist (s, x) (s, y) < δ := by
      simpa [Prod.dist_eq, Real.dist_eq] using hxy
    have hclose := hmod (s, x) ⟨hs, hx⟩ (s, y) ⟨hs, hy⟩ hdist
    simpa [F, f, ε, Real.dist_eq] using hclose
  have hint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * f x) (Set.Ioo c 1) := by
    simpa [f, mul_assoc] using
      LinearSieve.integrableOn_inv_sq_mul_upperRosserBoundaryMass
        (k + 1) s hc
  have hcomparison :=
    houter S z T
      (fun p => f (Real.log p / Real.log z)) f hz hlocal hT hcoord
      hf hfB hfmod hint (by
        intro p hp
        exact ⟨hf _ (hcoord p hp), le_rfl⟩)
  calc
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        ((Real.log p / Real.log z)⁻¹ *
          LinearSieve.upperRosserBoundaryMass (k + 1) s
            (Real.log p / Real.log z)) =
        ∑ p ∈ T, f (Real.log p / Real.log z) *
          (S.nu p / (1 - S.nu p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [f]
      ring
    _ ≤ (∫ x in Set.Ioo c 1, x⁻¹ * f x) + ρ := hcomparison
    _ = (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass (k + 1) s a) + ρ := by
      rw [LinearSieve.integral_upperRosserBoundaryMass_eq_integral_fixedDepthSupport
        (k + 1) hs.1]
      simp only [c, f, mul_assoc]

/-- Every positive fixed-depth complete outer Rosser contribution converges
uniformly on the upper-sieve range to its continuous boundary integral. -/
theorem
    exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ_le_integral_add_of_three_halves_le
    (k : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1) ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass (k + 1) s a) + ρ := by
      let c : ℝ := 1 / (2 * (3 : ℝ) ^ (k + 1))
      let A : ℝ := c⁻¹ + 1
      let ε : ℝ := ρ / (2 * A)
      have hc : 0 < c := by
        dsimp [c]
        positivity
      have hc1 : c < 1 := by
        dsimp [c]
        have hpow : (1 : ℝ) ≤ 3 ^ (k + 1) := one_le_pow₀ (by norm_num)
        rw [div_lt_one (by positivity : (0 : ℝ) < 2 * 3 ^ (k + 1))]
        nlinarith
      have hA : 0 < A := by
        dsimp [A]
        positivity
      have hε : 0 < ε := div_pos hρ (mul_pos (by norm_num) hA)
      obtain ⟨zPoint, hzPoint, hpoint⟩ :=
        exists_upperRosserBoundaryChainsFixedDepthDensity_le_boundaryMass_add_depth_screen
          (k + 1) K ε 4 hK hε
      obtain ⟨zOuter, hzOuter, houter⟩ :=
        exists_sum_nu_div_one_sub_mul_inv_mul_upperRosserBoundaryMass_succ_le_integral_add
          k K (ρ / 2) hK (half_pos hρ)
      obtain ⟨zMass, hzMass, hmass⟩ :=
        exists_weighted_sum_nu_div_one_sub_le_integral_add_screened
          K 1 1 0 c hK (by norm_num) (by norm_num) (by norm_num) hc hc1
      let z₀ : ℝ := max zPoint (max zOuter zMass)
      refine ⟨z₀, hzPoint.trans (le_max_left _ _), ?_⟩
      intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
      have hzPointZ : zPoint ≤ z := (le_max_left _ _).trans hz
      have hzOuterZ : zOuter ≤ z :=
        (le_max_left zOuter zMass).trans ((le_max_right _ _).trans hz)
      have hzMassZ : zMass ≤ z :=
        (le_max_right zOuter zMass).trans ((le_max_right _ _).trans hz)
      have hz2 : 2 ≤ z := hzPoint.trans hzPointZ
      have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz2
      have hzpos : 0 < z := by linarith
      have hlogz : 0 < Real.log z := Real.log_pos hz1
      let Q : Finset ℕ :=
        S.prodPrimes.primeFactors.filter
          (fun q : ℕ => c < Real.log q / Real.log z)
      have hQ : Q ⊆ S.prodPrimes.primeFactors := by
        intro q hq
        exact (Finset.mem_filter.mp hq).1
      have hQcoord : ∀ q ∈ Q,
          Real.log q / Real.log z ∈ Set.Icc c 1 := by
        intro q hq
        have hq' := Finset.mem_filter.mp hq
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
        refine ⟨hq'.2.le, ?_⟩
        rw [div_le_one hlogz]
        exact Real.strictMonoOn_log.monotoneOn hqpos hzpos (hcut q hq'.1)
      have hinv : MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹)
          (Set.Ioo c 1) := by
        apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hc1.le).1
        apply intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x)
        · intro x hx
          rw [Set.uIcc_of_le hc1.le] at hx
          exact (hc.trans_le hx.1).ne'
        · exact continuous_id.continuousOn
      have hinvIntegralLe :
          (∫ x : ℝ in Set.Ioo c 1, x⁻¹) ≤ c⁻¹ := by
        have hfinite : MeasureTheory.volume (Set.Ioo c 1) ≠ ⊤ := by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top
        have hconst :
            MeasureTheory.IntegrableOn (fun _ : ℝ => c⁻¹) (Set.Ioo c 1) :=
          MeasureTheory.integrableOn_const hfinite
        calc
          (∫ x : ℝ in Set.Ioo c 1, x⁻¹) ≤
              ∫ _x : ℝ in Set.Ioo c 1, c⁻¹ := by
            apply MeasureTheory.setIntegral_mono_on hinv hconst measurableSet_Ioo
            intro x hx
            exact (inv_le_inv₀ (hc.trans hx.1) hc).2 hx.1.le
          _ = (1 - c) * c⁻¹ := by
            rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
              Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hc1.le)]
            rfl
          _ ≤ c⁻¹ :=
            mul_le_of_le_one_left (inv_nonneg.mpr hc.le) (sub_le_self _ hc.le)
      have hmassComparison :=
        hmass S z Q (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
          hzMassZ hlocal hQ hQcoord
          (by intro x hx; norm_num)
          (by intro x hx; norm_num)
          (by intro x hx y hy; norm_num)
          (by simpa using hinv)
          (by intro q hq; exact ⟨by norm_num, le_rfl⟩)
      have hQmass :
          ∑ q ∈ Q, S.nu q / (1 - S.nu q) ≤ A := by
        calc
          ∑ q ∈ Q, S.nu q / (1 - S.nu q) =
              ∑ q ∈ Q, (1 : ℝ) * (S.nu q / (1 - S.nu q)) := by simp
          _ ≤ (∫ x in Set.Ioo c 1, x⁻¹ * (1 : ℝ)) + 1 :=
            hmassComparison
          _ ≤ A := by
            simp only [mul_one]
            dsimp [A]
            linarith
      have hpointwise : ∀ q ∈ Q,
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p))
              (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1) ≤
            LinearSieve.upperRosserBoundaryMass (k + 1) s
              (Real.log q / Real.log z) + ε := by
        intro q hq
        have hq' := Finset.mem_filter.mp hq
        let P : Finset ℕ :=
          S.prodPrimes.primeFactors.filter (fun p => q < p)
        apply hpoint S z Δ s q P hzPointZ hΔ hlocal hs
          ⟨by linarith, hsupper⟩
          (Nat.prime_of_mem_primeFactors hq'.1)
        · simp [P]
        · intro p hp
          exact (Finset.mem_filter.mp hp).1
        · intro p hp
          exact (Finset.mem_filter.mp hp).2.le
        · intro p hp
          exact hcut p (Finset.mem_filter.mp hp).1
        · simpa [c] using hq'.2
      have hpointwiseSum :
          (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p))
              (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1)) ≤
            ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
              (LinearSieve.upperRosserBoundaryMass (k + 1) s
                (Real.log q / Real.log z) + ε) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (hpointwise q hq)
          (nu_div_one_sub_nonneg_of_mem (hQ hq))
      have hmassToInv :
          (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
            LinearSieve.upperRosserBoundaryMass (k + 1) s
              (Real.log q / Real.log z)) ≤
            ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
              ((Real.log q / Real.log z)⁻¹ *
                LinearSieve.upperRosserBoundaryMass (k + 1) s
                  (Real.log q / Real.log z)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqcoord := hQcoord q hq
        have hqpos : 0 < Real.log q / Real.log z := hc.trans_le hqcoord.1
        apply mul_le_mul_of_nonneg_left
        · calc
            LinearSieve.upperRosserBoundaryMass (k + 1) s
                (Real.log q / Real.log z) =
                1 * LinearSieve.upperRosserBoundaryMass (k + 1) s
                  (Real.log q / Real.log z) := by ring
            _ ≤ (Real.log q / Real.log z)⁻¹ *
                LinearSieve.upperRosserBoundaryMass (k + 1) s
                  (Real.log q / Real.log z) :=
              mul_le_mul_of_nonneg_right
                ((one_le_inv₀ hqpos).2 hqcoord.2)
                (LinearSieve.upperRosserBoundaryMass_nonneg (k + 1) hqpos.le)
        · exact nu_div_one_sub_nonneg_of_mem (hQ hq)
      have houterBound :=
        houter S z s Q hzOuterZ hlocal hQ hQcoord ⟨hslo, hsupper⟩
      have herror : ε * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) ≤ ρ / 2 := by
        calc
          ε * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) ≤ ε * A :=
            mul_le_mul_of_nonneg_left hQmass hε.le
          _ = ρ / 2 := by
            dsimp [ε]
            field_simp [hA.ne']
      rw [sum_mul_upperRosserBoundaryChainsFixedDepthDensity_eq_screened
        (fun p => S.nu p / (1 - S.nu p))
        (fun p => S.nu p / (1 - S.nu p)) (k + 1) hz2 hΔ hs hslo hcut]
      change (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p))
          (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1)) ≤ _
      calc
        (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) (k + 1)) ≤
            ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
              (LinearSieve.upperRosserBoundaryMass (k + 1) s
                (Real.log q / Real.log z) + ε) := hpointwiseSum
        _ = (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
              LinearSieve.upperRosserBoundaryMass (k + 1) s
                (Real.log q / Real.log z)) +
            ε * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ ≤ (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
              ((Real.log q / Real.log z)⁻¹ *
                LinearSieve.upperRosserBoundaryMass (k + 1) s
                  (Real.log q / Real.log z))) + ρ / 2 :=
          add_le_add hmassToInv herror
        _ ≤ (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
              LinearSieve.upperRosserBoundaryMass (k + 1) s a) + ρ := by
          linarith

/-- The outer prime sum weighted by the complete continuous depth-two mass is,
uniformly on the upper-sieve range, bounded by the depth-two boundary integral.
This is the final one-dimensional Stieltjes step in the depth-two comparison. -/
theorem
    exists_sum_nu_div_one_sub_mul_inv_mul_upperRosserBoundaryMass_one_le_integral_add_of_three_halves_le
    (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z s : ℝ) (T : Finset ℕ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T, Real.log p / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1) →
        3 / 2 ≤ s →
        ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
          ((Real.log p / Real.log z)⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log p / Real.log z)) ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s a) + ρ := by
  let B : ℝ := 30 * Real.log 6
  let L : ℝ := 6 * (144 + 6 * Real.log 6) + 180 * Real.log 6
  have hlog : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨z₀, hz₀, houter⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add
      K ρ B L hK hρ hB hL
  refine ⟨z₀, hz₀, ?_⟩
  intro S z s T hz hlocal hT hcoord hs
  let f : ℝ → ℝ :=
    fun a => a⁻¹ * LinearSieve.upperRosserBoundaryMass 1 s a
  have hf : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, 0 ≤ f x := by
    intro x hx
    exact mul_nonneg
      (inv_nonneg.mpr ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans hx.1))
      (LinearSieve.upperRosserBoundaryMass_nonneg 1
        ((by norm_num : (0 : ℝ) ≤ 1 / 6).trans hx.1))
  have hfB : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1, f x ≤ B := by
    intro x hx
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hx.1
    have hxinv : x⁻¹ ≤ (6 : ℝ) := by
      calc
        x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
          (inv_le_inv₀ hxpos (by norm_num)).2 hx.1
        _ = 6 := by norm_num
    have hxinvNonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
    dsimp [f, B]
    calc
      x⁻¹ * LinearSieve.upperRosserBoundaryMass 1 s x ≤
          6 * (5 * Real.log 6) :=
        mul_le_mul hxinv
          (LinearSieve.upperRosserBoundaryMass_one_le_five_mul_log_six hx.1)
          (LinearSieve.upperRosserBoundaryMass_nonneg 1 hxpos.le)
          (by norm_num)
      _ = 30 * Real.log 6 := by ring
  have hfLip : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
        |f x - f y| ≤ L * |x - y| := by
    intro x hx y hy
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hx.1
    have hypos : 0 < y := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hy.1
    have hxinv : |x⁻¹| ≤ (6 : ℝ) := by
      rw [abs_of_pos (inv_pos.mpr hxpos)]
      calc
        x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
          (inv_le_inv₀ hxpos (by norm_num)).2 hx.1
        _ = 6 := by norm_num
    have hmass :=
      LinearSieve.abs_upperRosserBoundaryMass_one_sub_le_joint
        (s := s) (t := s) hx.1 hy.1
    simp only [sub_self, abs_zero, mul_zero, zero_add] at hmass
    have hmassAbs :
        |LinearSieve.upperRosserBoundaryMass 1 s y| ≤ 5 * Real.log 6 := by
      rw [abs_of_nonneg
        (LinearSieve.upperRosserBoundaryMass_nonneg 1 hypos.le)]
      exact LinearSieve.upperRosserBoundaryMass_one_le_five_mul_log_six hy.1
    have hinv :=
      LinearSieve.abs_inv_sub_inv_le_thirty_six_of_one_sixth_le hx.1 hy.1
    dsimp [f, L]
    calc
      |x⁻¹ * LinearSieve.upperRosserBoundaryMass 1 s x -
          y⁻¹ * LinearSieve.upperRosserBoundaryMass 1 s y| =
          |x⁻¹ * (LinearSieve.upperRosserBoundaryMass 1 s x -
              LinearSieve.upperRosserBoundaryMass 1 s y) +
            (x⁻¹ - y⁻¹) *
              LinearSieve.upperRosserBoundaryMass 1 s y| := by
            congr 1
            ring
      _ ≤ |x⁻¹| *
            |LinearSieve.upperRosserBoundaryMass 1 s x -
              LinearSieve.upperRosserBoundaryMass 1 s y| +
          |x⁻¹ - y⁻¹| *
            |LinearSieve.upperRosserBoundaryMass 1 s y| := by
        simpa only [abs_mul] using
          abs_add_le
            (x⁻¹ * (LinearSieve.upperRosserBoundaryMass 1 s x -
              LinearSieve.upperRosserBoundaryMass 1 s y))
            ((x⁻¹ - y⁻¹) *
              LinearSieve.upperRosserBoundaryMass 1 s y)
      _ ≤ 6 * ((144 + 6 * Real.log 6) * |x - y|) +
          (36 * |x - y|) * (5 * Real.log 6) :=
        add_le_add
          (mul_le_mul hxinv hmass (abs_nonneg _) (by norm_num))
          (mul_le_mul hinv hmassAbs (abs_nonneg _)
            (mul_nonneg (by norm_num) (abs_nonneg _)))
      _ = (6 * (144 + 6 * Real.log 6) + 180 * Real.log 6) *
          |x - y| := by ring
  have hint : MeasureTheory.IntegrableOn
      (fun x => x⁻¹ * f x) (Set.Ioo (1 / 6) 1) := by
    simpa [f, mul_assoc] using
      LinearSieve.integrableOn_inv_sq_mul_upperRosserBoundaryMass_one s
  have hcomparison :=
    houter S z T
      (fun p => f (Real.log p / Real.log z)) f
      hz hlocal hT hcoord hf hfB hfLip hint (by
        intro p hp
        exact ⟨hf _ (hcoord p hp), le_rfl⟩)
  calc
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        ((Real.log p / Real.log z)⁻¹ *
          LinearSieve.upperRosserBoundaryMass 1 s
            (Real.log p / Real.log z)) =
        ∑ p ∈ T, f (Real.log p / Real.log z) *
          (S.nu p / (1 - S.nu p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [f]
      ring
    _ ≤ (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * f x) + ρ := hcomparison
    _ = (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass 1 s a) + ρ := by
      rw [LinearSieve.integral_upperRosserBoundaryMass_one_eq_integral_one_sixth hs]
      congr 2
      funext a
      simp only [f]
      ring

/-- The screened depth-two residual prime sum is uniformly bounded by its
continuous boundary integral. -/
theorem exists_screenedResidualBoundaryMass_le_integral_add_of_three_halves_le
    (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ q ∈ S.prodPrimes.primeFactors.filter
            (fun q : ℕ => 1 / 6 < Real.log q / Real.log z),
          (S.nu q / (1 - S.nu q)) *
            ∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
              ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                    1 / 6 < Real.log p₁ / Real.log z),
                (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux 0
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z) (Real.log p₁ / Real.log z) ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s a) + ρ := by
  let ε₁ : ℝ := ρ / 144
  let ε₀ : ℝ := ρ / 24
  let B : ℝ := Real.log 6 + ε₁
  have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (Real.log_nonneg (by norm_num)) hε₁.le
  obtain ⟨zInner, hzInner, hinner⟩ :=
    exists_sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_logKernel_add
      K ε₁ hK hε₁
  obtain ⟨zMiddle, hzMiddle, hmiddle⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_Ioo_add
      K ε₀ B 12 hK hε₀ hB (by norm_num)
  obtain ⟨zOuter, hzOuter, houter⟩ :=
    exists_sum_nu_div_one_sub_mul_inv_mul_upperRosserBoundaryMass_one_le_integral_add_of_three_halves_le
      K (ρ / 2) hK (half_pos hρ)
  obtain ⟨zMass, hzMass, hmassComparison⟩ :=
    exists_weighted_sum_nu_div_one_sub_le_integral_add
      K 1 1 0 hK (by norm_num) (by norm_num) (by norm_num)
  let z₀ : ℝ := max (max zInner zMiddle) (max zOuter zMass)
  refine ⟨z₀, hzInner.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
  have hzInnerZ : zInner ≤ z :=
    (le_max_left zInner zMiddle).trans ((le_max_left _ _).trans hz)
  have hzMiddleZ : zMiddle ≤ z :=
    (le_max_right zInner zMiddle).trans ((le_max_left _ _).trans hz)
  have hzOuterZ : zOuter ≤ z :=
    (le_max_left zOuter zMass).trans ((le_max_right _ _).trans hz)
  have hzMassZ : zMass ≤ z :=
    (le_max_right zOuter zMass).trans ((le_max_right _ _).trans hz)
  have hz2 : 2 ≤ z := hzInner.trans hzInnerZ
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) hz2
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  let Q : Finset ℕ :=
    S.prodPrimes.primeFactors.filter
      (fun q : ℕ => 1 / 6 < Real.log q / Real.log z)
  have hQ : Q ⊆ S.prodPrimes.primeFactors := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hQcoord : ∀ q ∈ Q,
      Real.log q / Real.log z ∈ Set.Icc (1 / 6 : ℝ) 1 := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    refine ⟨hq'.2.le, ?_⟩
    rw [div_le_one hlogz]
    exact Real.strictMonoOn_log.monotoneOn hqpos hzpos (hcut q hq'.1)
  have hinv :
      MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹)
        (Set.Ioo (1 / 6) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
    apply intervalIntegral.intervalIntegrable_inv (f := fun x : ℝ => x)
    · intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      exact ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 6).trans_le hx.1)
    · exact continuous_id.continuousOn
  have hinvIntegralLe :
      (∫ x : ℝ in Set.Ioo (1 / 6) 1, x⁻¹) ≤ 5 := by
    have hfinite : MeasureTheory.volume (Set.Ioo (1 / 6 : ℝ) 1) ≠ ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ => (6 : ℝ))
          (Set.Ioo (1 / 6) 1) :=
      MeasureTheory.integrableOn_const hfinite
    calc
      (∫ x : ℝ in Set.Ioo (1 / 6) 1, x⁻¹) ≤
          ∫ _x : ℝ in Set.Ioo (1 / 6) 1, (6 : ℝ) := by
        apply MeasureTheory.setIntegral_mono_on hinv hconst measurableSet_Ioo
        intro x hx
        have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 6).trans hx.1
        calc
          x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
            (inv_le_inv₀ hxpos (by norm_num)).2 hx.1.le
          _ = 6 := by norm_num
      _ = (1 - (1 / 6 : ℝ)) * 6 := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
          Real.volume_Ioo, ENNReal.toReal_ofReal (by norm_num)]
        rfl
      _ = 5 := by norm_num
  have hQmassComparison :=
    hmassComparison S z Q (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      hzMassZ hlocal hQ hQcoord
      (by intro x hx; norm_num)
      (by intro x hx; norm_num)
      (by intro x hx y hy; norm_num)
      (by simpa using hinv)
      (by intro q hq; exact ⟨by norm_num, le_rfl⟩)
  have hQmass :
      ∑ q ∈ Q, S.nu q / (1 - S.nu q) ≤ 6 := by
    calc
      ∑ q ∈ Q, S.nu q / (1 - S.nu q) =
          ∑ q ∈ Q, (1 : ℝ) * (S.nu q / (1 - S.nu q)) := by simp
      _ ≤ (∫ x in Set.Ioo (1 / 6) 1, x⁻¹ * (1 : ℝ)) + 1 :=
        hQmassComparison
      _ ≤ 6 := by
        simp only [mul_one]
        linarith
  have hqBound : ∀ q ∈ Q,
      (∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
          (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
        ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
              1 / 6 < Real.log p₁ / Real.log z),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) ≤
        LinearSieve.upperRosserBoundaryMass 1 s
          (Real.log q / Real.log z) + ρ / 12 := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqa : 1 / 6 ≤ Real.log q / Real.log z := hq'.2.le
    have hqapos : 0 < Real.log q / Real.log z :=
      (by norm_num : (0 : ℝ) < 1 / 6).trans_le hqa
    let P : Finset ℕ :=
      S.prodPrimes.primeFactors.filter (fun p => q < p)
    let P₀all : Finset ℕ :=
      P.filter (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z)
    let P₀ : Finset ℕ :=
      P₀all.filter (fun p₀ => p₀ ^ 3 < Nat.floor Δ + 1)
    let inner : ℕ → ℝ := fun p₀ =>
      ∑ p₁ ∈ P.filter
          (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
            1 / 6 < Real.log p₁ / Real.log z),
        (S.nu p₁ / (1 - S.nu p₁)) *
          LinearSieve.upperRosserBoundaryMassAux 0
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            (Real.log q / Real.log z) (Real.log p₁ / Real.log z)
    have hP₀ : P₀ ⊆ S.prodPrimes.primeFactors := by
      intro p hp
      exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
    have hP₀coord : ∀ p₀ ∈ P₀,
        Real.log p₀ / Real.log z ∈
          Set.Icc (Real.log q / Real.log z) (min 1 (s / 3)) := by
      intro p₀ hp₀
      have hp₀' := Finset.mem_filter.mp hp₀
      have hp₀all := Finset.mem_filter.mp hp₀'.1
      have hp₀base := Finset.mem_filter.mp hp₀all.1
      have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀base.1
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
      have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
      have hqp₀ :
          Real.log q / Real.log z < Real.log p₀ / Real.log z := by
        apply (div_lt_div_iff_of_pos_right hlogz).2
        exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₀pos).2
          (by exact_mod_cast hp₀base.2)
      have hp₀one : Real.log p₀ / Real.log z ≤ 1 := by
        rw [div_le_one hlogz]
        exact Real.strictMonoOn_log.monotoneOn hp₀pos hzpos
          (hcut p₀ hp₀base.1)
      have hp₀floor : p₀ ^ 3 ≤ Nat.floor Δ := by omega
      have hp₀Δ : (p₀ : ℝ) ^ 3 ≤ Δ := by
        have hcast : ((p₀ ^ 3 : ℕ) : ℝ) ≤ (Nat.floor Δ : ℝ) := by
          exact_mod_cast hp₀floor
        norm_num at hcast
        exact hcast.trans (Nat.floor_le hΔ.le)
      have hlogpow : 3 * Real.log p₀ ≤ Real.log Δ := by
        have h := Real.strictMonoOn_log.monotoneOn
          (by exact pow_pos hp₀pos 3) hΔ hp₀Δ
        simpa [Real.log_pow] using h
      have hp₀third : Real.log p₀ / Real.log z ≤ s / 3 := by
        rw [hs]
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
        have hdiv :
            (3 * Real.log p₀) / Real.log z ≤
              Real.log Δ / Real.log z :=
          (div_le_div_iff_of_pos_right hlogz).2 hlogpow
        calc
          Real.log p₀ / Real.log z * 3 =
              (3 * Real.log p₀) / Real.log z := by ring
          _ ≤ Real.log Δ / Real.log z := hdiv
      exact ⟨hqp₀.le, le_min hp₀one hp₀third⟩
    by_cases hP₀ne : P₀.Nonempty
    · have hamin : Real.log q / Real.log z ≤ min 1 (s / 3) := by
        obtain ⟨p₀, hp₀⟩ := hP₀ne
        exact (hP₀coord p₀ hp₀).1.trans (hP₀coord p₀ hp₀).2
      have hInnerBound : ∀ p₀ ∈ P₀,
          inner p₀ ≤
            LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) (Real.log p₀ / Real.log z) + ε₁ := by
        intro p₀ hp₀
        have hp₀' := Finset.mem_filter.mp hp₀
        have hp₀all := Finset.mem_filter.mp hp₀'.1
        have hp₀base := Finset.mem_filter.mp hp₀all.1
        have hp₀prime : p₀.Prime :=
          Nat.prime_of_mem_primeFactors hp₀base.1
        have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀prime.pos
        apply hinner S z s (Real.log p₀ / Real.log z)
          (Real.log q / Real.log z)
          (P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
              1 / 6 < Real.log p₁ / Real.log z))
          hzInnerZ hlocal hqa
          ((hP₀coord p₀ hp₀).2.trans (min_le_left _ _))
        · intro p hp
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        · intro p₁ hp₁
          have hp₁' := Finset.mem_filter.mp hp₁
          have hp₁base := Finset.mem_filter.mp hp₁'.1
          have hp₁prime : p₁.Prime :=
            Nat.prime_of_mem_primeFactors hp₁base.1
          have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
          have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁prime.pos
          have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
          constructor
          · apply (div_lt_div_iff_of_pos_right hlogz).2
            exact (Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
              (by exact_mod_cast hp₁base.2)
          · apply (div_lt_div_iff_of_pos_right hlogz).2
            exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
              (by exact_mod_cast hp₁'.2.1)
      have hInnerNonneg : ∀ p₀ ∈ P₀, 0 ≤ inner p₀ := by
        intro p₀ hp₀
        apply Finset.sum_nonneg
        intro p₁ hp₁
        have hp₁mem :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1
        exact mul_nonneg (nu_div_one_sub_nonneg_of_mem hp₁mem)
          (LinearSieve.upperRosserBoundaryMassAux_nonneg 0 hqapos.le)
      have hfNonneg : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          0 ≤ LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) x + ε₁ := by
        intro x hx
        exact add_nonneg
          (LinearSieve.upperRosserBoundaryLogKernel_nonneg hqapos) hε₁.le
      have hfB : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) x + ε₁ ≤ B := by
        intro x hx
        dsimp [B]
        linarith [LinearSieve.upperRosserBoundaryLogKernel_le_log_six
          (s := s) hqa hx.2]
      have hfLip : ∀ x ∈ Set.Icc (1 / 6 : ℝ) 1,
          ∀ y ∈ Set.Icc (1 / 6 : ℝ) 1,
            |(LinearSieve.upperRosserBoundaryLogKernel s
                (Real.log q / Real.log z) x + ε₁) -
              (LinearSieve.upperRosserBoundaryLogKernel s
                (Real.log q / Real.log z) y + ε₁)| ≤
              12 * |x - y| := by
        intro x hx y hy
        simpa only [add_sub_add_right_eq_sub] using
          abs_upperRosserBoundaryLogKernel_sub_le_of_one_sixth_le hqa
            (x := x) (y := y) (s := s)
      have hfInt : MeasureTheory.IntegrableOn
          (fun x => x⁻¹ *
            (LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) x + ε₁))
          (Set.Ioo (1 / 6) 1) := by
        have hfinite :
            MeasureTheory.volume (Set.Ioo (1 / 6 : ℝ) 1) < ⊤ := by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top
        apply MeasureTheory.IntegrableOn.of_bound hfinite
          (measurable_id.inv.mul
            ((LinearSieve.measurable_upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z)).add measurable_const)).aestronglyMeasurable
          (6 * B)
        filter_upwards
          [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
        have hxpos : 0 < x :=
          (by norm_num : (0 : ℝ) < 1 / 6).trans hx.1
        have hxinv : x⁻¹ ≤ (6 : ℝ) := by
          calc
            x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
              (inv_le_inv₀ hxpos (by norm_num)).2 hx.1.le
            _ = 6 := by norm_num
        change |x⁻¹ * (LinearSieve.upperRosserBoundaryLogKernel s
          (Real.log q / Real.log z) x + ε₁)| ≤ 6 * B
        rw [abs_of_nonneg
          (mul_nonneg (inv_nonneg.mpr hxpos.le)
            (hfNonneg x ⟨hx.1.le, hx.2.le⟩))]
        exact mul_le_mul hxinv (hfB x ⟨hx.1.le, hx.2.le⟩)
          (hfNonneg x ⟨hx.1.le, hx.2.le⟩) (by norm_num)
      have hmiddleBound :=
        hmiddle S z P₀ inner
          (fun x => LinearSieve.upperRosserBoundaryLogKernel s
            (Real.log q / Real.log z) x + ε₁)
          (Real.log q / Real.log z) (min 1 (s / 3))
          hzMiddleZ hlocal hP₀ hqa hamin (min_le_left _ _)
          hP₀coord hfNonneg hfB hfLip hfInt
          (by
            intro p₀ hp₀
            exact ⟨hInnerNonneg p₀ hp₀, hInnerBound p₀ hp₀⟩)
      have hintervalSubset :
          Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)) ⊆
            Set.Ioo (1 / 6 : ℝ) 1 := by
        intro x hx
        exact ⟨hqa.trans_lt hx.1, hx.2.trans_le (min_le_left _ _)⟩
      have hkInt :
          MeasureTheory.IntegrableOn
            (fun x => x⁻¹ *
              LinearSieve.upperRosserBoundaryLogKernel s
                (Real.log q / Real.log z) x)
            (Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3))) :=
        (LinearSieve.integrableOn_inv_mul_upperRosserBoundaryLogKernel
          (s := s) hqa (show (1 : ℝ) ≤ 1 from le_rfl)).mono_set (by
            intro x hx
            exact ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩)
      have heInt :
          MeasureTheory.IntegrableOn (fun x => x⁻¹ * ε₁)
            (Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3))) :=
        (hinv.mono_set hintervalSubset).mul_const ε₁
      have heIntegral :
          (∫ x in Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)),
            x⁻¹ * ε₁) ≤ 6 * ε₁ := by
        have hfinite :
            MeasureTheory.volume
              (Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3))) ≠ ⊤ := by
          rw [Real.volume_Ioo]
          exact ENNReal.ofReal_ne_top
        have hconst :
            MeasureTheory.IntegrableOn (fun _ : ℝ => 6 * ε₁)
              (Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3))) :=
          MeasureTheory.integrableOn_const hfinite
        calc
          (∫ x in Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)),
              x⁻¹ * ε₁) ≤
              ∫ _x in Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)),
                6 * ε₁ := by
            apply MeasureTheory.setIntegral_mono_on heInt hconst measurableSet_Ioo
            intro x hx
            have hxpos : 0 < x := hqapos.trans hx.1
            have hxinv : x⁻¹ ≤ (6 : ℝ) := by
              calc
                x⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
                  (inv_le_inv₀ hxpos (by norm_num)).2 (hqa.trans hx.1.le)
                _ = 6 := by norm_num
            exact mul_le_mul_of_nonneg_right hxinv hε₁.le
          _ = (min 1 (s / 3) - Real.log q / Real.log z) * (6 * ε₁) := by
            rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
              Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr hamin)]
            rfl
          _ ≤ 6 * ε₁ := by
            have hlength :
                min 1 (s / 3) - Real.log q / Real.log z ≤ 1 := by
              linarith [min_le_left (1 : ℝ) (s / 3)]
            exact mul_le_of_le_one_left (by positivity) hlength
      have hintegral :
          (∫ x in Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)),
            x⁻¹ * (LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) x + ε₁)) ≤
            LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z) + 6 * ε₁ := by
        rw [show (fun x => x⁻¹ *
            (LinearSieve.upperRosserBoundaryLogKernel s
              (Real.log q / Real.log z) x + ε₁)) =
            (fun x => x⁻¹ *
              LinearSieve.upperRosserBoundaryLogKernel s
                (Real.log q / Real.log z) x + x⁻¹ * ε₁) by
              funext x
              ring,
          MeasureTheory.integral_add hkInt heInt,
          ← LinearSieve.upperRosserBoundaryMass_one_eq_integral_logKernel hqapos]
        linarith
      have hsum :
          (∑ p₀ ∈ P₀all,
            ∑ p₁ ∈ P.filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                  1 / 6 < Real.log p₁ / Real.log z),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux 0
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z)
                  (Real.log p₁ / Real.log z)) =
              ∑ p₀ ∈ P₀, inner p₀ * (S.nu p₀ / (1 - S.nu p₀)) := by
        calc
          (∑ p₀ ∈ P₀all,
              ∑ p₁ ∈ P.filter
                  (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                    1 / 6 < Real.log p₁ / Real.log z),
                (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                  LinearSieve.upperRosserBoundaryMassAux 0
                    (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                    (Real.log q / Real.log z)
                    (Real.log p₁ / Real.log z)) =
              ∑ p₀ ∈ P₀all,
                (S.nu p₀ / (1 - S.nu p₀)) * inner p₀ := by
            apply Finset.sum_congr rfl
            intro p₀ hp₀
            dsimp only [inner]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p₁ hp₁
            ring
          _ = ∑ p₀ ∈ P₀,
                (S.nu p₀ / (1 - S.nu p₀)) * inner p₀ := by
            symm
            apply Finset.sum_subset
            · exact Finset.filter_subset _ _
            · intro p₀ hp₀ hp₀not
              have hcube : ¬p₀ ^ 3 < Nat.floor Δ + 1 := by
                intro hcube
                exact hp₀not (Finset.mem_filter.mpr ⟨hp₀, hcube⟩)
              have hinnerZero : inner p₀ = 0 := by
                dsimp only [inner]
                apply Finset.sum_eq_zero
                intro p₁ hp₁
                exact (hcube (Finset.mem_filter.mp hp₁).2.2.1).elim
              rw [hinnerZero, mul_zero]
          _ = ∑ p₀ ∈ P₀, inner p₀ * (S.nu p₀ / (1 - S.nu p₀)) := by
            apply Finset.sum_congr rfl
            intro p₀ hp₀
            ring
      change (∑ p₀ ∈ P₀all,
        ∑ p₁ ∈ P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
              1 / 6 < Real.log p₁ / Real.log z),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) ≤ _
      rw [hsum]
      calc
        (∑ p₀ ∈ P₀, inner p₀ * (S.nu p₀ / (1 - S.nu p₀))) ≤
            (∫ x in Set.Ioo (Real.log q / Real.log z) (min 1 (s / 3)),
              x⁻¹ * (LinearSieve.upperRosserBoundaryLogKernel s
                (Real.log q / Real.log z) x + ε₁)) + ε₀ := hmiddleBound
        _ ≤ LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z) + 6 * ε₁ + ε₀ := by linarith
        _ = LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z) + ρ / 12 := by
            dsimp [ε₁, ε₀]
            ring
    · have hsumZero :
          (∑ p₀ ∈ P₀all,
            ∑ p₁ ∈ P.filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
                  1 / 6 < Real.log p₁ / Real.log z),
              (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
                LinearSieve.upperRosserBoundaryMassAux 0
                  (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
                  (Real.log q / Real.log z)
                  (Real.log p₁ / Real.log z)) = 0 := by
        apply Finset.sum_eq_zero
        intro p₀ hp₀
        have hcube : ¬p₀ ^ 3 < Nat.floor Δ + 1 := by
          intro hcube
          exact hP₀ne ⟨p₀, Finset.mem_filter.mpr ⟨hp₀, hcube⟩⟩
        apply Finset.sum_eq_zero
        intro p₁ hp₁
        exact (hcube (Finset.mem_filter.mp hp₁).2.2.1).elim
      change (∑ p₀ ∈ P₀all,
        ∑ p₁ ∈ P.filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
              1 / 6 < Real.log p₁ / Real.log z),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) ≤ _
      rw [hsumZero]
      exact add_nonneg
        (LinearSieve.upperRosserBoundaryMass_nonneg 1 hqapos.le)
        (by positivity)
  have hmain :
      ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryMass 1 s
            (Real.log q / Real.log z) ≤
        ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          ((Real.log q / Real.log z)⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z)) := by
    apply Finset.sum_le_sum
    intro q hq
    have hqa := (hQcoord q hq)
    have hqapos : 0 < Real.log q / Real.log z :=
      (by norm_num : (0 : ℝ) < 1 / 6).trans_le hqa.1
    apply mul_le_mul_of_nonneg_left
    · calc
        LinearSieve.upperRosserBoundaryMass 1 s
            (Real.log q / Real.log z) =
            1 * LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z) := by ring
        _ ≤ (Real.log q / Real.log z)⁻¹ *
              LinearSieve.upperRosserBoundaryMass 1 s
                (Real.log q / Real.log z) := by
          apply mul_le_mul_of_nonneg_right
          · exact (one_le_inv₀ hqapos).2 hqa.2
          · exact LinearSieve.upperRosserBoundaryMass_nonneg 1 hqapos.le
    · exact nu_div_one_sub_nonneg_of_mem (hQ hq)
  have houterBound :=
    houter S z s Q hzOuterZ hlocal hQ hQcoord hslo
  have herror :
      (ρ / 12) * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) ≤ ρ / 2 := by
    calc
      (ρ / 12) * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) ≤
          (ρ / 12) * 6 :=
        mul_le_mul_of_nonneg_left hQmass (by positivity)
      _ = ρ / 2 := by ring
  change (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
    ∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
        (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
      ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
          (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
            1 / 6 < Real.log p₁ / Real.log z),
        (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
          LinearSieve.upperRosserBoundaryMassAux 0
            (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
            (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) ≤ _
  calc
    (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
      ∑ p₀ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
          (fun p₀ : ℕ => 1 / 6 < Real.log p₀ / Real.log z),
        ∑ p₁ ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).filter
            (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < Nat.floor Δ + 1 ∧
              1 / 6 < Real.log p₁ / Real.log z),
          (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - Real.log p₀ / Real.log z - Real.log p₁ / Real.log z)
              (Real.log q / Real.log z) (Real.log p₁ / Real.log z)) ≤
        ∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          (LinearSieve.upperRosserBoundaryMass 1 s
            (Real.log q / Real.log z) + ρ / 12) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hqBound q hq)
        (nu_div_one_sub_nonneg_of_mem (hQ hq))
    _ = (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryMass 1 s
            (Real.log q / Real.log z)) +
        (ρ / 12) * (∑ q ∈ Q, S.nu q / (1 - S.nu q)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (∑ q ∈ Q, (S.nu q / (1 - S.nu q)) *
          ((Real.log q / Real.log z)⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s
              (Real.log q / Real.log z))) + ρ / 2 := by
      exact add_le_add hmain herror
    _ ≤ (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass 1 s a) + ρ := by
      linarith

/-- Uniform depth-two comparison between the explicit finite Rosser boundary
sum and its continuous Buchstab integral. -/
theorem
    exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_one_le_integral_add_of_three_halves_le
    (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                (S.prodPrimes.primeFactors.filter (fun p => q < p)) 1 ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass 1 s a) + ρ := by
  obtain ⟨z₀, hz₀, hscreened⟩ :=
    exists_screenedResidualBoundaryMass_le_integral_add_of_three_halves_le
      K ρ hK hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
  exact
    (sum_mul_upperRosserBoundaryChainsFixedDepthDensity_one_le_screenedResidualBoundaryMass
      (show 1 < z by linarith [hz₀.trans hz]) hΔ hs hslo).trans
      (hscreened S z Δ s hz hΔ hlocal hcut hs hslo hsupper)

/-- Fixed-mesh inner depth-two estimate with its closed-face hypothesis
discharged uniformly.  A common positive lower bound for the mesh supplies the
atom cutoff; no additional analytic hypothesis is required. -/
theorem
    exists_sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_rpow_partition_Icc_add
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (K ρ c : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z s x₀ a : ℝ) (T : Finset ℕ)
          (cell : ℕ → ι) (u v : ι → ℝ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        (∀ i, c ≤ u i) → (∀ i, u i ≤ v i) →
        T ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ T,
          z ^ (u (cell p)) ≤ (p : ℝ) ∧
            (p : ℝ) ≤ z ^ (v (cell p))) →
        ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
            LinearSieve.upperRosserBoundaryMassAux 0
              (s - x₀ - Real.log p / Real.log z) a
              (Real.log p / Real.log z) ≤
          (∑ i, (v i / u i *
            (1 + K / (u i * Real.log z)) - 1)) + ρ := by
  obtain ⟨z₀, hz₀, hfaces⟩ :=
    exists_rpow_partition_right_faces_mass_le ι K ρ c hK hρ hc
  let z₁ := max z₀ ((2 : ℝ) ^ (1 / c))
  refine ⟨z₁, hz₀.trans (le_max_left _ _), ?_⟩
  intro S z s x₀ a T cell u v hz hlocal hcu huv hT hinterval
  have hz₀z : z₀ ≤ z := (le_max_left _ _).trans hz
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz₀z)
  have hzbase : (2 : ℝ) ^ (1 / c) ≤ z :=
    (le_max_right _ _).trans hz
  have hzc : 2 ≤ z ^ c := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by simp
      _ = ((2 : ℝ) ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        field_simp
      _ ≤ z ^ c := Real.rpow_le_rpow (by positivity) hzbase hc.le
  apply
    sum_nu_div_one_sub_mul_upperRosserBoundaryMassAux_zero_le_rpow_partition_Icc_add_global_atoms
      hlocal hz1 (fun i => hc.trans_le (hcu i)) huv
  · intro i
    exact hzc.trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (hcu i))
  · exact hT
  · exact hinterval
  · apply hfaces S z T cell v hz₀z hlocal hT
    · intro p hp
      exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (hcu (cell p))).trans
        (hinterval p hp).1
    · intro p hp
      exact (hinterval p hp).2

end MathlibNt.SieveTheory.SwitchingPrinciple
