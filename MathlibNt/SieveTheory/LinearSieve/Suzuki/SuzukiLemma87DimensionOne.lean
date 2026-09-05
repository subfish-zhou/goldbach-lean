import MathlibNt.SieveTheory.SwitchingPrinciple

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple

set_option maxHeartbeats 800000

/-- The middle-range prime sum in Suzuki Lemma 8.7 (dimension one): the
prime range stops at `v`, while the Euler suffix ratio still stops at `z`. -/
noncomputable def suzukiLemmaEightSevenPrimeSum
    (S : BoundingSieve) (D w v z : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑ p ∈ S.prodPrimes.primeFactors.filter
      (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v),
    S.nu p *
      (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹) *
      H (Real.log D / Real.log p)

private theorem suzuki_suffix_product_split
    (S : BoundingSieve) {p : ℕ} {v z : ℝ}
    (hpv : (p : ℝ) < v) (hvz : v ≤ z) :
    (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹) =
      (∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < v), (1 - S.nu q)⁻¹) *
      suzukiLocalRatio S v z := by
  classical
  let A := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => p ≤ q ∧ (q : ℝ) < v)
  let B := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => v ≤ (q : ℝ) ∧ (q : ℝ) < z)
  let C := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z)
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro q hqA hqB
    have hA := Finset.mem_filter.mp hqA
    have hB := Finset.mem_filter.mp hqB
    exact (not_lt_of_ge hB.2.1) hA.2.2
  have hcup : A ∪ B = C := by
    ext q
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hq, hpq, hqv⟩ | ⟨hq, hvq, hqz⟩)
      · exact ⟨hq, hpq, hqv.trans_le hvz⟩
      · exact ⟨hq, by exact_mod_cast (le_trans (le_of_lt hpv) hvq), hqz⟩
    · rintro ⟨hq, hpq, hqz⟩
      by_cases hqv : (q : ℝ) < v
      · exact Or.inl ⟨hq, hpq, hqv⟩
      · exact Or.inr ⟨hq, le_of_not_gt hqv, hqz⟩
  unfold suzukiLocalRatio
  change (∏ q ∈ C, (1 - S.nu q)⁻¹) =
    (∏ q ∈ A, (1 - S.nu q)⁻¹) * (∏ q ∈ B, (1 - S.nu q)⁻¹)
  rw [← hcup, Finset.prod_union hdis]

/-- Exact factorization used in Suzuki's proof of Lemma 8.7. -/
theorem suzukiLemmaEightSevenPrimeSum_eq_localRatio_mul
    (S : BoundingSieve) (D w v z : ℝ) (H : ℝ → ℝ) (hvz : v ≤ z) :
    suzukiLemmaEightSevenPrimeSum S D w v z H =
      suzukiLocalRatio S v z * suzukiLemmaEightSixPrimeSum S D w v H := by
  classical
  unfold suzukiLemmaEightSevenPrimeSum suzukiLemmaEightSixPrimeSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpv := (Finset.mem_filter.mp hp).2.2
  rw [suzuki_suffix_product_split S hpv hvz]
  ring

private theorem suzukiLocalRatio_nonneg
    (S : BoundingSieve) (v z : ℝ) : 0 ≤ suzukiLocalRatio S v z := by
  classical
  unfold suzukiLocalRatio
  apply Finset.prod_nonneg
  intro p hp
  have hpS := (Finset.mem_filter.mp hp).1
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
  have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
  exact inv_nonneg.mpr (sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le)

private theorem exponent_pos_of_two_le_rpow
    {D x a : ℝ} (hD : 1 < D) (hx : 2 ≤ x) (ha : x = D ^ (1 / a)) :
    0 < a := by
  have hD0 : 0 < D := zero_lt_one.trans hD
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have halog : Real.log x = Real.log D / a := by
    rw [ha, Real.log_rpow hD0]
    ring
  have hdiv : 0 < Real.log D / a := halog ▸ hlogx
  rcases (div_pos_iff.mp hdiv) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge hlogD.le) h.1)

private theorem coordinate_orders
    {D z v w s τ σ : ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ)) :
    0 < s ∧ 0 < τ ∧ 0 < σ ∧ s ≤ τ ∧ τ ≤ σ := by
  have hs := exponent_pos_of_two_le_rpow hD hz2 hz
  have hτ := exponent_pos_of_two_le_rpow hD hv2 hv
  have hσ := exponent_pos_of_two_le_rpow hD hw2 hw
  have hD0 : 0 < D := zero_lt_one.trans hD
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogs : Real.log z = Real.log D / s := by
    rw [hz, Real.log_rpow hD0]
    ring
  have hlogτ : Real.log v = Real.log D / τ := by
    rw [hv, Real.log_rpow hD0]
    ring
  have hlogσ : Real.log w = Real.log D / σ := by
    rw [hw, Real.log_rpow hD0]
    ring
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw2
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv2
  have hz0 : 0 < z := lt_of_lt_of_le (by norm_num) hz2
  have hlog_wv : Real.log w ≤ Real.log v :=
    Real.strictMonoOn_log.monotoneOn hw0 hv0 hwv
  have hlog_vz : Real.log v ≤ Real.log z :=
    Real.strictMonoOn_log.monotoneOn hv0 hz0 hvz
  have hsτ : s ≤ τ := by
    rw [hlogτ, hlogs] at hlog_vz
    have hmul := (div_le_div_iff₀ hτ hs).mp hlog_vz
    nlinarith
  have hτσ : τ ≤ σ := by
    rw [hlogσ, hlogτ] at hlog_wv
    have hmul := (div_le_div_iff₀ hσ hτ).mp hlog_wv
    nlinarith
  exact ⟨hs, hτ, hσ, hsτ, hτσ⟩

/-- Suzuki Lemma 8.7, specialized to sieve dimension one (`κ = 1`).
The sum is over the middle range `w ≤ p < v`, but retains the suffix ratio
`V(p)/V(z)`.  The error is exactly `6 K² H(τ) / log w * (τ/s)`. -/
theorem suzukiLemmaEightSevenDimensionOne
    {S : BoundingSieve} {D z v w s τ σ K : ℝ} {H : ℝ → ℝ}
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hHcont : Continuous H)
    (hH0 : ∀ t ∈ Set.Icc τ σ, 0 ≤ H t)
    (hHt : AntitoneOn (fun t => H t * t) (Set.Icc τ σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z H ≤
      (1 / s) * (∫ t in τ..σ, H t) +
        (6 * K ^ 2 * H τ / Real.log w) * (τ / s) := by
  have hord := coordinate_orders hD hz2 hv2 hw2 hwv hvz hz hv hw
  rcases hord with ⟨hs, hτ, hσ, hsτ, hτσ⟩
  have h86 := suzukiLemmaEightSixDimensionOne hD hw2 hτ hτσ hv hw
    hHcont hH0 hHt (show 0 ≤ K by linarith) hlocal
  have hratio0 := suzukiLocalRatio_nonneg S v z
  have hfac := suzukiLemmaEightSevenPrimeSum_eq_localRatio_mul S D w v z H hvz
  rw [hfac]
  calc
    suzukiLocalRatio S v z * suzukiLemmaEightSixPrimeSum S D w v H ≤
        suzukiLocalRatio S v z *
          ((1 / τ) * (∫ t in τ..σ, H t) + 2 * K * H τ / Real.log w) :=
      mul_le_mul_of_nonneg_left h86 hratio0
    _ ≤ (1 / s) * (∫ t in τ..σ, H t) +
        (6 * K ^ 2 * H τ / Real.log w) * (τ / s) := by
      let I : ℝ := ∫ t in τ..σ, H t
      have hw1 : 1 < w := lt_of_lt_of_le (by norm_num) hw2
      have hv1 : 1 < v := lt_of_lt_of_le (by norm_num) hv2
      have hlogw : 0 < Real.log w := Real.log_pos hw1
      have hlogv : 0 < Real.log v := Real.log_pos hv1
      have hHτ0 : 0 ≤ H τ := hH0 τ ⟨le_rfl, hτσ⟩
      have hI0 : 0 ≤ I := by
        dsimp [I]
        exact intervalIntegral.integral_nonneg hτσ hH0
      have hHle : ∀ t ∈ Set.Icc τ σ, H t ≤ H τ := by
        intro t ht
        have ht0 : 0 < t := hτ.trans_le ht.1
        have hHt0 : 0 ≤ H t := hH0 t ht
        have hprod := hHt (show τ ∈ Set.Icc τ σ from ⟨le_rfl, hτσ⟩) ht ht.1
        have hscale : H t * τ ≤ H t * t :=
          mul_le_mul_of_nonneg_left ht.1 hHt0
        have : H t * τ ≤ H τ * τ := by nlinarith
        nlinarith
      have hIle : I ≤ H τ * (σ - τ) := by
        have hmono := intervalIntegral.integral_mono_on hτσ
          (hHcont.intervalIntegrable τ σ)
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => H τ) volume τ σ)
          hHle
        simpa [I, mul_comm] using hmono
      have hratio : suzukiLocalRatio S v z ≤
          (τ / s) * (1 + K / Real.log v) := by
        have hloc := hlocal v z hv2 hvz
        unfold suzukiLocalRatio
        calc
          (∏ p ∈ S.prodPrimes.primeFactors.filter
              (fun p : ℕ => v ≤ (p : ℝ) ∧ (p : ℝ) < z),
              (1 - S.nu p)⁻¹) ≤
              Real.log z / Real.log v * (1 + K / Real.log v) := hloc
          _ = (τ / s) * (1 + K / Real.log v) := by
            have hD0 : 0 < D := zero_lt_one.trans hD
            have hlogs : Real.log z = Real.log D / s := by
              rw [hz, Real.log_rpow hD0]
              ring
            have hlogτ : Real.log v = Real.log D / τ := by
              rw [hv, Real.log_rpow hD0]
              ring
            rw [hlogs, hlogτ]
            field_simp [ne_of_gt (Real.log_pos hD)]
      have hB0 : 0 ≤ (1 / τ) * I + 2 * K * H τ / Real.log w := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hratio hB0
      have hlogv_formula : Real.log v = Real.log D / τ := by
        have hD0 : 0 < D := zero_lt_one.trans hD
        rw [hv, Real.log_rpow hD0]
        ring
      have hlogw_formula : Real.log w = Real.log D / σ := by
        have hD0 : 0 < D := zero_lt_one.trans hD
        rw [hw, Real.log_rpow hD0]
        ring
      have hcross : K / Real.log v * (I / s) ≤
          (K * H τ / Real.log w) * (τ / s) := by
        have hK0 : 0 ≤ K := by linarith
        have hστ : σ - τ ≤ σ := by linarith
        have hIσ : I ≤ H τ * σ :=
          hIle.trans (mul_le_mul_of_nonneg_left hστ hHτ0)
        let C : ℝ := K * τ / (Real.log D * s)
        have hC0 : 0 ≤ C := by
          dsimp [C]
          exact div_nonneg (mul_nonneg hK0 hτ.le)
            (mul_nonneg (Real.log_pos hD).le hs.le)
        have hmulI := mul_le_mul_of_nonneg_left hIσ hC0
        rw [hlogv_formula, hlogw_formula]
        have hs0 : s ≠ 0 := ne_of_gt hs
        have hτ0 : τ ≠ 0 := ne_of_gt hτ
        have hσ0' : σ ≠ 0 := ne_of_gt hσ
        have hlogD0 : Real.log D ≠ 0 := ne_of_gt (Real.log_pos hD)
        calc
          K / (Real.log D / τ) * (I / s) = C * I := by
            dsimp [C]
            field_simp
          _ ≤ C * (H τ * σ) := hmulI
          _ = (K * H τ / (Real.log D / σ)) * (τ / s) := by
            dsimp [C]
            field_simp
      have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
        have h := Real.log_two_gt_d9
        norm_num at h ⊢
        linarith
      have hlog2v : Real.log 2 ≤ Real.log v := by
        exact Real.strictMonoOn_log.monotoneOn (by norm_num)
          (zero_lt_one.trans hv1) hv2
      have hlogv23 : (2 / 3 : ℝ) < Real.log v := hlog2.trans_le hlog2v
      have honeK : 1 + K / Real.log v ≤ 2 * K := by
        have hdiv : K / Real.log v ≤ (3 / 2 : ℝ) * K := by
          rw [div_le_iff₀ hlogv]
          have hK0 : 0 ≤ K := by linarith
          nlinarith
        linarith
      have hA0 : 0 ≤ τ / s := div_nonneg hτ.le hs.le
      have herr0 : 0 ≤ 2 * K * H τ / Real.log w := by positivity
      have herrScale :
          (τ / s) * (1 + K / Real.log v) *
              (2 * K * H τ / Real.log w) ≤
            (4 * K^2 * H τ / Real.log w) * (τ / s) := by
        have hm := mul_le_mul_of_nonneg_left honeK hA0
        have hm' := mul_le_mul_of_nonneg_right hm herr0
        calc
          (τ / s) * (1 + K / Real.log v) *
              (2 * K * H τ / Real.log w) ≤
              ((τ / s) * (2 * K)) * (2 * K * H τ / Real.log w) := hm'
          _ = (4 * K^2 * H τ / Real.log w) * (τ / s) := by ring
      have hcoarse :
          (K * H τ / Real.log w) * (τ / s) +
              (4 * K^2 * H τ / Real.log w) * (τ / s) ≤
            (6 * K^2 * H τ / Real.log w) * (τ / s) := by
        have hunit : 0 ≤ (H τ / Real.log w) * (τ / s) := by positivity
        have hK0 : 0 ≤ K := by linarith
        calc
          (K * H τ / Real.log w) * (τ / s) +
              (4 * K^2 * H τ / Real.log w) * (τ / s) =
              (K + 4 * K^2) * ((H τ / Real.log w) * (τ / s)) := by ring
          _ ≤ (6 * K^2) * ((H τ / Real.log w) * (τ / s)) := by
            apply mul_le_mul_of_nonneg_right _ hunit
            nlinarith
          _ = (6 * K^2 * H τ / Real.log w) * (τ / s) := by ring
      calc
        suzukiLocalRatio S v z *
            ((1 / τ) * I + 2 * K * H τ / Real.log w) ≤
            (τ / s) * (1 + K / Real.log v) *
              ((1 / τ) * I + 2 * K * H τ / Real.log w) := hmul
        _ = (1 / s) * I + K / Real.log v * (I / s) +
              (τ / s) * (1 + K / Real.log v) *
                (2 * K * H τ / Real.log w) := by
              field_simp
        _ ≤ (1 / s) * I +
              (K * H τ / Real.log w) * (τ / s) +
              (4 * K^2 * H τ / Real.log w) * (τ / s) := by
            nlinarith
        _ ≤ (1 / s) * I +
              (6 * K^2 * H τ / Real.log w) * (τ / s) := by
            linarith
        _ = _ := rfl


end MathlibNt.SieveTheory.SwitchingPrinciple
