import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeil

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

namespace SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Closed-endpoint form of the `qD` clamp conditions.  The only extra case
relative to the legacy strict theorem is the lower endpoint itself; continuity
extends weighted antitonicity from `Ioc` to that endpoint. -/
lemma qDClamp_conditions_of_claim14_6_ii_closed
    {H : Section13HatLayers} {β D d Δ τ σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hτ : H.betaHat + sign.epsilon ≤ τ) (_hτσ : τ ≤ σ)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    Continuous (qDClamp H sign.opposite D d Δ τ) ∧
      (∀ t ∈ Icc τ σ, 0 ≤ qDClamp H sign.opposite D d Δ τ t) ∧
      AntitoneOn (fun t => qDClamp H sign.opposite D d Δ τ t * t) (Icc τ σ) := by
  have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
  have hτ1 : 1 < τ := by
    rw [hH.betaHat_eq] at hτ
    linarith [hH.beta_gt_one]
  have hqcont : ContinuousOn (qD H sign.opposite D d Δ) (Ioi 1) := by
    unfold qD
    have hlog : 0 < Real.log D := Real.log_pos hD
    have htpos : ∀ t ∈ Ioi (1 : ℝ), 0 < t := fun t ht => zero_lt_one.trans ht
    have htmpos : ∀ t ∈ Ioi (1 : ℝ), 0 < t - 1 := fun t ht => sub_pos.mpr ht
    have htpow : ContinuousOn (fun t : ℝ => t ^ d) (Ioi 1) :=
      continuousOn_id.rpow continuousOn_const
        (fun t ht => Or.inl (ne_of_gt (htpos t ht)))
    have hbase : ContinuousOn (fun t : ℝ => 1 + t ^ d / Real.log D) (Ioi 1) :=
      continuousOn_const.add (htpow.div_const _)
    have hbasePos : ∀ t ∈ Ioi (1 : ℝ), 0 < 1 + t ^ d / Real.log D := by
      intro t ht
      have : 0 ≤ t ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg (htpos t ht).le _) hlog.le
      linarith
    have houter : ContinuousOn
        (fun t : ℝ => (1 + t ^ d / Real.log D) ^ (t - 1)) (Ioi 1) :=
      hbase.rpow (continuousOn_id.sub continuousOn_const)
        (fun t ht => Or.inl (ne_of_gt (hbasePos t ht)))
    have hshift : ContinuousOn
        (fun t : ℝ => (t - 1) ^ (H.kappaHat - 1 + 1)) (Ioi 1) :=
      (continuousOn_id.sub continuousOn_const).rpow continuousOn_const
        (fun t ht => Or.inl (ne_of_gt (htmpos t ht)))
    have hratio : ContinuousOn (fun t : ℝ => t / (t - 1)) (Ioi 1) :=
      continuousOn_id.div (continuousOn_id.sub continuousOn_const)
        (fun t ht => ne_of_gt (htmpos t ht))
    have hratioPow : ContinuousOn (fun t : ℝ => (t / (t - 1)) ^ Δ) (Ioi 1) :=
      hratio.rpow continuousOn_const (fun t ht =>
        Or.inl (ne_of_gt (div_pos (htpos t ht) (htmpos t ht))))
    have hTshift : ContinuousOn (fun t : ℝ => H.T sign.opposite (t - 1)) (Ioi 1) :=
      (hH.continuous sign.opposite).comp
        (continuousOn_id.sub continuousOn_const) (by
          intro t ht
          exact show 0 < t - 1 from sub_pos.mpr (show 1 < t from ht))
    exact ((houter.mul hshift).mul hTshift).mul hratioPow
  have hcont : Continuous (qDClamp H sign.opposite D d Δ τ) := by
    apply hqcont.comp_continuous (continuous_const.max continuous_id)
    intro t
    exact hτ1.trans_le (le_max_left τ t)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    rw [qDClamp_eq_of_le H sign.opposite D d Δ ht.1]
    exact (qD_pos H sign.opposite hD (hτ1.trans_le ht.1)
      (hH.positive sign.opposite (t - 1)
        (sub_pos.mpr (hτ1.trans_le ht.1)))).le
  · let f : ℝ → ℝ := fun t => qDClamp H sign.opposite D d Δ τ t * t
    have hfcont : Continuous f := hcont.mul continuous_id
    intro x hx y hy hxy
    change f y ≤ f x
    by_cases hxy' : x = y
    · simp [hxy']
    have hxylt : x < y := lt_of_le_of_ne hxy hxy'
    by_cases hxopen : H.betaHat + sign.epsilon < x
    · dsimp [f]
      rw [qDClamp_eq_of_le H sign.opposite D d Δ hx.1,
        qDClamp_eq_of_le H sign.opposite D d Δ hy.1]
      exact hii sign ⟨hxopen, hx.2⟩
        ⟨hxopen.trans hxylt, hy.2⟩ hxy
    · have hxeq : x = H.betaHat + sign.epsilon :=
        le_antisymm (le_of_not_gt hxopen) (hτ.trans hx.1)
      have hsub : Ioc x y ⊆ {u | f y ≤ f u} := by
        intro u hu
        change qDClamp H sign.opposite D d Δ τ y * y ≤
          qDClamp H sign.opposite D d Δ τ u * u
        rw [qDClamp_eq_of_le H sign.opposite D d Δ hy.1,
          qDClamp_eq_of_le H sign.opposite D d Δ (hx.1.trans hu.1.le)]
        exact hii sign
          ⟨by simpa [hxeq] using hu.1, hu.2.trans hy.2⟩
          ⟨by simpa [hxeq] using hxylt, hy.2⟩ hu.2
      have hclosed : IsClosed {u | f y ≤ f u} :=
        isClosed_le continuous_const hfcont
      apply (closure_minimal hsub hclosed)
      rw [closure_Ioc (ne_of_lt hxylt)]
      exact ⟨le_rfl, hxy⟩

/-- Lemma 8.7 for `qD` at the source-faithful closed lower endpoint. -/
theorem lemma8_7_qD_of_claim14_6_ii_closed
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} (sign : ErrorSign)
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + sign.epsilon ≤ τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (qD H sign.opposite D d Δ) ≤
      (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) +
        (6 * K ^ 2 * qD H sign.opposite D d Δ τ / Real.log w) * (τ / s) := by
  let Q := qDClamp H sign.opposite D d Δ τ
  obtain ⟨hcont, hnonneg, hanti⟩ :=
    qDClamp_conditions_of_claim14_6_ii_closed hH sign hD hτ hτσ hii
  have h87 := suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz
    hz hv hw hcont hnonneg hanti hK hlocal
  have hτpos : 0 < τ := by
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    rw [hH.betaHat_eq] at hτ
    linarith [hH.beta_gt_one]
  have hcoord : ∀ x ∈ Icc w v, Real.log D / Real.log x ∈ Icc τ σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hτpos hτσ hv hw hx
  have hprime : suzukiLemmaEightSevenPrimeSum S D w v z Q =
      suzukiLemmaEightSevenPrimeSum S D w v z (qD H sign.opposite D d Δ) := by
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show Q (Real.log D / Real.log p) =
        qD H sign.opposite D d Δ (Real.log D / Real.log p) by
      exact qDClamp_eq_of_le H sign.opposite D d Δ ht.1]
  have hint : (∫ t in τ..σ, Q t) =
      ∫ t in τ..σ, qD H sign.opposite D d Δ t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hτσ]
    intro t ht
    exact qDClamp_eq_of_le H sign.opposite D d Δ ht.1
  rw [hprime, hint, qDClamp_eq_of_le H sign.opposite D d Δ le_rfl] at h87
  exact h87

/-- Closed-endpoint `Σ₁₂` middle-range assembly. -/
theorem sigma12_middle_le_qD_lemma8_7_closed
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} (sign : ErrorSign) (R : ℝ → ℝ)
    (hmajorant : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      R (Real.log D / Real.log p) ≤
        qD H sign.opposite D d Δ (Real.log D / Real.log p))
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + sign.epsilon ≤ τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    suzukiLemmaEightSevenPrimeSum S D w v z R ≤
      (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) +
        (6 * K ^ 2 * qD H sign.opposite D d Δ τ / Real.log w) *
          (τ / s) := by
  exact (suzukiLemmaEightSevenPrimeSum_mono_on_middle
    S D w v z R (qD H sign.opposite D d Δ) hmajorant).trans
      (lemma8_7_qD_of_claim14_6_ii_closed (S := S) (H := H) (sign := sign)
        hH hD hz2 hv2 hw2 hwv hvz hz hv hw hτ hτσ hK hlocal hii)

end SwitchingPrinciple.SuzukiLemma144KappaOne



/-- Natural-ceiling `Σ₁₂` estimate at the closed lower endpoint. -/
theorem sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil_closed
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ w v s τ σ : ℝ} {N D znat : ℕ}
    (hH : Section13HatContract H β)
    (hD : 1 < (D : ℝ))
    (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ (D : ℝ) ^ (1 / s))
    (hz : znat = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ τ)
    (hτσ : τ ≤ σ) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hCeil : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    sigmaTwelve S.prodPrimes.primeFactors S.nu
        (fun p => suzukiVProduct S (p : ℝ))
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        (suzukiVProduct S (znat : ℝ)) C K Δ N D σ τ ≤
      C * Real.exp (Real.sqrt K) * suzukiVProduct S (znat : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in τ..σ,
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 *
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ τ /
              Real.log w) * (τ / s))) := by
  classical
  let x : ℝ := (D : ℝ) ^ (1 / s)
  let Q : ℝ → ℝ := qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ
  have hDnat : 0 < D := by exact_mod_cast (show (0 : ℝ) < D by linarith)
  have hx : 0 < x := natCast_rpow_one_div_pos hDnat s
  have hV : suzukiVProduct S (znat : ℝ) = suzukiVProduct S x :=
    suzukiVProduct_natCeil_eq_power S hx (by simpa [x] using hz)
  have hcarrier : sigmaOneCarrier S.prodPrimes.primeFactors D σ τ =
      S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v) := by
    ext p
    simp only [sigmaOneCarrier, Finset.mem_filter]
    rw [hw, hv]
  have hsum :
      (∑ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ τ,
        S.nu p * suzukiVProduct S (p : ℝ) / suzukiVProduct S (znat : ℝ) *
          errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
            (inheritedCoordinate D p) *
          Real.log ((D ⌈/⌉ p : ℕ) : ℝ) ^ (-Δ)) ≤
        (Real.log (D : ℝ)) ^ (-Δ) *
          suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v x Q := by
    rw [hcarrier]
    unfold suzukiLemmaEightSevenPrimeSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
    have hnu : 0 ≤ S.nu p := (S.nu_pos_of_prime p hpprime hpdiv).le
    have hpv : (p : ℝ) < v := hp'.2.2
    have hpx : (p : ℝ) < x := hpv.trans_le (by simpa [x] using hvz)
    have hsuffix : 0 ≤ ∏ q ∈ S.prodPrimes.primeFactors.filter
        (fun q : ℕ => p ≤ q ∧ (q : ℝ) < x), (1 - S.nu q)⁻¹ := by
      apply Finset.prod_nonneg
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
      have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hq'.1).2.1
      exact inv_nonneg.mpr
        (sub_nonneg.mpr (S.nu_lt_one_of_prime q hqprime hqdiv).le)
    have herr := naturalCeil_inherited_error_le_claim14_13 H
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).1
      (hCeil p hp'.1 hp'.2.1 hp'.2.2).2 hΔ
      (hT p hp'.1 hp'.2.1 hp'.2.2)
      (h1413 p hp'.1 hp'.2.1 hp'.2.2)
    rw [show S.nu p * suzukiVProduct S (p : ℝ) /
        suzukiVProduct S (znat : ℝ) =
        S.nu p * (suzukiVProduct S (p : ℝ) /
          suzukiVProduct S (znat : ℝ)) by ring]
    rw [hV, suzukiVProduct_div_eq_suffix S hpx]
    dsimp [Q]
    have hmul := mul_le_mul_of_nonneg_left herr (mul_nonneg hnu hsuffix)
    nlinarith
  have houter : 0 ≤ C * Real.exp (Real.sqrt K) * suzukiVProduct S (znat : ℝ) :=
    mul_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S _).le
  unfold sigmaTwelve
  apply (mul_le_mul_of_nonneg_left hsum houter).trans
  apply mul_le_mul_of_nonneg_left _ houter
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  exact sigma12_middle_le_qD_lemma8_7_closed (S := S) (H := H)
    (ErrorSign.ofDepth N) Q (fun p hp hpw hpv => le_rfl)
    hH hD (by simpa [x] using hv2.trans hvz) hv2 hw2 hwv
    (by simpa [x] using hvz)
    (by simp [x]) hv hw hτ hτσ hK hlocal hii


end MathlibNt.SieveTheory
