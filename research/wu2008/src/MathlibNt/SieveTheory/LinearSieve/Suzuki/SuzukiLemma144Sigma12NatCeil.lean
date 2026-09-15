import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveGlobalScaling
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NatCeilPowerCarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim1413Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISuccessor

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option maxHeartbeats 1600000

/-! Natural-ceiling closure of the `Σ₁₂` input.  The finite sum itself, a
Claim-14.6 conclusion, and `mainSum` are never assumed. -/

/-- Natural-ceiling version of the global `Σ₁₂` estimate.  The strict carrier
below `D^(1/s)` is transported exactly through `z = ⌈D^(1/s)⌉₊`; no equality
between the real cast of `z` and the power cutoff is used. -/
theorem sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil
    {S : BoundingSieve} {H : Section13HatLayers}
    {β C K d Δ w v s τ σ : ℝ} {N D znat : ℕ}
    (hH : Section13HatContract H β)
    (hD : 1 < (D : ℝ))
    (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ (D : ℝ) ^ (1 / s))
    (hz : znat = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hv : v = (D : ℝ) ^ (1 / τ))
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hτ : H.betaHat + (ErrorSign.ofDepth N).epsilon < τ)
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
  exact sigma12_middle_le_qD_lemma8_7 (S := S) (H := H)
    (ErrorSign.ofDepth N) Q (fun p hp hpw hpv => le_rfl)
    hH hD (by simpa [x] using hv2.trans hvz) hv2 hw2 hwv
    (by simpa [x] using hvz)
    (by simp [x]) hv hw hτ hτσ hK hlocal hii

noncomputable def sigma12ContractionMultiplier (σ Δ : ℝ) : ℝ :=
  (1 - 1 / σ) ^ (1 - Δ)

noncomputable def sigma12InheritedBudget
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) * errorEnvelope H N (D : ℝ) d s

noncomputable def sigma12EndpointRemainder
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D z : ℕ) (C K d Δ s σ : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ) *
      ((6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s /
          Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))

/-- The source contraction has a canonical strict midpoint enlargement. -/
theorem exists_sigma12_sameC_strictFactor
    {σ Δ : ℝ} (hσ : 1 < σ) (hΔ : Δ < 1) :
    ∃ q : Lemma144StrictFactor,
      q.ρ = (1 + sigma12ContractionMultiplier σ Δ) / 2 ∧
      sigma12ContractionMultiplier σ Δ < q.ρ := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hbasepos : 0 < 1 - 1 / σ := sub_pos.mpr ((div_lt_one hσ0).2 hσ)
  have hbaselt : 1 - 1 / σ < 1 := by
    have : 0 < 1 / σ := one_div_pos.mpr hσ0
    linarith
  have hexp : 0 < 1 - Δ := sub_pos.mpr hΔ
  have ha0 : 0 ≤ sigma12ContractionMultiplier σ Δ := by
    exact Real.rpow_nonneg hbasepos.le _
  have ha1 : sigma12ContractionMultiplier σ Δ < 1 := by
    exact Real.rpow_lt_one hbasepos.le hbaselt hexp
  let q : Lemma144StrictFactor :=
    { ρ := (1 + sigma12ContractionMultiplier σ Δ) / 2
      nonneg := by linarith
      lt_one := by linarith }
  refine ⟨q, rfl, ?_⟩
  dsimp [q]
  linarith

/-- For all sufficiently large natural `D`, the raw moving Claim-14.6 sources,
the natural-ceiling `Σ₁₂` bridge, and Lemma 8.7 give a strict same-constant
contraction. -/
theorem eventually_sigmaTwelve_internal_contraction_sameC
    {S : BoundingSieve} {H : Section13HatLayers}
    {C K d Δ s : ℝ} {N : ℕ}
    (hH : Section13HatSourceContract H) (hN : 2 ≤ N)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hs0 : 0 < s)
    (hsLower : 2 + (ErrorSign.ofDepth N).epsilon ≤ s)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hC : 0 ≤ C) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ (D z : ℕ), D₀ ≤ (D : ℝ) →
      1 < sourceSigma (D : ℝ) d →
      s ≤ sourceSigma (D : ℝ) d →
      1 < (D : ℝ) →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s) →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      H.betaHat + (ErrorSign.ofDepth N).epsilon < s →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ) / 2 ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ *
              sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          q.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) := by
  obtain ⟨D₀, hD₀, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  refine ⟨D₀, hD₀, ?_⟩
  intro D z hDlarge hσ1 hsσ hD hv2 hw2 hwv hz hthreshold hCeil hT
  obtain ⟨_hi, hii, hiii⟩ := h146 (D : ℝ) hDlarge
  let σ : ℝ := sourceSigma (D : ℝ) d
  let a : ℝ := sigma12ContractionMultiplier σ Δ
  let A : ℝ := C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ)
  let B : ℝ := errorEnvelope H N (D : ℝ) d s
  let R : ℝ := (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
      (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)
  have h12 := sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil
    (S := S) (H := H) (β := (2 : ℝ)) (C := C) (K := K) (d := d) (Δ := Δ)
    (w := (D : ℝ) ^ (1 / σ)) (v := (D : ℝ) ^ (1 / s))
    (s := s) (τ := s) (σ := σ) (N := N) (D := D) (znat := z)
    hH.toSection13HatContract hD hv2 hw2 hwv le_rfl hz rfl rfl
    hthreshold hsσ hK hlocal (by simpa [σ] using hii) hC hΔ0.le
    (by simpa [σ] using hCeil) (by simpa [σ] using hT)
    (by
      intro p hp hpw hpv
      have hcp := hCeil p hp hpw hpv
      exact claim14_13_pointwise_carrier H (by omega : 1 ≤ N) hcp.1 hcp.2 hd1 hΔ0
        (hT p hp hpw hpv))
  have hint := hiii (ErrorSign.ofDepth N) s hsLower hsσ
  have hintScaled :
      (1 / s) * (∫ t in s..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤ a * B := by
    have hmul := mul_le_mul_of_nonneg_left hint.le (one_div_nonneg.mpr hs0.le)
    calc
      (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
          (1 / s) * (a * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by
            simpa [σ, a, sigma12ContractionMultiplier] using hmul
      _ = a * ((1 / s) * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by ring
      _ = a * B := by rw [one_div_mul_lambda_eq_errorEnvelope H hs0]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  have hraw :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ N D σ s ≤
        a * (A * B) + A * R := by
    apply h12.trans
    rw [show C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in s..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
              (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))) =
        A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) by
            dsimp [A, R]; ring]
    have hinside :
        (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R ≤
          a * B + R := add_le_add hintScaled (le_refl R)
    calc
      A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) ≤
          A * (a * B + R) := mul_le_mul_of_nonneg_left hinside hA
      _ = a * (A * B) + A * R := by ring
  obtain ⟨q, hq, haq⟩ := exists_sigma12_sameC_strictFactor hσ1 hΔ1
  have hB : 0 ≤ B := by
    apply errorEnvelope_nonneg H N hD hs0.le
    exact (hH.positive (ErrorSign.ofDepth N) s hs0).le
  have hbudget : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨q, by simpa [σ] using hq, ?_, ?_⟩
  · simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hraw
  · have hρ : a ≤ q.ρ := haq.le
    have hslack : a * (A * B) + A * R ≤ q.ρ * (A * B) + A * R := by
      exact add_le_add (mul_le_mul_of_nonneg_right hρ hbudget) le_rfl
    have hfinal := hraw.trans hslack
    simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hfinal


end MathlibNt.SieveTheory
