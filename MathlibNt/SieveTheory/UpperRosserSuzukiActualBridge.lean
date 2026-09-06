import MathlibNt.SieveTheory.LinearSieve.Rosser.LowerRosserAccumulatorNormalization
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserQuantitativeJointDiagonal

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The unnormalised upper-Rosser boundary layer at pair depth `k`.
The distinguished terminal prime is external to the stored even chain, so this
is the odd Suzuki source layer `2*k+1`.  Its terminal factor is the Euler product
strictly below `q`, not an inverse suffix product. -/
noncomputable def upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) : ℝ :=
  ∑ q ∈ suzukiSupportedBelow S z,
    S.nu q * sourceDiscreteEuler S q *
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        ((suzukiSupportedBelow S z).filter (fun p => q < p)) k

private theorem upper_ceilDiv_ceilDiv_eq
    {D a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (D ⌈/⌉ a) ⌈/⌉ b = D ⌈/⌉ (a * b) := by
  exact MathlibNt.SieveTheory.ceilDiv_ceilDiv_eq ha hb

private theorem upperSuzukiUnnormalizedLayer_succ
    (S : BoundingSieve) (D z k : ℕ) :
    upperSuzukiUnnormalizedLayer S D z (k + 1) =
      ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => p ^ 3 < D),
        S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
          S.nu p₁ * upperSuzukiUnnormalizedLayer S
            (D ⌈/⌉ (p₀ * p₁)) p₁ k := by
  classical
  let Z := suzukiSupportedBelow S z
  unfold upperSuzukiUnnormalizedLayer
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1)) = _
  have hexpand (q : ℕ) (hq : q ∈ Z) :
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (Z.filter (fun p => q < p)) (k + 1) =
        ∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k := by
    apply upperRosserBoundaryChainsFixedDepthDensity_succ S.nu
    · simp
    · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    · intro p hp
      exact Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
  have hrewrite :
      (∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          upperRosserBoundaryChainsFixedDepthDensity S.nu D q
            (Z.filter (fun p => q < p)) (k + 1)) =
      ∑ q ∈ Z,
        S.nu q * sourceDiscreteEuler S q *
          (∑ p₀ ∈ Z.filter (fun p => q < p),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu p₀ * S.nu p₁ *
                upperRosserBoundaryChainsFixedDepthDensity S.nu
                  (D ⌈/⌉ (p₀ * p₁)) q
                  ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hexpand q hq]
  rw [hrewrite]
  change (∑ q ∈ Z,
      S.nu q * sourceDiscreteEuler S q *
        (∑ p₀ ∈ Z.filter (fun p => q < p),
          ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
              (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            S.nu p₀ * S.nu p₁ *
              upperRosserBoundaryChainsFixedDepthDensity S.nu
                (D ⌈/⌉ (p₀ * p₁)) q
                ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k)) = _
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ p₀ ∈ Z,
          ∑ q ∈ Z.filter (fun q => q < p₀),
            ∑ p₁ ∈ (Z.filter (fun p => q < p)).filter
                (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_comm'
          intro q p₀
          simp only [Finset.mem_filter]
          tauto
    _ = ∑ p₀ ∈ Z,
          ∑ p₁ ∈ Z.filter (fun p₁ => p₁ < p₀ ∧ p₀ ^ 3 < D),
            ∑ q ∈ Z.filter (fun q => q < p₁),
              S.nu q * sourceDiscreteEuler S q *
                (S.nu p₀ * S.nu p₁ *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((Z.filter (fun p => q < p)).filter (fun p => p < p₁)) k) := by
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_comm'
          intro q p₁
          constructor
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            have hp₁base := Finset.mem_filter.mp hp₁'.1
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hp₁base.2⟩,
              Finset.mem_filter.mpr ⟨hp₁base.1, hp₁'.2⟩⟩
          · intro h
            rcases h with ⟨hq, hp₁⟩
            have hq' := Finset.mem_filter.mp hq
            have hp₁' := Finset.mem_filter.mp hp₁
            exact ⟨Finset.mem_filter.mpr ⟨hq'.1, hq'.2.trans hp₁'.2.1⟩,
              Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨hp₁'.1, hq'.2⟩, hp₁'.2⟩⟩
    _ = ∑ p₀ ∈ Z.filter (fun p => p ^ 3 < D),
          S.nu p₀ * ∑ p₁ ∈ suzukiSupportedBelow S p₀,
            S.nu p₁ *
              (∑ q ∈ suzukiSupportedBelow S p₁,
                S.nu q * sourceDiscreteEuler S q *
                  upperRosserBoundaryChainsFixedDepthDensity S.nu
                    (D ⌈/⌉ (p₀ * p₁)) q
                    ((suzukiSupportedBelow S p₁).filter (fun p => q < p)) k) := by
          rw [Finset.sum_filter]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          have hp₀z : p₀ < z := (Finset.mem_filter.mp hp₀).2
          by_cases hcut : p₀ ^ 3 < D
          · rw [if_pos hcut]
            apply Finset.sum_congr
            · ext p₁
              simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hp₁S, hp₁z⟩, hp₁p₀, _⟩
                exact ⟨hp₁S, hp₁p₀⟩
              · rintro ⟨hp₁S, hp₁p₀⟩
                exact ⟨⟨hp₁S, hp₁p₀.trans hp₀z⟩,
                  hp₁p₀, hcut⟩
            · intro p₁ hp₁
              have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
              have hp₁z : p₁ < z := hp₁p₀.trans hp₀z
              apply Finset.sum_congr
              · ext q
                simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                constructor
                · rintro ⟨⟨hqS, hqz⟩, hqp₁⟩
                  exact ⟨hqS, hqp₁⟩
                · rintro ⟨hqS, hqp₁⟩
                  exact ⟨⟨hqS, hqp₁.trans hp₁z⟩,
                    hqp₁⟩
              · intro q hq
                have hcarrier :
                    (Z.filter (fun p => q < p)).filter (fun p => p < p₁) =
                      (suzukiSupportedBelow S p₁).filter (fun p => q < p) := by
                  ext p
                  simp only [Z, suzukiSupportedBelow, Finset.mem_filter]
                  constructor
                  · rintro ⟨⟨⟨hpS, hpz⟩, hqp⟩, hpp₁⟩
                    exact ⟨⟨hpS, hpp₁⟩, hqp⟩
                  · rintro ⟨⟨hpS, hpp₁⟩, hqp⟩
                    exact ⟨⟨⟨hpS, hpp₁.trans hp₁z⟩, hqp⟩, hpp₁⟩
                rw [hcarrier]
                ring
          · rw [if_neg hcut]
            apply Finset.sum_eq_zero
            intro p₁ hp₁
            exact False.elim (hcut (Finset.mem_filter.mp hp₁).2.2)
    _ = _ := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          rfl

/-- Exact arbitrary-depth odd-layer bridge.  Pair depth `k` in the production
upper boundary has `2*k` stored primes plus the external terminal prime, hence
it is Suzuki source depth `2*k+1`.  The only base-domain hypothesis is `1 < D`,
needed because the empty stored chain must still be active. -/
theorem suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) (hD : 1 < D) :
    suzukiSourceV S (2 * k + 1) D z =
      upperSuzukiUnnormalizedLayer S D z k := by
  induction k generalizing D z with
  | zero =>
      classical
      rw [show 2 * 0 + 1 = 1 by omega, suzukiSourceV_one]
      change (∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => D ≤ q ^ 3),
          S.nu q * sourceDiscreteEuler S q) =
        ∑ q ∈ suzukiSupportedBelow S z,
          S.nu q * sourceDiscreteEuler S q *
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              ((suzukiSupportedBelow S z).filter (fun p => q < p)) 0
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      have hqprime : q.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      rw [upperRosserBoundaryChainsFixedDepthDensity_zero S.nu hD
        (by simp) hqprime]
      · by_cases hcube : D ≤ q ^ 3 <;> simp [hcube]
      · intro p hp
        exact (Finset.mem_filter.mp hp).2.le
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        suzukiSourceV_odd_succ_eq_upper_only S (by omega)
          (show Odd (2 * k + 3) from ⟨k + 1, by omega⟩)]
      rw [upperSuzukiUnnormalizedLayer_succ]
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      apply congrArg (fun x : ℝ => S.nu p₀ * x)
      rw [suzukiSourceV_succ_eq_unrestricted S (by omega)
        (by
          intro hodd
          exact (Nat.not_odd_iff_even.mpr
            (show Even (2 * k + 2) from ⟨k + 1, by omega⟩) hodd).elim)]
      apply Finset.sum_congr rfl
      intro p₁ hp₁
      have hp₀pos : 0 < p₀ := (Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp hp₀).1).1).pos
      have hp₁prime : p₁.Prime := Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp hp₁).1
      have hDres : 1 < (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
        have hcut : p₀ ^ 3 < D := (Finset.mem_filter.mp hp₀).2
        have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2
        have hle : p₀ ≤ (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
          by_contra hn
          have hc : (D ⌈/⌉ p₀) ⌈/⌉ p₁ < p₀ := Nat.lt_of_not_ge hn
          have hmul₁ := (ceilDiv_le_iff_le_mul hp₁prime.pos).1 hc.le
          have hmul₀ := (ceilDiv_le_iff_le_mul hp₀pos).1 hmul₁
          have hp₁le : p₁ ≤ p₀ := hp₁p₀.le
          nlinarith [hp₁prime.two_le]
        exact hp₁prime.one_lt.trans_le (hp₁p₀.le.trans hle)
      rw [ih ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁ hDres,
        upper_ceilDiv_ceilDiv_eq hp₀pos hp₁prime.pos]

/-- The actual odd Suzuki parity aggregate is the finite sum of the first `m`
production upper-boundary pair layers. -/
theorem suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
    (S : BoundingSieve) (D z m : ℕ) (hD : 1 < D) :
    suzukiActualT S (2 * m + 1) D z =
      ∑ k ∈ Finset.range (m + 1), upperSuzukiUnnormalizedLayer S D z k := by
  induction m with
  | zero =>
      rw [show 2 * 0 + 1 = 1 by omega, suzukiActualT_one,
        suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z 0 hD]
      simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        suzukiActualT_add_two]
      have hlayer : suzukiSourceV S (2 * m + 1 + 2) D z =
          upperSuzukiUnnormalizedLayer S D z (m + 1) := by
        simpa only [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega] using
          suzukiSourceV_odd_eq_upperSuzukiUnnormalizedLayer S D z (m + 1) hD
      rw [hlayer, ih]
      simpa only [add_comm] using (Finset.sum_range_succ
        (fun k => upperSuzukiUnnormalizedLayer S D z k) (m + 1)).symm


end MathlibNt.SieveTheory
