import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteBoundaryTermination

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The canonical increasing list of supported primes below `z`. -/
noncomputable def suzukiSupportedBelowList (S : BoundingSieve) (z : ℕ) : List ℕ :=
  (suzukiSupportedBelow S z).sort (· ≤ ·)

@[simp] theorem suzukiSupportedBelowList_toFinset (S : BoundingSieve) (z : ℕ) :
    (suzukiSupportedBelowList S z).toFinset = suzukiSupportedBelow S z := by
  exact Finset.sort_toFinset _ _

private theorem foldr_insert_empty_eq_toFinset : ∀ qs : List ℕ,
    qs.foldr insert ∅ = qs.toFinset
  | [] => by simp
  | q :: qs => by simp [foldr_insert_empty_eq_toFinset qs]

private theorem lowerRosserBoundaryAccum_list_expansion
    (nu : ℕ → ℝ) (D : ℕ) : ∀ qs : List ℕ,
    qs.Nodup → qs.Pairwise (· < ·) →
    lowerRosserBoundaryAccum nu D ∅ qs =
      ∑ q ∈ qs.toFinset,
        nu q * (∏ r ∈ qs.toFinset.filter (fun r => r < q), (1 - nu r)) *
          lowerRosserBoundaryMass nu D q
            (qs.toFinset.filter (fun r => q < r))
  | [], _, _ => by simp [lowerRosserBoundaryAccum]
  | q :: qs, hnodup, hsorted => by
      have hn := List.nodup_cons.mp hnodup
      have hs := List.pairwise_cons.mp hsorted
      rw [lowerRosserBoundaryAccum,
        lowerRosserBoundaryAccum_list_expansion nu D qs hn.2 hs.2]
      have hqnot : q ∉ qs.toFinset := by simpa using hn.1
      simp only [List.toFinset_cons]
      have hlt : ∀ r ∈ qs.toFinset, q < r := by
        intro r hr
        exact hs.1 r (by simpa using hr)
      have hqPrefix : (insert q qs.toFinset).filter (fun r => r < q) = ∅ := by
        ext r
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hr, hrq⟩
          · omega
          · exact False.elim ((Nat.not_lt_of_ge (hlt r hr).le) hrq)
        · intro h
          simpa using h
      have hqSuffix : (insert q qs.toFinset).filter (fun r => q < r) = qs.toFinset := by
        ext r
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hr, hqr⟩
          · omega
          · exact hr
        · intro hr
          exact ⟨Or.inr hr, hlt r hr⟩
      rw [Finset.sum_insert hqnot, hqPrefix, hqSuffix,
        foldr_insert_empty_eq_toFinset]
      simp only [Finset.prod_empty, one_mul]
      have htail :
          (∑ r ∈ qs.toFinset,
            nu r * (∏ a ∈ (insert q qs.toFinset).filter (fun a => a < r),
              (1 - nu a)) *
              lowerRosserBoundaryMass nu D r
                ((insert q qs.toFinset).filter (fun a => r < a))) =
          (1 - nu q) *
            ∑ r ∈ qs.toFinset,
              nu r * (∏ a ∈ qs.toFinset.filter (fun a => a < r), (1 - nu a)) *
                lowerRosserBoundaryMass nu D r
                  (qs.toFinset.filter (fun a => r < a)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hqr := hlt r hr
        have hqnotPrefix : q ∉ qs.toFinset.filter (fun a => a < r) := by simp [hn.1]
        have hprefix :
            (insert q qs.toFinset).filter (fun a => a < r) =
              insert q (qs.toFinset.filter (fun a => a < r)) := by
          ext a
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨rfl | ha, har⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨ha, har⟩
          · rintro (rfl | ⟨ha, har⟩)
            · exact ⟨Or.inl rfl, hqr⟩
            · exact ⟨Or.inr ha, har⟩
        have hsuffix :
            (insert q qs.toFinset).filter (fun a => r < a) =
              qs.toFinset.filter (fun a => r < a) := by
          ext a
          simp only [mem_filter, mem_insert]
          constructor
          · rintro ⟨rfl | ha, hra⟩
            · exact False.elim ((Nat.not_lt_of_ge hqr.le) hra)
            · exact ⟨ha, hra⟩
          · rintro ⟨ha, hra⟩
            exact ⟨Or.inr ha, hra⟩
        rw [hprefix, hsuffix, Finset.prod_insert hqnotPrefix]
        ring
      rw [htail]
      ring

private theorem lowerRosserBoundaryMass_eq_sum_chains
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqmin : ∀ p ∈ P, q ≤ p) :
    lowerRosserBoundaryMass nu D q P =
      ∑ l ∈ lowerRosserBoundaryChains D q P, (l.map nu).prod := by
  unfold lowerRosserBoundaryMass
  rw [← sum_lowerRosserBoundary_eq_sum_chains D q P nu]
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro s hs
    have hsub : s ⊆ P := Finset.mem_powerset.mp hs
    exact (lowerRosserBoundarySet_iff_cube_le
      (fun h => hqP (hsub h)) hqprime
      (fun p hp => hqmin p (hsub hp))).symm
  · intro s hs
    rfl

/-- Every finite boundary powerset mass is the sum of all its exact even source
layers.  The range `P.card + 1` is a structural support bound, not a fixed-depth
replacement. -/
theorem lowerRosserBoundaryMass_eq_sum_fixedPairDepth0Density
    (nu : ℕ → ℝ) {D q : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqmin : ∀ p ∈ P, q ≤ p) :
    lowerRosserBoundaryMass nu D q P =
      ∑ k ∈ Finset.range (P.card + 1),
        lowerRosserBoundaryChainsFixedPairDepth0Density nu D q P k := by
  rw [lowerRosserBoundaryMass_eq_sum_chains nu hqP hqprime hqmin]
  unfold lowerRosserBoundaryChainsFixedPairDepth0Density
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨k, hk, huniq⟩ := lowerRosserBoundaryChains_exists_unique_depth hl
  obtain ⟨hnodup, _, hlsub, _⟩ :=
    (mem_lowerRosserBoundaryChains_iff hqP hqprime hqmin).mp hl
  have hlenle : l.length ≤ P.card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hlsub
  have hkRange : k ∈ Finset.range (P.card + 1) := by
    simp only [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single k]
  · simp [hk]
  · intro j hj hjk
    simp only [ite_eq_right_iff]
    intro hjlen
    exact False.elim (hjk (huniq j hjlen))
  · intro hknot
    exact False.elim (hknot hkRange)

/-- Exact expansion of the production accumulator over its canonical supported
prime list.  The prefix Euler product is the source terminal factor. -/
theorem lowerRosserBoundaryAccum_supportedBelow_eq_primeSum
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserBoundaryAccum S.nu D ∅ (suzukiSupportedBelowList S z) =
      ∑ q ∈ suzukiSupportedBelow S z,
        S.nu q * sourceDiscreteEuler S q *
          lowerRosserBoundaryMass S.nu D q
            ((suzukiSupportedBelow S z).filter (fun r => q < r)) := by
  classical
  rw [lowerRosserBoundaryAccum_list_expansion S.nu D
    (suzukiSupportedBelowList S z)
    (Finset.sort_nodup _ _) (Finset.sortedLT_sort _).pairwise,
    suzukiSupportedBelowList_toFinset]
  apply Finset.sum_congr rfl
  intro q hq
  have hqz : q < z := (Finset.mem_filter.mp hq).2
  apply congrArg (fun x : ℝ => S.nu q * x *
    lowerRosserBoundaryMass S.nu D q
      ((suzukiSupportedBelow S z).filter (fun r => q < r)))
  unfold sourceDiscreteEuler
  apply Finset.prod_congr
  · unfold suzukiSupportedBelow
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrS, hrz⟩, hrq⟩
      exact ⟨hrS, hrq⟩
    · rintro ⟨hrS, hrq⟩
      exact ⟨⟨hrS, hrq.trans hqz⟩, hrq⟩
  · intro r hr
    rfl

/-- The unnormalized exact pair-depth layer.  Unlike
`lowerSuzukiNormalizedLayer`, its terminal factor is Suzuki's finite Euler
product below `q`, exactly as in the production accumulator. -/
noncomputable def lowerSuzukiUnnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) : ℝ :=
  ∑ q ∈ suzukiSupportedBelow S z,
    S.nu q * sourceDiscreteEuler S q * lowerSuzukiDiscreteKernel S D z k q

/-- Successive ceiling divisions by positive divisors equal division by their product. -/
theorem ceilDiv_ceilDiv_eq {D a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (D ⌈/⌉ a) ⌈/⌉ b = D ⌈/⌉ (a * b) := by
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff_le_mul hb).2
    apply (ceilDiv_le_iff_le_mul ha).2
    rw [← mul_assoc]
    exact (ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb)).1 le_rfl
  · apply (ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb)).2
    rw [mul_assoc]
    exact (ceilDiv_le_iff_le_mul ha).1
      ((ceilDiv_le_iff_le_mul hb).1 le_rfl)

private theorem lowerRosserEvenBoundaryLayerMass_succ_pair
    (S : BoundingSieve) (k D z : ℕ) :
    lowerRosserEvenBoundaryLayerMass S (k + 1) D z =
      ∑ p₀ ∈ suzukiSupportedBelow S z,
        S.nu p₀ *
          ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
              (fun p₁ => p₁ ^ 3 < D ⌈/⌉ p₀),
            S.nu p₁ * lowerRosserEvenBoundaryLayerMass S k
              ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁ := by
  unfold lowerRosserEvenBoundaryLayerMass
  rw [show 2 * (k + 1 + 1) = (2 * k + 2) + 2 by omega,
    lowerRosserBoundaryLayerMass]
  simp only [if_neg (show ¬ Odd (2 * k + 2 + 2) from
    Nat.not_odd_iff_even.mpr
      (show Even (2 * k + 2 + 2) from ⟨k + 2, by omega⟩))]
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  congr 1
  rw [show 2 * k + 2 + 1 = (2 * k + 1) + 2 by omega,
    lowerRosserBoundaryLayerMass]
  simp only [if_pos (show Odd (2 * k + 1 + 2) from ⟨k + 1, by omega⟩)]
  rfl

/-- Exact all-depth layer bridge: pair depth `k` is Suzuki source depth
`2*(k+1)`, with no fixed-depth truncation. -/
theorem lowerRosserEvenBoundaryLayerMass_eq_unnormalizedLayer
    (S : BoundingSieve) (D z k : ℕ) (hzD : z ≤ D) :
    lowerRosserEvenBoundaryLayerMass S k D z =
      lowerSuzukiUnnormalizedLayer S D z k := by
  induction k using Nat.strong_induction_on generalizing D z with
  | h k ih =>
      cases k with
      | zero =>
          classical
          unfold lowerRosserEvenBoundaryLayerMass lowerSuzukiUnnormalizedLayer
          simp only [lowerRosserBoundaryLayerMass, if_neg (by norm_num : ¬ Odd 2)]
          simp_rw [Finset.mul_sum]
          have hreindex :
              (∑ p ∈ suzukiSupportedBelow S z,
                ∑ q ∈ (suzukiSupportedBelow S p).filter
                    (fun q => D ⌈/⌉ p ≤ q ^ 3),
                  S.nu p * (S.nu q * sourceDiscreteEuler S q)) =
              ∑ p ∈ suzukiSupportedBelow S z,
                ∑ q ∈ (suzukiSupportedBelow S z).filter
                    (fun q => q < p ∧ D ⌈/⌉ p ≤ q ^ 3),
                  S.nu p * (S.nu q * sourceDiscreteEuler S q) := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr
            · ext q
              simp only [suzukiSupportedBelow, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hqS, hqp⟩, hDq⟩
                exact ⟨⟨hqS, hqp.trans (Finset.mem_filter.mp hp).2⟩, hqp, hDq⟩
              · rintro ⟨⟨hqS, hqz⟩, hqp, hDq⟩
                exact ⟨⟨hqS, hqp⟩, hDq⟩
            · intro q hq
              rfl
          rw [hreindex]
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q hq
          have hqprime : q.Prime :=
            Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
          have hqnot : q ∉ (suzukiSupportedBelow S z).filter (fun p => q < p) := by simp
          have hqmin : ∀ p ∈ (suzukiSupportedBelow S z).filter (fun p => q < p), q ≤ p := by
            intro p hp
            exact (Finset.mem_filter.mp hp).2.le
          rw [lowerSuzukiDiscreteKernel,
            lowerRosserBoundaryChainsFixedPairDepth0Density_zero
              S.nu hqnot hqprime hqmin]
          have hcarrier :
              (suzukiSupportedBelow S z).filter
                  (fun p => q < p ∧ D ⌈/⌉ p ≤ q ^ 3) =
                ((suzukiSupportedBelow S z).filter (fun p => q < p)).filter
                  (fun p => p < D ∧ D ≤ p * q ^ 3) := by
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hpSupport, hqp, hceil⟩
              have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors
                (Finset.mem_filter.mp hpSupport).1).pos
              have hpD : p < D :=
                (Finset.mem_filter.mp hpSupport).2.trans_le hzD
              exact ⟨⟨hpSupport, hqp⟩, hpD,
                (ceilDiv_le_iff_le_mul hp0).1 hceil⟩
            · rintro ⟨⟨hpSupport, hqp⟩, hpD, hmul⟩
              have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors
                (Finset.mem_filter.mp hpSupport).1).pos
              exact ⟨hpSupport, hqp, (ceilDiv_le_iff_le_mul hp0).2 hmul⟩
          rw [← Finset.sum_filter, hcarrier, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
      | succ k =>
          classical
          rw [lowerRosserEvenBoundaryLayerMass_succ_pair]
          have hleft :
              (∑ p₀ ∈ suzukiSupportedBelow S z,
                S.nu p₀ *
                  ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
                      (fun p₁ => p₁ ^ 3 < D ⌈/⌉ p₀),
                    S.nu p₁ * lowerRosserEvenBoundaryLayerMass S k
                      ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁) =
              ∑ p₀ ∈ suzukiSupportedBelow S z,
                S.nu p₀ *
                  ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
                      (fun p₁ => p₁ ^ 3 < D ⌈/⌉ p₀),
                    S.nu p₁ * lowerSuzukiUnnormalizedLayer S
                      (D ⌈/⌉ (p₀ * p₁)) p₁ k := by
            apply Finset.sum_congr rfl
            intro p₀ hp₀
            congr 1
            apply Finset.sum_congr rfl
            intro p₁ hp₁
            have hp₀pos : 0 < p₀ := (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp hp₀).1).pos
            have hp₁prime : p₁.Prime := Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).1
            have hp₁bound : p₁ ≤ (D ⌈/⌉ p₀) ⌈/⌉ p₁ := by
              by_contra hn
              have hceil : (D ⌈/⌉ p₀) ⌈/⌉ p₁ ≤ p₁ :=
                (Nat.lt_of_not_ge hn).le
              have hsmall := (ceilDiv_le_iff_le_mul hp₁prime.pos).1 hceil
              have hlarge := (Finset.mem_filter.mp hp₁).2
              nlinarith [hp₁prime.two_le]
            rw [ih k (Nat.lt_succ_self k) ((D ⌈/⌉ p₀) ⌈/⌉ p₁) p₁ hp₁bound,
              ceilDiv_ceilDiv_eq hp₀pos hp₁prime.pos]
          rw [hleft]
          have hcanonical :
              (∑ p₀ ∈ suzukiSupportedBelow S z,
                S.nu p₀ *
                  ∑ p₁ ∈ (suzukiSupportedBelow S p₀).filter
                      (fun p₁ => p₁ ^ 3 < D ⌈/⌉ p₀),
                    S.nu p₁ * lowerSuzukiUnnormalizedLayer S
                      (D ⌈/⌉ (p₀ * p₁)) p₁ k) =
              ∑ p₀ ∈ suzukiSupportedBelow S z,
                S.nu p₀ *
                  ∑ p₁ ∈ (suzukiSupportedBelow S z).filter
                      (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                    S.nu p₁ *
                      ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₁),
                        S.nu q * sourceDiscreteEuler S q *
                          lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q := by
            apply Finset.sum_congr rfl
            intro p₀ hp₀
            have hp₀z : p₀ < z := (Finset.mem_filter.mp hp₀).2
            have hp₀pos : 0 < p₀ := (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp hp₀).1).pos
            apply congrArg (fun x : ℝ => S.nu p₀ * x)
            apply Finset.sum_congr
            · apply Finset.ext
              intro p₁
              simp only [Finset.mem_filter, suzukiSupportedBelow]
              have hcut : p₁ ^ 3 < D ⌈/⌉ p₀ ↔ p₀ * p₁ ^ 3 < D := by
                rw [← not_le, ceilDiv_le_iff_le_mul hp₀pos]
                omega
              constructor
              · rintro ⟨⟨hp₁S, hp₁p₀⟩, hceil⟩
                exact ⟨⟨hp₁S, hp₁p₀.trans hp₀z⟩, hp₁p₀, hcut.mp hceil⟩
              · rintro ⟨⟨hp₁S, hp₁z⟩, hp₁p₀, hprod⟩
                exact ⟨⟨hp₁S, hp₁p₀⟩, hcut.mpr hprod⟩
            · intro p₁ hp₁
              have hp₁p₀ : p₁ < p₀ := (Finset.mem_filter.mp hp₁).2.1
              have hp₁z : p₁ < z :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).2
              unfold lowerSuzukiUnnormalizedLayer
              apply congrArg (fun x : ℝ => S.nu p₁ * x)
              apply Finset.sum_congr
              · apply Finset.ext
                intro q
                simp only [Finset.mem_filter, suzukiSupportedBelow]
                constructor
                · intro hq
                  rcases hq with ⟨hqS, hqp₁⟩
                  exact ⟨⟨hqS, hqp₁.trans hp₁z⟩, hqp₁⟩
                · intro hq
                  rcases hq with ⟨⟨hqS, hqz⟩, hqp₁⟩
                  exact ⟨hqS, hqp₁⟩
              · intro q hq
                rfl
          rw [hcanonical]
          unfold lowerSuzukiUnnormalizedLayer
          have hswapInner (p₀ : ℕ) :
              (∑ p₁ ∈ (suzukiSupportedBelow S z).filter
                    (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                S.nu p₁ *
                  ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₁),
                    S.nu q * sourceDiscreteEuler S q *
                      lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q) =
              ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₀),
                S.nu q * sourceDiscreteEuler S q *
                  ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter
                      (fun p => q < p)).filter
                      (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                    S.nu p₁ *
                      lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q := by
            calc
              _ = ∑ p₁ ∈ (suzukiSupportedBelow S z).filter
                      (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                    ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₁),
                      S.nu p₁ * (S.nu q * sourceDiscreteEuler S q *
                        lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q) := by
                  simp_rw [Finset.mul_sum]
              _ = ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₀),
                    ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter
                        (fun p => q < p)).filter
                        (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                      S.nu p₁ * (S.nu q * sourceDiscreteEuler S q *
                        lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q) := by
                  apply Finset.sum_comm'
                  intro p₁ q
                  simp only [Finset.mem_filter]
                  constructor
                  · rintro ⟨⟨hp₁z, hp₁p₀, hcut⟩, hqz, hqp₁⟩
                    exact ⟨⟨⟨hp₁z, hqp₁⟩, hp₁p₀, hcut⟩,
                      hqz, hqp₁.trans hp₁p₀⟩
                  · rintro ⟨⟨⟨hp₁z, hqp₁⟩, hp₁p₀, hcut⟩, hqz, hqp₀⟩
                    exact ⟨⟨hp₁z, hp₁p₀, hcut⟩, hqz, hqp₁⟩
              _ = _ := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro p₁ hp₁
                  ring
          simp_rw [hswapInner]
          have hright :
              (∑ q ∈ suzukiSupportedBelow S z,
                S.nu q * sourceDiscreteEuler S q *
                  lowerSuzukiDiscreteKernel S D z (k + 1) q) =
              ∑ q ∈ suzukiSupportedBelow S z,
                S.nu q * sourceDiscreteEuler S q *
                  ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => q < p),
                    ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter
                        (fun p => q < p)).filter
                        (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                      S.nu p₀ * S.nu p₁ *
                        lowerSuzukiDiscreteKernel S (D ⌈/⌉ (p₀ * p₁)) p₁ k q := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [lowerSuzukiDiscreteKernel_succ S hq k]
          rw [hright]
          calc
            _ = ∑ p₀ ∈ suzukiSupportedBelow S z,
                  ∑ q ∈ (suzukiSupportedBelow S z).filter (fun q => q < p₀),
                    S.nu p₀ * (S.nu q * sourceDiscreteEuler S q *
                      ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter
                          (fun p => q < p)).filter
                          (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                        S.nu p₁ * lowerSuzukiDiscreteKernel S
                          (D ⌈/⌉ (p₀ * p₁)) p₁ k q) := by
                simp_rw [Finset.mul_sum]
            _ = ∑ q ∈ suzukiSupportedBelow S z,
                  ∑ p₀ ∈ (suzukiSupportedBelow S z).filter (fun p => q < p),
                    S.nu p₀ * (S.nu q * sourceDiscreteEuler S q *
                      ∑ p₁ ∈ ((suzukiSupportedBelow S z).filter
                          (fun p => q < p)).filter
                          (fun p₁ => p₁ < p₀ ∧ p₀ * p₁ ^ 3 < D),
                        S.nu p₁ * lowerSuzukiDiscreteKernel S
                          (D ⌈/⌉ (p₀ * p₁)) p₁ k q) := by
                apply Finset.sum_comm'
                intro p₀ q
                simp only [Finset.mem_filter]
                tauto
            _ = _ := by
                apply Finset.sum_congr rfl
                intro q hq
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p₀ hp₀
                simp_rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p₁ hp₁
                ring

end MathlibNt.SieveTheory
