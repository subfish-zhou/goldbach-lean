import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryActualCorrelation
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimePrefix

/-!
# Removing the actual outer coefficients before the IV.3 Gram expansion

The first modulus coefficient, gamma and first beta depend only on the
shared outer triple. Their exact L2 cost is outside the correlation sum.
The remaining signed coefficient depends only on `(n₂,s')`, not on `k₁`.
The small-root phase and all carrier restrictions are still retained.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wCorrelationOuterWeight (K : WExtractedKey) (β c₁ γ : ℕ → ℝ)
    (o : ℕ × ℕ × ℕ) : ℝ :=
  γ (K.2 * o.2.1) * c₁ (K.1.2.2.1 * K.1.2.2.2.1 * o.1) *
    β (K.1.1 * K.1.2.1 * o.2.2)

def wCorrelationInnerWeight (K : WExtractedKey) (β ζ : ℕ → ℝ)
    (t : WExtractedTuple × ℤ) : ℝ :=
  ζ ((K.1.2.2.1 * K.1.2.2.2.2 / K.2) * t.1.1.2.2) *
    β (K.1.1 * (wGCDTuple (wExtractedOriginal t.1)).n₂)

/-- Equality of the two inner arithmetic coordinates suffices. Neither
the first modulus nor its coefficient is concealed in this weight. -/
theorem wCorrelationInnerWeight_eq (K : WExtractedKey) (β ζ : ℕ → ℝ)
    {t u : WExtractedTuple × ℤ}
    (hn : (wGCDTuple (wExtractedOriginal t.1)).n₂ =
      (wGCDTuple (wExtractedOriginal u.1)).n₂)
    (hs : t.1.1.2.2 = u.1.1.2.2) :
    wCorrelationInnerWeight K β ζ t = wCorrelationInnerWeight K β ζ u := by
  simp only [wCorrelationInnerWeight, hn, hs]

theorem wExtractedCoefficient_eq_outer_inner
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K)
    (β c₁ γ ζ : ℕ → ℝ) :
    wExtractedCoefficient β c₁ γ ζ t.1 =
      wCorrelationOuterWeight K β c₁ γ (wCorrelationOuter t) *
        wCorrelationInnerWeight K β ζ t := by
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hk := (wExtractedKeyFiber_spec ht).1
  have hd := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.1) hk
  have hd₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) hk
  have hδ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.1) hk
  have hδ₁ := congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.2.2.1) hk
  have hq := hv.q_eq
  have hn₁ := hv.N₁_eq
  have hn₂ := hv.N₂_eq
  change t.1.2.1 = _ at hq
  change t.1.2.2.1 = _ at hn₁
  change t.1.2.2.2 = _ at hn₂
  change (wGCDTuple (wExtractedOriginal t.1)).d = K.1.1 at hd
  change (wGCDTuple (wExtractedOriginal t.1)).d₁ = K.1.2.1 at hd₁
  change (wGCDTuple (wExtractedOriginal t.1)).δ = K.1.2.2.1 at hδ
  change (wGCDTuple (wExtractedOriginal t.1)).δ₁ = K.1.2.2.2.1 at hδ₁
  rw [hd, hd₁] at hn₁
  rw [hd] at hn₂
  rw [hδ, hδ₁] at hq
  dsimp only [wExtractedCoefficient, wCorrelationOuterWeight,
    wCorrelationInnerWeight, wCorrelationOuter]
  rw [(wExtractedKeyFiber_spec ht).2.1, (wExtractedKeyFiber_spec ht).2.2.2.2,
    hq, hn₁, hn₂]
  ring

def wSeparatedCorrelationEnergy (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (U : Finset (WExtractedTuple × ℤ)) (c : Finset (ℕ × ℕ))
    (K : WExtractedKey) (β ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ o ∈ (wCoprimeFiber x N S U c).image wCorrelationOuter,
    (∑ t ∈ wCorrelationOuterFiber x N S U c o,
      ∑ u ∈ wCorrelationOuterFiber x N S U c o,
        ((wCorrelationInnerWeight K β ζ t : ℂ) *
          star (wCorrelationInnerWeight K β ζ u : ℂ)) *
          (wActualSmallRootFactor a t * star (wActualSmallRootFactor a u)) *
          wActualReciprocalCorrelation K a t u).re

def wCorrelationOuterMass (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (U : Finset (WExtractedTuple × ℤ)) (c : Finset (ℕ × ℕ))
    (K : WExtractedKey) (β c₁ γ : ℕ → ℝ) : ℝ :=
  ∑ o ∈ (wCoprimeFiber x N S U c).image wCorrelationOuter,
    wCorrelationOuterWeight K β c₁ γ o ^ 2

theorem wSeparatedCorrelationEnergy_nonneg
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) :
    0 ≤ wSeparatedCorrelationEnergy x N S U c K β ζ a := by
  apply sum_nonneg
  intro o _
  have he := congrArg Complex.re (wCorrelationOuterFiber_gram hN hQ hU c o
    (fun t => (wCorrelationInnerWeight K β ζ t : ℂ)))
  rw [← he]
  exact sq_nonneg _

theorem wCoprimeFiber_separated_cauchy
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    (c : Finset (ℕ × ℕ)) (β c₁ γ ζ : ℕ → ℝ) :
    ‖∑ t ∈ wCoprimeFiber x N S U c,
      (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
        wExtractedArithmeticPhase a t.2 t.1‖ ^ 2 ≤
      wCorrelationOuterMass x N S U c K β c₁ γ *
        wSeparatedCorrelationEnergy x N S U c K β ζ a := by
  let O := (wCoprimeFiber x N S U c).image wCorrelationOuter
  let B : ℕ × ℕ × ℕ → ℂ := fun o =>
    ∑ t ∈ wCorrelationOuterFiber x N S U c o,
      (wCorrelationInnerWeight K β ζ t : ℂ) * wExtractedArithmeticPhase a t.2 t.1
  have he : (∑ t ∈ wCoprimeFiber x N S U c,
      (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) * wExtractedArithmeticPhase a t.2 t.1) =
      ∑ o ∈ O, (wCorrelationOuterWeight K β c₁ γ o : ℂ) * B o := by
    rw [sum_wCorrelationOuterFibers]
    apply sum_congr rfl
    intro o _
    dsimp only [B]
    rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    obtain ⟨ht, ho⟩ := mem_filter.mp ht
    rw [wExtractedCoefficient_eq_outer_inner hN hQ (hU (mem_filter.mp ht).1),
      Complex.ofReal_mul, ho, mul_assoc]
  rw [he]
  calc
    _ ≤ (∑ o ∈ O, |wCorrelationOuterWeight K β c₁ γ o| * ‖B o‖) ^ 2 := by
      gcongr
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sum_le O (fun o => (wCorrelationOuterWeight K β c₁ γ o : ℂ) * B o)
    _ ≤ (∑ o ∈ O, |wCorrelationOuterWeight K β c₁ γ o| ^ 2) *
        ∑ o ∈ O, ‖B o‖ ^ 2 :=
      sum_mul_sq_le_sq_mul_sq O _ _
    _ = _ := by
      simp only [sq_abs]
      congr 1
      apply sum_congr rfl
      intro o _
      exact congrArg Complex.re (wCorrelationOuterFiber_gram hN hQ hU c o
        (fun t => (wCorrelationInnerWeight K β ζ t : ℂ)))

/-- The selected prefix of a cell is a real original tuple carrier, not
an arbitrary family of weights inserted into an interval theorem. -/
theorem wCoprimePrefixMax_sq_le_separated_correlation
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
    {U : Finset (WExtractedTuple × ℤ)}
    (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
      R S (highOmegaCutoff x) b K)
    (c : Finset (ℕ × ℕ)) (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) :
    ∃ cap ∈ _root_.LiLiuPrereqFouvry.Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j),
      wAnalyticBlockPrefixMax (wCoprimeFiber x N S U c) j β c₁ γ ζ a ^ 2 ≤
        wCorrelationOuterMass x N S (wAnalyticPrefix U cap) c K β c₁ γ *
          wSeparatedCorrelationEnergy x N S (wAnalyticPrefix U cap) c K β ζ a := by
  obtain ⟨cap, hcap, he⟩ :=
    wAnalyticBlockPrefixMax_attained (wCoprimeFiber x N S U c) j β c₁ γ ζ a
  refine ⟨cap, hcap, ?_⟩
  rw [he]
  have hc : wAnalyticPrefix (wCoprimeFiber x N S U c) cap =
      wCoprimeFiber x N S (wAnalyticPrefix U cap) c := by
    ext t
    simp only [wAnalyticPrefix, wCoprimeFiber, mem_filter]
    tauto
  unfold wAnalyticPrefixSum
  rw [hc]
  exact wCoprimeFiber_separated_cauchy hN hQ
    (fun _ ht => hU (mem_filter.mp ht).1) c β c₁ γ ζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
