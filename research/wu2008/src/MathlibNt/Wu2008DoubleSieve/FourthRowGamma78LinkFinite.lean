import MathlibNt.Wu2008DoubleSieve.FourthRowGamma6LinkFinite
import MathlibNt.Wu2008DoubleSieve.Gamma78GainFinite

/-! # Exact finite Γ7/Γ8 selected-prime prefix transport

The Boolean is true for [0,0] and false for [0,1].  No source-box or
real-cutoff bound is assumed. Only actual nonzero fibres are truncated.
-/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

noncomputable def fourthRowGamma78LinkWord (tri : Bool) : List ℕ :=
  if tri then [0, 0] else [0, 1]

/-- Literal two-prime source carrier: the cutoff is p, not the first window. -/
theorem fourthRowGamma78Link_carrier (N d p q : ℕ) :
    fourthRowMotherPrefixCarrier N d [p, q] =
      sourceSieveCarrier N (d * p * q) (d * N) (p : ℝ) := by
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

theorem fourthRowGamma78Link_colours (b c : ℝ) (p : ℕ) :
    (fourthRowMotherColour b c p = 0 ↔ (p : ℝ) < b) ∧
    (fourthRowMotherColour b c p = 1 ↔ b ≤ (p : ℝ) ∧ (p : ℝ) < c) := by
  unfold fourthRowMotherColour
  split_ifs <;> simp_all

/-- A selected prime in colour zero forces the real base to exceed one. -/
theorem fourthRowGamma78Link_base_gt_one (N d p : ℕ) (δ : ℝ)
    (hp : p.Prime)
    (hpb : (p : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB) :
    1 < (N : ℝ) ^ (1 / 2 - δ) / d := by
  by_contra h
  have hpow := Real.rpow_le_one (show 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / d by positivity)
    (le_of_not_gt h) (show 0 ≤ gamma6BaseB by norm_num [gamma6BaseB])
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

noncomputable def fourthRowGamma78LinkPairs (tri : Bool) (N d : ℕ) (δ : ℝ) :
    Finset (ℕ × ℕ) :=
  (fourthRowGamma5LinkPairs N d δ).filter (fun pq =>
    (pq.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ∧
    (if tri then True else ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ≤ (pq.2 : ℝ)) ∧
    (pq.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma78GainUpper tri)

/-- Exact colour recognition on ordered prime pairs, including half-open endpoints. -/
theorem fourthRowGamma78Link_pairs (tri : Bool) (N d : ℕ) (δ : ℝ) :
    (((primeWindow N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (5 / 2))) ×ˢ
      (primeWindow N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (5 / 2)))).filter (fun pq => pq.1 < pq.2)).filter
      (fun pq => [pq.1, pq.2].map (fourthRowMotherColour
        (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))) =
          fourthRowGamma78LinkWord tri) = fourthRowGamma78LinkPairs tri N d δ := by
  ext ⟨p, q⟩
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hbc (hR : 1 < R) : R ^ gamma6BaseB ≤ R ^ gamma5ClassicalB :=
    Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [gamma6BaseB, gamma5ClassicalB])
  have hcf (hR : 1 < R) : R ^ gamma5ClassicalB ≤ R ^ gamma6BaseF :=
    Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [gamma5ClassicalB, gamma6BaseF])
  simp only [mem_filter, mem_product, mem_primeWindow, fourthRowGamma78LinkPairs,
    fourthRowGamma5Link_pairs_iff, (fourthRowGamma6Link_cutoffs N d δ).1,
    (fourthRowGamma6Link_cutoffs N d δ).2.2, fourthRowGamma5Link_cutoff,
    List.map_cons, List.map_nil]
  cases tri <;> simp only [fourthRowGamma78LinkWord, gamma78GainUpper,
    Bool.false_eq_true, if_false, if_true, List.cons.injEq, and_true, true_and,
    (fourthRowGamma78Link_colours _ _ p).1,
    (fourthRowGamma78Link_colours _ _ q).1,
    (fourthRowGamma78Link_colours _ _ q).2, gamma5ClassicalS]
  · constructor
    · rintro ⟨⟨⟨⟨hp, hpN, hpa, _⟩, ⟨hq, hqN, _, _⟩⟩, hpq⟩, hpb, hbq, hqc⟩
      exact ⟨⟨hp, hq, hpN, hqN, hpa, hpq, hqc⟩, hpb, hbq, hqc⟩
    · rintro ⟨⟨hp, hq, hpN, hqN, hpa, hpq, hqc⟩, hpb, hbq, _⟩
      have hR := fourthRowGamma78Link_base_gt_one N d p δ hp hpb
      have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
      exact ⟨⟨⟨⟨hp, hpN, hpa, (hpq'.trans hqc).trans_le (hcf hR)⟩,
        ⟨hq, hqN, hpa.trans hpq'.le, hqc.trans_le (hcf hR)⟩⟩, hpq⟩, hpb, hbq, hqc⟩
  · constructor
    · rintro ⟨⟨⟨⟨hp, hpN, hpa, _⟩, ⟨hq, hqN, _, _⟩⟩, hpq⟩, hpb, hqb⟩
      have hR := fourthRowGamma78Link_base_gt_one N d p δ hp hpb
      exact ⟨⟨hp, hq, hpN, hqN, hpa, hpq, hqb.trans_le (hbc hR)⟩, hpb, hqb⟩
    · rintro ⟨⟨hp, hq, hpN, hqN, hpa, hpq, _⟩, hpb, hqb⟩
      have hR := fourthRowGamma78Link_base_gt_one N d p δ hp hpb
      have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
      exact ⟨⟨⟨⟨hp, hpN, hpa, hpb.trans_le ((hbc hR).trans (hcf hR))⟩,
        ⟨hq, hqN, hpa.trans hpq'.le, hqb.trans_le ((hbc hR).trans (hcf hR))⟩⟩,
        hpq⟩, hpb, hqb⟩

/-- The list image is injective: no pair label or tuple multiplicity is lost. -/
theorem fourthRowGamma78Link_prefix_sum (tri : Bool) (N d : ℕ) (δ : ℝ) :
    fourthRowMotherPrefixTerm N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2)) (fourthRowGamma78LinkWord tri) =
    ∑ pq ∈ fourthRowGamma78LinkPairs tri N d δ,
      (sourceSieveCount N (d * pq.1 * pq.2) (d * N) (pq.1 : ℝ) : ℝ) := by
  have hlen : (fourthRowGamma78LinkWord tri).length = 2 := by cases tri <;> rfl
  unfold fourthRowMotherPrefixTerm
  rw [hlen]
  simp only [fourthRowMotherTuples]
  rw [sum_image]
  · rw [← fourthRowGamma78Link_pairs tri N d δ]
    simp only [sum_filter, fourthRowGamma78Link_carrier, sourceSieveCount, Int.cast_natCast]
  · intro x _ y _ h
    simpa only [List.cons.injEq, and_true, Prod.ext_iff] using h

/-- Truncation is an equality because omitted actual source fibres are zero. -/
theorem fourthRowGamma78Link_bounded_sum {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (tri : Bool) (d : ℕ) (δ : ℝ) :
    (∑ pq ∈ fourthRowGamma78LinkPairs tri N d δ,
      (sourceSieveCount N (d * pq.1 * pq.2) (d * N) (pq.1 : ℝ) : ℝ)) =
    ∑ pq ∈ (fourthRowGamma78LinkPairs tri N d δ).filter
      (fun pq => pq.1 ≤ N ∧ pq.2 ≤ N),
      (sourceSieveCount N (d * pq.1 * pq.2) (d * N) (pq.1 : ℝ) : ℝ) := by
  symm
  apply sum_subset (filter_subset _ _)
  intro pq hpq hn
  have hz : sourceSieveCount N (d * pq.1 * pq.2) (d * N) (pq.1 : ℝ) = 0 := by
    by_contra hz
    have hp := fourthRowGamma5Link_factor_bound hN he
      ((dvd_mul_left pq.1 d).trans (dvd_mul_right (d * pq.1) pq.2)) hz
    have hq := fourthRowGamma5Link_factor_bound hN he
      (dvd_mul_left pq.2 (d * pq.1)) hz
    exact hn (mem_filter.mpr ⟨hpq, hp, hq⟩)
  simp [hz]

/-- The original mother equals the accepted selected-prime count, on the wide domain. -/
theorem fourthRowGamma78Link_count_eq {i N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (tri : Bool) (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowMotherPrefixSum N δ W (fourthRowGamma78LinkWord tri) =
      gamma78GainCount N W (gamma78GainLabels tri N δ W) := by
  have hlabels : gamma78GainLabels tri N δ W =
      (boxConvolutionSupport W).biUnion (fun d =>
        ((fourthRowGamma78LinkPairs tri N d δ).filter
          (fun pq => pq.1 ≤ N ∧ pq.2 ≤ N)).image (fun pq => (d, pq))) := by
    ext ⟨d, p, q⟩
    simp only [gamma78GainLabels, gamma5ClassicalLabels, fourthRowGamma78LinkPairs,
      mem_filter, mem_product, mem_range, Nat.lt_succ_iff,
      mem_biUnion, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hd, hpN, hqN⟩, hh⟩, hx⟩
      exact ⟨d, hd, (p, q), ⟨⟨(fourthRowGamma5Link_pairs_iff N d p q δ).mpr hh, hx⟩,
        hpN, hqN⟩, rfl, rfl⟩
    · rintro ⟨e, he, ⟨r, s⟩, ⟨⟨hh, hx⟩, hrN, hsN⟩, hed, hpair⟩
      cases hed
      cases hpair
      exact ⟨⟨⟨he, hrN, hsN⟩, (fourthRowGamma5Link_pairs_iff N d p q δ).mp hh⟩, hx⟩
  unfold fourthRowMotherPrefixSum gamma78GainCount
  rw [hlabels, sum_biUnion]
  · apply sum_congr rfl
    intro d _
    rw [fourthRowGamma78Link_prefix_sum, fourthRowGamma78Link_bounded_sum hN he,
      sum_image]
    · simp only [mul_sum, gamma5ClassicalProduct]
    · intro x _ y _ h
      exact (Prod.mk.inj h).2
  · intro d _ e _ hde
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨p, _, hp⟩ := mem_image.mp hx
    obtain ⟨q, _, hq⟩ := mem_image.mp hy
    exact hde (by simpa using congrArg Prod.fst (hp.trans hq.symm))

/-- Γ7 is the literal [0,0] mother addend. -/
theorem fourthRowGamma78Link_gamma7_eq {i N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowMotherPrefixSum N δ W [0, 0] =
      gamma78GainCount N W (gamma78GainLabels true N δ W) :=
  fourthRowGamma78Link_count_eq hN he true δ W

/-- Γ8 is the literal [0,1] mother addend. -/
theorem fourthRowGamma78Link_gamma8_eq {i N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowMotherPrefixSum N δ W [0, 1] =
      gamma78GainCount N W (gamma78GainLabels false N δ W) :=
  fourthRowGamma78Link_count_eq hN he false δ W

end Wu2008DoubleSieve
