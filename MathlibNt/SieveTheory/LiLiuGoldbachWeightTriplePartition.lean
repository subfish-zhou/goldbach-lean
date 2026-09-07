import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruple

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachWeightTriplePartition (P : Prop) :
    Decidable P :=
  Classical.propDecidable P

/-- The part of `S6Closed` with middle prime `s ≤ b`, keeping the original
`t,r,s` nesting and all closed-endpoint/repeat contributions. -/
noncomputable def goldbachWeightLowMiddle
    (A : Finset ℕ) (N : ℕ) (z b y : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z y,
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
          (fun s : ℕ => (s : ℝ) ≤ b),
        literalH A (N * r) (r * s * t) s

/-- The complementary part of `S6Closed` with `b < s`. -/
noncomputable def goldbachWeightUpperMiddle
    (A : Finset ℕ) (N : ℕ) (z b y : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z y,
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
          (fun s : ℕ => b < (s : ℝ)),
        literalH A (N * r) (r * s * t) s

theorem goldbachWeightLowMiddle_nonneg
    (A : Finset ℕ) (N : ℕ) (z b y : ℝ) :
    0 ≤ goldbachWeightLowMiddle A N z b y := by
  unfold goldbachWeightLowMiddle
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro s hs
  exact literalH_nonneg A (N * r) (r * s * t) s

theorem goldbachWeightUpperMiddle_nonneg
    (A : Finset ℕ) (N : ℕ) (z b y : ℝ) :
    0 ≤ goldbachWeightUpperMiddle A N z b y := by
  unfold goldbachWeightUpperMiddle
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro s hs
  exact literalH_nonneg A (N * r) (r * s * t) s

private theorem goldbachWeightTriplePartition_closedPrimes_eq_filter_ge
    (N : ℕ) (z y : ℝ) {r : ℕ}
    (hr : r ∈ goldbachClosedPrimes N z y) :
    goldbachClosedPrimes N (r : ℝ) y =
      (goldbachClosedPrimes N z y).filter (fun s : ℕ => r ≤ s) := by
  ext s
  constructor
  · intro hs
    rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨_, _, hrz, _⟩
    rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, hsN, hrs, hsy⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨mem_goldbachClosedPrimes_iff.mpr ?_, ?_⟩
    · exact ⟨hsPrime, hsN, hrz.trans hrs, hsy⟩
    · exact_mod_cast hrs
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hrs⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨hsPrime, hsN, _, hsy⟩
    exact mem_goldbachClosedPrimes_iff.mpr
      ⟨hsPrime, hsN, by exact_mod_cast hrs, hsy⟩

private theorem goldbachWeightTriplePartition_closedPrimes_filter_le_eq_lower
    (N : ℕ) (z y : ℝ) {s : ℕ}
    (hs : s ∈ goldbachClosedPrimes N z y) :
    (goldbachClosedPrimes N z y).filter (fun r : ℕ => r ≤ s) =
      goldbachClosedPrimes N z (s : ℝ) := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_filter.mp hr with ⟨hrClosed, hrs⟩
    rcases mem_goldbachClosedPrimes_iff.mp hrClosed with ⟨hrPrime, hrN, hrz, _⟩
    exact mem_goldbachClosedPrimes_iff.mpr
      ⟨hrPrime, hrN, hrz, by exact_mod_cast hrs⟩
  · intro hr
    rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, hsN, hsz, hsy⟩
    rcases mem_goldbachClosedPrimes_iff.mp hr with ⟨hrPrime, hrN, hrz, hrs⟩
    refine Finset.mem_filter.mpr ?_
    refine ⟨mem_goldbachClosedPrimes_iff.mpr ?_, ?_⟩
    · exact ⟨hrPrime, hrN, hrz, hrs.trans hsy⟩
    · exact_mod_cast hrs

private theorem goldbachWeightTriplePartition_triangle_swap
    (N : ℕ) (z y : ℝ) (F : ℕ → ℕ → ℤ) :
    (∑ s ∈ goldbachClosedPrimes N z y,
        ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), F r s) =
      ∑ r ∈ goldbachClosedPrimes N z y,
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) y, F r s := by
  let T := goldbachClosedPrimes N z y
  calc
    ∑ s ∈ goldbachClosedPrimes N z y,
        ∑ r ∈ goldbachClosedPrimes N z (s : ℝ), F r s =
      ∑ s ∈ T,
        ∑ r ∈ T.filter (fun r : ℕ => r ≤ s), F r s := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [goldbachWeightTriplePartition_closedPrimes_filter_le_eq_lower N z y hs]
    _ = ∑ s ∈ T, ∑ r ∈ T, if r ≤ s then F r s else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_filter]
    _ = ∑ r ∈ T, ∑ s ∈ T, if r ≤ s then F r s else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ r ∈ T,
          ∑ s ∈ T.filter (fun s : ℕ => r ≤ s), F r s := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_filter]
    _ = ∑ r ∈ goldbachClosedPrimes N z y,
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) y, F r s := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [goldbachWeightTriplePartition_closedPrimes_eq_filter_ge N z y hr]

private theorem goldbachWeightTriplePartition_closedPrimes_filter_lt_eq_halfOpen_of_le
    (N : ℕ) (z b y : ℝ) (hby : b ≤ y) :
    (goldbachClosedPrimes N z y).filter (fun p : ℕ => (p : ℝ) < b) =
      goldbachHalfOpenPrimes N z b := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpb⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, hpz, _⟩
    exact mem_goldbachHalfOpenPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpb⟩
  · intro hp
    rcases mem_goldbachHalfOpenPrimes_iff.mp hp with ⟨hpPrime, hpN, hpz, hpb⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpb.le.trans hby⟩, hpb⟩

private theorem goldbachWeightTriplePartition_closedPrimes_filter_not_lt_eq_closed
    (N : ℕ) (z b y : ℝ) (hzb : z ≤ b) :
    (goldbachClosedPrimes N z y).filter (fun p : ℕ => ¬(p : ℝ) < b) =
      goldbachClosedPrimes N b y := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpNotLt⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, _, hpy⟩
    exact mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, not_lt.mp hpNotLt, hpy⟩
  · intro hp
    rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hpPrime, hpN, hpb, hpy⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hzb.trans hpb, hpy⟩, not_lt.mpr hpb⟩

private theorem goldbachWeightTriplePartition_closedPrimes_filter_le_eq_self
    (N : ℕ) (r y b : ℝ) (hyb : y ≤ b) :
    (goldbachClosedPrimes N r y).filter (fun s : ℕ => (s : ℝ) ≤ b) =
      goldbachClosedPrimes N r y := by
  ext s
  constructor
  · intro hs
    exact (Finset.mem_filter.mp hs).1
  · intro hs
    rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨_, _, _, hsy⟩
    exact Finset.mem_filter.mpr ⟨hs, hsy.trans hyb⟩

private theorem goldbachWeightTriplePartition_closedPrimes_filter_le_eq_closed
    (N : ℕ) (r b y : ℝ) (hby : b ≤ y) :
    (goldbachClosedPrimes N r y).filter (fun s : ℕ => (s : ℝ) ≤ b) =
      goldbachClosedPrimes N r b := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hsb⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨hsPrime, hsN, hrs, _⟩
    exact mem_goldbachClosedPrimes_iff.mpr ⟨hsPrime, hsN, hrs, hsb⟩
  · intro hs
    rcases mem_goldbachClosedPrimes_iff.mp hs with ⟨hsPrime, hsN, hrs, hsb⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hsPrime, hsN, hrs, hsb.trans hby⟩, hsb⟩

private theorem goldbachWeightTriplePartition_closedPrimes_filter_le_empty_of_lt_lower
    (N : ℕ) {r : ℕ} {b y : ℝ}
    (hbr : b < (r : ℝ)) :
    (goldbachClosedPrimes N (r : ℝ) y).filter (fun s : ℕ => (s : ℝ) ≤ b) = ∅ := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hsb⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨_, _, hrs, _⟩
    have hbs : b < (s : ℝ) := lt_of_lt_of_le hbr hrs
    exact (not_lt_of_ge hsb hbs).elim
  · intro hs
    cases hs

private theorem goldbachWeightTriplePartition_low_slice_eq_s6_slice_of_lt
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) {t : ℕ}
    (ht : t ∈ goldbachHalfOpenPrimes N z b) :
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => (s : ℝ) ≤ b),
          literalH A (N * r) (r * s * t) s) =
      ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
          literalH A (N * r) (r * s * t) s := by
  rcases mem_goldbachHalfOpenPrimes_iff.mp ht with ⟨_, _, _, htb⟩
  apply Finset.sum_congr rfl
  intro r hr
  rw [goldbachWeightTriplePartition_closedPrimes_filter_le_eq_self N (r : ℝ) (t : ℝ) b htb.le]

theorem goldbachWeightT14_eq_goldbachS6Closed
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) :
    goldbachWeightT14 A N z b = goldbachS6Closed A N z b := by
  unfold goldbachWeightT14 goldbachS6Closed
  apply Finset.sum_congr rfl
  intro t ht
  simpa using
    (goldbachWeightTriplePartition_triangle_swap N z (t : ℝ)
      (fun r s : ℕ => literalH A (N * r) (r * s * t) s))

private theorem goldbachWeightTriplePartition_low_slice_eq_t15_slice
    (A : Finset ℕ) (N : ℕ) (z b : ℝ) {t : ℕ}
    (ht : t ∈ goldbachClosedPrimes N b (t : ℝ)) :
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => (s : ℝ) ≤ b),
          literalH A (N * r) (r * s * t) s) =
      ∑ s ∈ goldbachClosedPrimes N z b,
        ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
          literalH A (N * r) (r * s * t) s := by
  let T := goldbachClosedPrimes N z (t : ℝ)
  let slice : ℕ → ℤ := fun r =>
    ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
        (fun s : ℕ => (s : ℝ) ≤ b),
      literalH A (N * r) (r * s * t) s
  rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨_, _, hbt, _⟩
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      T
      (fun r : ℕ => (r : ℝ) ≤ b)
      slice
  have hzero :
      ∑ r ∈ T.filter (fun r : ℕ => ¬(r : ℝ) ≤ b), slice r = 0 := by
    refine Finset.sum_eq_zero ?_
    intro r hr
    rcases Finset.mem_filter.mp hr with ⟨_, hrNotLe⟩
    have hrb : b < (r : ℝ) := lt_of_not_ge hrNotLe
    rw [show slice r =
      ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
          (fun s : ℕ => (s : ℝ) ≤ b),
        literalH A (N * r) (r * s * t) s by rfl]
    rw [goldbachWeightTriplePartition_closedPrimes_filter_le_empty_of_lt_lower N hrb, Finset.sum_empty]
  have hkeep :
      ∑ r ∈ T, slice r =
        ∑ r ∈ T.filter (fun r : ℕ => (r : ℝ) ≤ b), slice r := by
    have hsplit' :
        ∑ r ∈ T, slice r =
          ∑ r ∈ T.filter (fun r : ℕ => (r : ℝ) ≤ b), slice r +
            ∑ r ∈ T.filter (fun r : ℕ => ¬(r : ℝ) ≤ b), slice r := by
      simpa [slice] using hsplit.symm
    omega
  calc
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => (s : ℝ) ≤ b),
          literalH A (N * r) (r * s * t) s) =
      ∑ r ∈ T, slice r := by
        rfl
    _ = ∑ r ∈ T.filter (fun r : ℕ => (r : ℝ) ≤ b), slice r := by
          exact hkeep
    _ = ∑ r ∈ goldbachClosedPrimes N z b, slice r := by
          rw [goldbachWeightTriplePartition_closedPrimes_filter_le_eq_closed N z b (t : ℝ) hbt]
    _ = ∑ r ∈ goldbachClosedPrimes N z b,
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) b,
            literalH A (N * r) (r * s * t) s := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [show slice r =
              ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
                  (fun s : ℕ => (s : ℝ) ≤ b),
                literalH A (N * r) (r * s * t) s by rfl]
            rw [goldbachWeightTriplePartition_closedPrimes_filter_le_eq_closed
              N (r : ℝ) b (t : ℝ) hbt]
    _ = ∑ s ∈ goldbachClosedPrimes N z b,
          ∑ r ∈ goldbachClosedPrimes N z (s : ℝ),
            literalH A (N * r) (r * s * t) s := by
            simpa using
              (goldbachWeightTriplePartition_triangle_swap N z b
                (fun r s : ℕ => literalH A (N * r) (r * s * t) s)).symm

private theorem goldbachWeightTriplePartition_lowMiddle_eq_goldbachS6HalfOpen_add_goldbachWeightT15
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ)
    (hzb : z ≤ b) (hbc : b ≤ c) :
    goldbachWeightLowMiddle A N z b c =
      goldbachS6HalfOpen A N z b + goldbachWeightT15 A N z b c := by
  let lowSlice : ℕ → ℤ := fun t =>
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
          (fun s : ℕ => (s : ℝ) ≤ b),
        literalH A (N * r) (r * s * t) s
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z c)
      (fun t : ℕ => (t : ℝ) < b)
      lowSlice
  have hdecomp :
      ∑ t ∈ goldbachClosedPrimes N z c, lowSlice t =
        ∑ t ∈ goldbachHalfOpenPrimes N z b, lowSlice t +
          ∑ t ∈ goldbachClosedPrimes N b c, lowSlice t := by
    calc
      ∑ t ∈ goldbachClosedPrimes N z c, lowSlice t =
        ∑ t ∈ goldbachHalfOpenPrimes N z b, lowSlice t +
          ∑ t ∈ (goldbachClosedPrimes N z c).filter (fun t : ℕ => ¬(t : ℝ) < b), lowSlice t := by
            simpa [goldbachWeightTriplePartition_closedPrimes_filter_lt_eq_halfOpen_of_le N z b c hbc]
              using hsplit.symm
      _ = ∑ t ∈ goldbachHalfOpenPrimes N z b, lowSlice t +
            ∑ t ∈ goldbachClosedPrimes N b c, lowSlice t := by
              rw [goldbachWeightTriplePartition_closedPrimes_filter_not_lt_eq_closed N z b c hzb]
  have hfirst :
      ∑ t ∈ goldbachHalfOpenPrimes N z b, lowSlice t =
        goldbachS6HalfOpen A N z b := by
    unfold goldbachS6HalfOpen
    apply Finset.sum_congr rfl
    intro t ht
    simpa [lowSlice] using
      goldbachWeightTriplePartition_low_slice_eq_s6_slice_of_lt A N z b ht
  have hsecond :
      ∑ t ∈ goldbachClosedPrimes N b c, lowSlice t =
        goldbachWeightT15 A N z b c := by
    unfold goldbachWeightT15
    apply Finset.sum_congr rfl
    intro t ht
    have htSelf : t ∈ goldbachClosedPrimes N b (t : ℝ) := by
      rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, htN, hbt, _⟩
      exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htN, hbt, le_rfl⟩
    simpa [lowSlice] using
      goldbachWeightTriplePartition_low_slice_eq_t15_slice A N z b htSelf
  unfold goldbachWeightLowMiddle
  change ∑ t ∈ goldbachClosedPrimes N z c, lowSlice t =
    goldbachS6HalfOpen A N z b + goldbachWeightT15 A N z b c
  rw [hdecomp, hfirst, hsecond]

theorem goldbachWeightLowMiddle_add_goldbachWeightUpperMiddle_eq_goldbachS6Closed
    (A : Finset ℕ) (N : ℕ) (z b y : ℝ) :
    goldbachWeightLowMiddle A N z b y +
        goldbachWeightUpperMiddle A N z b y =
      goldbachS6Closed A N z y := by
  symm
  unfold goldbachWeightLowMiddle goldbachWeightUpperMiddle goldbachS6Closed
  calc
    ∑ t ∈ goldbachClosedPrimes N z y,
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
            literalH A (N * r) (r * s * t) s =
      ∑ t ∈ goldbachClosedPrimes N z y,
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ((∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => (s : ℝ) ≤ b),
              literalH A (N * r) (r * s * t) s) +
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => ¬(s : ℝ) ≤ b),
              literalH A (N * r) (r * s * t) s) := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro r hr
            exact (Finset.sum_filter_add_sum_filter_not
              (goldbachClosedPrimes N (r : ℝ) (t : ℝ))
              (fun s : ℕ => (s : ℝ) ≤ b)
              (fun s => literalH A (N * r) (r * s * t) s)).symm
    _ =
      (∑ t ∈ goldbachClosedPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => (s : ℝ) ≤ b),
              literalH A (N * r) (r * s * t) s) +
        ∑ t ∈ goldbachClosedPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => ¬(s : ℝ) ≤ b),
              literalH A (N * r) (r * s * t) s := by
          simp_rw [Finset.sum_add_distrib]
    _ =
      (∑ t ∈ goldbachClosedPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => (s : ℝ) ≤ b),
              literalH A (N * r) (r * s * t) s) +
        ∑ t ∈ goldbachClosedPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => b < (s : ℝ)),
              literalH A (N * r) (r * s * t) s := by
          congr 1
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro r hr
          congr 1
          ext s
          simp [not_le]
    _ = goldbachWeightLowMiddle A N z b y + goldbachWeightUpperMiddle A N z b y := by
          rfl

theorem goldbachWeightT14_add_goldbachWeightT15_eq_goldbachWeightLowMiddle_add_goldbachB6
    (A : Finset ℕ) (N : ℕ) (z b c : ℝ)
    (_hz : 2 ≤ z) (hzb : z ≤ b) (hbc : b ≤ c) :
    goldbachWeightT14 A N z b + goldbachWeightT15 A N z b c =
      goldbachWeightLowMiddle A N z b c + goldbachB6 A N z b := by
  have hT14 :
      goldbachWeightT14 A N z b = goldbachS6Closed A N z b :=
    goldbachWeightT14_eq_goldbachS6Closed A N z b
  have hLow :
      goldbachWeightLowMiddle A N z b c =
        goldbachS6HalfOpen A N z b + goldbachWeightT15 A N z b c :=
    goldbachWeightTriplePartition_lowMiddle_eq_goldbachS6HalfOpen_add_goldbachWeightT15
      A N z b c hzb hbc
  have hClosed :
      goldbachS6Closed A N z b =
        goldbachS6HalfOpen A N z b + goldbachB6 A N z b :=
    goldbachS6Closed_eq_goldbachS6HalfOpen_add_goldbachB6 A N z b
  omega

private theorem goldbachWeightTriplePartition_closedPrimes_subset_of_le
    (N : ℕ) (z c u : ℝ) (hcu : c ≤ u) :
    goldbachClosedPrimes N z c ⊆ goldbachClosedPrimes N z u := by
  intro t ht
  rcases mem_goldbachClosedPrimes_iff.mp ht with ⟨htPrime, htN, hzt, htc⟩
  exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htN, hzt, htc.trans hcu⟩

theorem goldbachWeightLowMiddle_monotone_right
    (A : Finset ℕ) (N : ℕ) (z b c u : ℝ)
    (hcu : c ≤ u) :
    goldbachWeightLowMiddle A N z b c ≤ goldbachWeightLowMiddle A N z b u := by
  unfold goldbachWeightLowMiddle
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (goldbachWeightTriplePartition_closedPrimes_subset_of_le N z c u hcu) ?_
  intro t ht huNot
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro s hs
  exact literalH_nonneg A (N * r) (r * s * t) s

theorem goldbachWeightT14_add_goldbachWeightT15_add_goldbachWeightUpperMiddle_le_goldbachS6Closed_add_goldbachB6
    (A : Finset ℕ) (N : ℕ) (z b c u : ℝ)
    (hz : 2 ≤ z) (hzb : z ≤ b) (hbc : b ≤ c) (hcu : c ≤ u) :
    goldbachWeightT14 A N z b + goldbachWeightT15 A N z b c +
        goldbachWeightUpperMiddle A N z b u ≤
      goldbachS6Closed A N z u + goldbachB6 A N z b := by
  have hsplit :
      goldbachWeightLowMiddle A N z b u +
          goldbachWeightUpperMiddle A N z b u =
        goldbachS6Closed A N z u :=
    goldbachWeightLowMiddle_add_goldbachWeightUpperMiddle_eq_goldbachS6Closed A N z b u
  have hmain :
      goldbachWeightT14 A N z b + goldbachWeightT15 A N z b c =
        goldbachWeightLowMiddle A N z b c + goldbachB6 A N z b :=
    goldbachWeightT14_add_goldbachWeightT15_eq_goldbachWeightLowMiddle_add_goldbachB6
      A N z b c hz hzb hbc
  have hmono :
      goldbachWeightLowMiddle A N z b c ≤ goldbachWeightLowMiddle A N z b u :=
    goldbachWeightLowMiddle_monotone_right A N z b c u hcu
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig