import MathlibNt.SieveTheory.LiLiuGoldbachDoubleDifference

open scoped BigOperators

open Finset

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachClosedTriples (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Closed prime carrier `z ≤ p ≤ y`, keeping the actual conditions
`p.Prime` and `p ∤ N`. -/
noncomputable def goldbachClosedPrimes (N : ℕ) (z y : ℝ) : Finset ℕ :=
  (siftingPrimes N (y + 1)).filter fun p : ℕ => z ≤ (p : ℝ) ∧ (p : ℝ) ≤ y

theorem mem_goldbachHalfOpenPrimes_iff {N p : ℕ} {z y : ℝ} :
    p ∈ goldbachHalfOpenPrimes N z y ↔
      p.Prime ∧ ¬p ∣ N ∧ z ≤ (p : ℝ) ∧ (p : ℝ) < y := by
  rw [goldbachHalfOpenPrimes, Finset.mem_filter, mem_siftingPrimes]
  constructor
  · rintro ⟨⟨hpPrime, hpy, hpN⟩, hpz⟩
    exact ⟨hpPrime, hpN, hpz, hpy⟩
  · rintro ⟨hpPrime, hpN, hpz, hpy⟩
    exact ⟨⟨hpPrime, hpy, hpN⟩, hpz⟩

theorem mem_goldbachClosedPrimes_iff {N p : ℕ} {z y : ℝ} :
    p ∈ goldbachClosedPrimes N z y ↔
      p.Prime ∧ ¬p ∣ N ∧ z ≤ (p : ℝ) ∧ (p : ℝ) ≤ y := by
  rw [goldbachClosedPrimes, Finset.mem_filter, mem_siftingPrimes]
  constructor
  · rintro ⟨⟨hpPrime, hpUpper, hpN⟩, hpz, hpy⟩
    exact ⟨hpPrime, hpN, hpz, hpy⟩
  · rintro ⟨hpPrime, hpN, hpz, hpy⟩
    refine ⟨⟨hpPrime, ?_, hpN⟩, hpz, hpy⟩
    have hy1 : y < y + 1 := by linarith
    exact hpy.trans_lt hy1

theorem literalH_nonneg (A : Finset ℕ) (M d : ℕ) (x : ℝ) :
    0 ≤ literalH A M d x := by
  unfold literalH
  exact_mod_cast Nat.zero_le ((A.filter (literalHPoint M d x)).card)

private theorem goldbachClosedPrimes_filter_lt_eq_halfOpen
    (N : ℕ) (z y : ℝ) :
    (goldbachClosedPrimes N z y).filter (fun p : ℕ => (p : ℝ) < y) =
      goldbachHalfOpenPrimes N z y := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpy⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨hpPrime, hpN, hpz, _⟩
    exact mem_goldbachHalfOpenPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpy⟩
  · intro hp
    rcases mem_goldbachHalfOpenPrimes_iff.mp hp with ⟨hpPrime, hpN, hpz, hpy⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpPrime, hpN, hpz, hpy.le⟩, hpy⟩

private theorem goldbachClosedPrimes_filter_not_lt_self_eq_singleton
    (N : ℕ) (z : ℝ) {t : ℕ}
    (ht : t ∈ goldbachClosedPrimes N z (t : ℝ)) :
    ((goldbachClosedPrimes N z (t : ℝ)).filter fun p : ℕ => ¬(p : ℝ) < t) = {t} := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpClosed, hpNotLt⟩
    rcases mem_goldbachClosedPrimes_iff.mp hpClosed with ⟨_, _, _, hpt⟩
    have htp : (t : ℝ) ≤ p := not_lt.mp hpNotLt
    have hptNat : p ≤ t := by exact_mod_cast hpt
    have htpNat : t ≤ p := by exact_mod_cast htp
    exact Finset.mem_singleton.mpr (le_antisymm hptNat htpNat)
  · intro hp
    rcases Finset.mem_singleton.mp hp with rfl
    exact Finset.mem_filter.mpr ⟨ht, not_lt.mpr le_rfl⟩

private theorem goldbachClosedMiddle_filter_strict_eq_halfOpen
    (N r t : ℕ) :
    ((goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
      (fun s : ℕ => r < s ∧ (s : ℝ) < t)) =
      (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r < s) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hrs, hst⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨hsPrime, hsN, hrsLe, _⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachHalfOpenPrimes_iff.mpr ⟨hsPrime, hsN, hrsLe, hst⟩, hrs⟩
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsHalf, hrs⟩
    rcases mem_goldbachHalfOpenPrimes_iff.mp hsHalf with ⟨hsPrime, hsN, hrsLe, hst⟩
    exact Finset.mem_filter.mpr
      ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hsPrime, hsN, hrsLe, hst.le⟩, hrs, hst⟩

private theorem goldbachClosedMiddle_filter_not_strict_eq_repeat
    (N r t : ℕ) :
    ((goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
      (fun s : ℕ => ¬(r < s ∧ (s : ℝ) < t))) =
      ((goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
        (fun s : ℕ => r = s ∨ s = t)) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hsNotStrict⟩
    rcases mem_goldbachClosedPrimes_iff.mp hsClosed with ⟨_, _, hrsLe, hstLe⟩
    have hrsLeNat : r ≤ s := by exact_mod_cast hrsLe
    have hstLeNat : s ≤ t := by exact_mod_cast hstLe
    have hRepeat : r = s ∨ s = t := by
      by_cases hrs : r < s
      · by_cases hst : s < t
        · exfalso
          exact hsNotStrict ⟨hrs, by exact_mod_cast hst⟩
        · right
          omega
      · left
        omega
    exact Finset.mem_filter.mpr ⟨hsClosed, hRepeat⟩
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsClosed, hRepeat⟩
    refine Finset.mem_filter.mpr ⟨hsClosed, ?_⟩
    rintro ⟨hrs, hst⟩
    rcases hRepeat with rfl | rfl
    · exact (lt_irrefl _ hrs).elim
    · exact (lt_irrefl _ hst).elim

/-- Actual weakly ordered half-open triple sum `S6h`, with `t < y` but
`r = s`, `s = t`, and `r = s = t` all retained. -/
noncomputable def goldbachS6HalfOpen (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ t ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
        literalH A (N * r) (r * s * t) s

/-- Actual repeat mass `R`, counting exactly the weakly ordered half-open
triples with `r = s` or `s = t`. -/
noncomputable def goldbachR (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ t ∈ goldbachHalfOpenPrimes N z y,
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
          (fun s : ℕ => r = s ∨ s = t),
        literalH A (N * r) (r * s * t) s

/-- Actual weakly ordered closed triple sum `S6closed`, with `t ≤ y`. -/
noncomputable def goldbachS6Closed (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ t ∈ goldbachClosedPrimes N z y,
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
        literalH A (N * r) (r * s * t) s

/-- Actual endpoint mass `B6`, i.e. the part of `S6closed` with `t = y`
when such a prime exists, and zero otherwise. -/
noncomputable def goldbachB6 (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ t ∈ (goldbachClosedPrimes N z y).filter (fun t : ℕ => y ≤ (t : ℝ)),
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
      ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
        literalH A (N * r) (r * s * t) s

theorem goldbachR_nonneg (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    0 ≤ goldbachR A N z y := by
  unfold goldbachR
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro s hs
  exact literalH_nonneg A (N * r) (r * s * t) s

theorem goldbachB6_nonneg (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    0 ≤ goldbachB6 A N z y := by
  unfold goldbachB6
  refine Finset.sum_nonneg ?_
  intro t ht
  refine Finset.sum_nonneg ?_
  intro r hr
  refine Finset.sum_nonneg ?_
  intro s hs
  exact literalH_nonneg A (N * r) (r * s * t) s

private theorem goldbachStrictMiddleEndpoint_empty
    (N t : ℕ) :
    ((goldbachClosedPrimes N (t : ℝ) (t : ℝ)).filter
      (fun s : ℕ => t < s ∧ (s : ℝ) < t)) = ∅ := by
  ext s
  constructor
  · intro hs
    exfalso
    rcases Finset.mem_filter.mp hs with ⟨_, ⟨hts, hst⟩⟩
    have hts' : (t : ℝ) < s := by exact_mod_cast hts
    linarith
  · intro hs
    cases hs

private theorem goldbachS6HalfOpen_slice_eq_goldbachWStrict_slice_add_goldbachR_slice
    (A : Finset ℕ) (N : ℕ) (z : ℝ) (t : ℕ)
    (htClosed : t ∈ goldbachClosedPrimes N z (t : ℝ)) :
    (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
          literalH A (N * r) (r * s * t) s) =
      (∑ r ∈ goldbachHalfOpenPrimes N z (t : ℝ),
        ∑ s ∈ (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r < s),
          literalH A (N * r) (r * s * t) s) +
      (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r = s ∨ s = t),
          literalH A (N * r) (r * s * t) s) := by
  calc
    ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
          literalH A (N * r) (r * s * t) s =
      ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
        ((∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r < s ∧ (s : ℝ) < t),
            literalH A (N * r) (r * s * t) s) +
          ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r = s ∨ s = t),
            literalH A (N * r) (r * s * t) s) := by
              apply Finset.sum_congr rfl
              intro r hr
              have hsplit :=
                Finset.sum_filter_add_sum_filter_not
                  (goldbachClosedPrimes N (r : ℝ) (t : ℝ))
                  (fun s : ℕ => r < s ∧ (s : ℝ) < t)
                  (fun s => literalH A (N * r) (r * s * t) s)
              rw [← hsplit, goldbachClosedMiddle_filter_not_strict_eq_repeat]
    _ = (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r < s ∧ (s : ℝ) < t),
            literalH A (N * r) (r * s * t) s) +
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r = s ∨ s = t),
            literalH A (N * r) (r * s * t) s := by
          rw [Finset.sum_add_distrib]
    _ = (∑ r ∈ goldbachHalfOpenPrimes N z (t : ℝ),
          ∑ s ∈ (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r < s),
            literalH A (N * r) (r * s * t) s) +
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
            (fun s : ℕ => r = s ∨ s = t),
            literalH A (N * r) (r * s * t) s := by
          have hsplitR :=
            Finset.sum_filter_add_sum_filter_not
              (goldbachClosedPrimes N z (t : ℝ))
              (fun r : ℕ => (r : ℝ) < t)
              (fun r =>
                ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
                    (fun s : ℕ => r < s ∧ (s : ℝ) < t),
                  literalH A (N * r) (r * s * t) s)
          rw [← hsplitR]
          have hstrictR :
              (goldbachClosedPrimes N z (t : ℝ)).filter (fun r : ℕ => (r : ℝ) < t) =
                goldbachHalfOpenPrimes N z (t : ℝ) :=
            goldbachClosedPrimes_filter_lt_eq_halfOpen N z (t : ℝ)
          have hdiagR :
              ((goldbachClosedPrimes N z (t : ℝ)).filter fun r : ℕ => ¬(r : ℝ) < t) = {t} :=
            goldbachClosedPrimes_filter_not_lt_self_eq_singleton N z htClosed
          rw [hstrictR, hdiagR, Finset.sum_singleton]
          rw [goldbachStrictMiddleEndpoint_empty, Finset.sum_empty, add_zero]
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          rw [goldbachClosedMiddle_filter_strict_eq_halfOpen]

theorem goldbachS6HalfOpen_eq_goldbachWStrict_add_goldbachR
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachS6HalfOpen A N z y = goldbachWStrict A N z y + goldbachR A N z y := by
  unfold goldbachS6HalfOpen goldbachWStrict goldbachR
  calc
    ∑ t ∈ goldbachHalfOpenPrimes N z y,
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
            literalH A (N * r) (r * s * t) s =
      ∑ t ∈ goldbachHalfOpenPrimes N z y,
        ((∑ r ∈ goldbachHalfOpenPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r < s),
              literalH A (N * r) (r * s * t) s) +
          (∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => r = s ∨ s = t),
              literalH A (N * r) (r * s * t) s)) := by
            apply Finset.sum_congr rfl
            intro t ht
            have htClosed : t ∈ goldbachClosedPrimes N z (t : ℝ) := by
              rcases mem_goldbachHalfOpenPrimes_iff.mp ht with ⟨htPrime, htN, htz, _⟩
              exact mem_goldbachClosedPrimes_iff.mpr ⟨htPrime, htN, htz, le_rfl⟩
            exact goldbachS6HalfOpen_slice_eq_goldbachWStrict_slice_add_goldbachR_slice
              A N z t htClosed
    _ = (∑ t ∈ goldbachHalfOpenPrimes N z y,
          ∑ r ∈ goldbachHalfOpenPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachHalfOpenPrimes N (r : ℝ) (t : ℝ)).filter (fun s : ℕ => r < s),
              literalH A (N * r) (r * s * t) s) +
        ∑ t ∈ goldbachHalfOpenPrimes N z y,
          ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
            ∑ s ∈ (goldbachClosedPrimes N (r : ℝ) (t : ℝ)).filter
              (fun s : ℕ => r = s ∨ s = t),
              literalH A (N * r) (r * s * t) s := by
          rw [Finset.sum_add_distrib]
    _ = goldbachWStrict A N z y + goldbachR A N z y := by
          simp [goldbachWStrict, goldbachR]

theorem goldbachS6Closed_eq_goldbachS6HalfOpen_add_goldbachB6
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachS6Closed A N z y = goldbachS6HalfOpen A N z y + goldbachB6 A N z y := by
  unfold goldbachS6Closed goldbachS6HalfOpen goldbachB6
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z y)
      (fun t : ℕ => (t : ℝ) < y)
      (fun t =>
        ∑ r ∈ goldbachClosedPrimes N z (t : ℝ),
          ∑ s ∈ goldbachClosedPrimes N (r : ℝ) (t : ℝ),
            literalH A (N * r) (r * s * t) s)
  rw [goldbachClosedPrimes_filter_lt_eq_halfOpen] at hsplit
  simpa [not_lt] using hsplit.symm

theorem goldbachWStrict_eq_goldbachS6Closed_sub_goldbachR_sub_goldbachB6
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachWStrict A N z y = goldbachS6Closed A N z y - goldbachR A N z y - goldbachB6 A N z y := by
  calc
    goldbachWStrict A N z y =
        goldbachS6HalfOpen A N z y - goldbachR A N z y := by
          have h := goldbachS6HalfOpen_eq_goldbachWStrict_add_goldbachR A N z y
          omega
    _ = (goldbachS6Closed A N z y - goldbachB6 A N z y) - goldbachR A N z y := by
          rw [goldbachS6Closed_eq_goldbachS6HalfOpen_add_goldbachB6]
          ring
    _ = goldbachS6Closed A N z y - goldbachR A N z y - goldbachB6 A N z y := by
          ring

/-- Closed `S3`, keeping the literal endpoint `p = y` when it exists. -/
noncomputable def goldbachS3Closed (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ s ∈ goldbachClosedPrimes N z y, literalH A N s z

/-- Closed `S5`, keeping the literal endpoint `r = y` in the first prime. -/
noncomputable def goldbachS5Closed (A : Finset ℕ) (N : ℕ) (z y : ℝ) : ℤ :=
  ∑ rs ∈ (goldbachS4Pairs N z).filter
      (fun rs => (rs.1 : ℝ) ≤ y ∧ y ≤ (rs.2 : ℝ)),
    literalH A (N * rs.1) (rs.1 * rs.2) rs.2

theorem goldbachS3HalfOpen_le_goldbachS3Closed
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachS3HalfOpen A N z y ≤ goldbachS3Closed A N z y := by
  unfold goldbachS3HalfOpen goldbachS3Closed
  rw [← goldbachClosedPrimes_filter_lt_eq_halfOpen N z y]
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (goldbachClosedPrimes N z y)
      (fun s : ℕ => (s : ℝ) < y)
      (fun s => literalH A N s z)
  have hnonneg :
      0 ≤ ∑ s ∈ (goldbachClosedPrimes N z y).filter (fun s : ℕ => ¬(s : ℝ) < y),
        literalH A N s z := by
          refine Finset.sum_nonneg ?_
          intro s hs
          exact literalH_nonneg A N s z
  linarith

theorem goldbachS5HalfOpen_le_goldbachS5Closed
    (A : Finset ℕ) (N : ℕ) (z y : ℝ) :
    goldbachS5HalfOpen A N z y ≤ goldbachS5Closed A N z y := by
  unfold goldbachS5HalfOpen goldbachS5Closed
  have hcarrier :
      ((goldbachS4Pairs N z).filter (fun rs : ℕ × ℕ => (rs.1 : ℝ) ≤ y ∧ y ≤ (rs.2 : ℝ))).filter
        (fun rs : ℕ × ℕ => (rs.1 : ℝ) < y) =
      (goldbachS4Pairs N z).filter (fun rs : ℕ × ℕ => (rs.1 : ℝ) < y ∧ y ≤ (rs.2 : ℝ)) := by
    ext rs
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hrs, _, hrs2⟩, hrs1lt⟩
      exact ⟨hrs, hrs1lt, hrs2⟩
    · rintro ⟨hrs, hrs1lt, hrs2⟩
      exact ⟨⟨hrs, hrs1lt.le, hrs2⟩, hrs1lt⟩
  rw [← hcarrier]
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      ((goldbachS4Pairs N z).filter (fun rs : ℕ × ℕ => (rs.1 : ℝ) ≤ y ∧ y ≤ (rs.2 : ℝ)))
      (fun rs : ℕ × ℕ => (rs.1 : ℝ) < y)
      (fun rs => literalH A (N * rs.1) (rs.1 * rs.2) rs.2)
  have hnonneg :
      0 ≤
        ∑ rs ∈
          ((goldbachS4Pairs N z).filter (fun rs : ℕ × ℕ => (rs.1 : ℝ) ≤ y ∧ y ≤ (rs.2 : ℝ))).filter
            (fun rs : ℕ × ℕ => ¬(rs.1 : ℝ) < y),
          literalH A (N * rs.1) (rs.1 * rs.2) rs.2 := by
            refine Finset.sum_nonneg ?_
            intro rs hrs
            exact literalH_nonneg A (N * rs.1) (rs.1 * rs.2) rs.2
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig