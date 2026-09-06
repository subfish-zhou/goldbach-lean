

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIBilinear

/-!
 # Canonical dyadic ledger for the full Vaughan Type-II prefix

The canonical blocks are the fibres of the floor binary logarithm on the
literal truncated ranges `u < d ≤ N` and `v < e ≤ N`.  Thus the first block
also handles `d = 1` (or `e = 1`), while a cutoff lying inside a dyadic shell
only truncates that one shell.  Every retained integer belongs to exactly one
block, including the zero/empty boundary cases.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The literal positive truncated interval `u < d ≤ N`. -/
def vaughanTypeIIRange (N u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun d => u < d)

@[simp] theorem mem_vaughanTypeIIRange {N u d : ℕ} :
    d ∈ vaughanTypeIIRange N u ↔ 0 < d ∧ d ≤ N ∧ u < d := by
  simp [vaughanTypeIIRange, Nat.succ_le_iff, and_assoc]

/-- Canonical dyadic bases, represented by binary-logarithm levels. -/
def vaughanCanonicalDyadicBases (N u : ℕ) : Finset ℕ :=
  (vaughanTypeIIRange N u).image (Nat.log 2)

/-- The canonical (possibly cutoff-truncated) binary shell at level `k`. -/
def vaughanCanonicalDyadicBlock (N u k : ℕ) : Finset ℕ :=
  (vaughanTypeIIRange N u).filter (fun d => Nat.log 2 d = k)

@[simp] theorem mem_vaughanCanonicalDyadicBlock {N u k d : ℕ} :
    d ∈ vaughanCanonicalDyadicBlock N u k ↔
      0 < d ∧ d ≤ N ∧ u < d ∧ Nat.log 2 d = k := by
  simp [vaughanCanonicalDyadicBlock, and_assoc]

/-- A level is selected exactly when its block is nonempty. -/
theorem mem_vaughanCanonicalDyadicBases_iff {N u k : ℕ} :
    k ∈ vaughanCanonicalDyadicBases N u ↔
      ∃ d ∈ vaughanCanonicalDyadicBlock N u k, True := by
  simp [vaughanCanonicalDyadicBases, vaughanCanonicalDyadicBlock]

/-- Every retained integer lies in the block indexed by its own level. -/
theorem mem_own_vaughanCanonicalDyadicBlock {N u d : ℕ}
    (hd : d ∈ vaughanTypeIIRange N u) :
    Nat.log 2 d ∈ vaughanCanonicalDyadicBases N u ∧
      d ∈ vaughanCanonicalDyadicBlock N u (Nat.log 2 d) := by
  constructor
  · exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  · simp [vaughanCanonicalDyadicBlock, hd]

/-- Membership determines the dyadic level uniquely. -/
theorem vaughanCanonicalDyadicBlock_level_unique {N u d k₁ k₂ : ℕ}
    (h₁ : d ∈ vaughanCanonicalDyadicBlock N u k₁)
    (h₂ : d ∈ vaughanCanonicalDyadicBlock N u k₂) : k₁ = k₂ := by
  exact (mem_vaughanCanonicalDyadicBlock.mp h₁).2.2.2.symm.trans
    (mem_vaughanCanonicalDyadicBlock.mp h₂).2.2.2

/-- A canonical level really is the half-open binary shell
`[2^k,2^(k+1))`, after the literal cutoff truncations. -/
theorem vaughanCanonicalDyadicBlock_pow_bounds {N u k d : ℕ}
    (hd : d ∈ vaughanCanonicalDyadicBlock N u k) :
    2 ^ k ≤ d ∧ d < 2 ^ (k + 1) := by
  have hpos : 0 < d := (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hlog : Nat.log 2 d = k :=
    (mem_vaughanCanonicalDyadicBlock.mp hd).2.2.2
  exact (Nat.log_eq_iff (Or.inr ⟨by omega, hpos.ne'⟩)).mp hlog

/-- Distinct canonical blocks are disjoint. -/
theorem vaughanCanonicalDyadicBlock_disjoint {N u k₁ k₂ : ℕ}
    (h : k₁ ≠ k₂) :
    Disjoint (vaughanCanonicalDyadicBlock N u k₁)
      (vaughanCanonicalDyadicBlock N u k₂) := by
  rw [Finset.disjoint_left]
  intro d hd₁ hd₂
  exact h (vaughanCanonicalDyadicBlock_level_unique hd₁ hd₂)

/-- The canonical blocks cover the retained interval exactly. -/
theorem biUnion_vaughanCanonicalDyadicBlock (N u : ℕ) :
    (vaughanCanonicalDyadicBases N u).biUnion
      (vaughanCanonicalDyadicBlock N u) = vaughanTypeIIRange N u := by
  ext d
  constructor
  · simp only [Finset.mem_biUnion]
    rintro ⟨k, hk, hd⟩
    exact (Finset.mem_filter.mp hd).1
  · intro hd
    exact Finset.mem_biUnion.mpr
      ⟨Nat.log 2 d, (mem_own_vaughanCanonicalDyadicBlock hd).1,
        (mem_own_vaughanCanonicalDyadicBlock hd).2⟩

/-- If the strict cutoff reaches the upper endpoint, every canonical block
base disappears.  This includes the `N = 0` boundary. -/
theorem vaughanCanonicalDyadicBases_eq_empty_of_le {N u : ℕ} (hNu : N ≤ u) :
    vaughanCanonicalDyadicBases N u = ∅ := by
  have hrange : vaughanTypeIIRange N u = ∅ := by
    ext d
    simp [vaughanTypeIIRange]
    omega
  simp [vaughanCanonicalDyadicBases, hrange]

/-- Exact one-dimensional fibrewise sum ledger. -/
theorem sum_vaughanCanonicalDyadicBlock {M : Type*} [AddCommMonoid M]
    (N u : ℕ) (f : ℕ → M) :
    (∑ k ∈ vaughanCanonicalDyadicBases N u,
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k, f d) =
        ∑ d ∈ vaughanTypeIIRange N u, f d := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f

/-- The number of nonempty canonical shells has the exact natural upper bound
`log₂ N + 1`, uniformly in the cutoff (and also when the range is empty). -/
theorem card_vaughanCanonicalDyadicBases_le (N u : ℕ) :
    (vaughanCanonicalDyadicBases N u).card ≤ Nat.log 2 N + 1 := by
  calc
    (vaughanCanonicalDyadicBases N u).card ≤
        (Finset.range (Nat.log 2 N + 1)).card := by
      apply Finset.card_le_card
      intro k hk
      rw [Finset.mem_range]
      rw [vaughanCanonicalDyadicBases, Finset.mem_image] at hk
      obtain ⟨d, hd, rfl⟩ := hk
      have hdN : d ≤ N := (mem_vaughanTypeIIRange.mp hd).2.1
      exact Nat.lt_succ_of_le (Nat.log_monotone hdN)
    _ = Nat.log 2 N + 1 := Finset.card_range _

/-- Canonical rectangle indices for the two cutoff ranges. -/
def vaughanCanonicalDyadicRectangles (N u v : ℕ) : Finset (ℕ × ℕ) :=
  vaughanCanonicalDyadicBases N u ×ˢ vaughanCanonicalDyadicBases N v

/-- The integer pairs belonging to one canonical dyadic rectangle. -/
def vaughanCanonicalDyadicRectangleBlock
    (N u v : ℕ) (kl : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  vaughanCanonicalDyadicBlock N u kl.1 ×ˢ
    vaughanCanonicalDyadicBlock N v kl.2

/-- A retained pair belongs to the rectangle indexed by its two logarithms. -/
theorem mem_own_vaughanCanonicalDyadicRectangleBlock {N u v d e : ℕ}
    (hd : d ∈ vaughanTypeIIRange N u) (he : e ∈ vaughanTypeIIRange N v) :
    (Nat.log 2 d, Nat.log 2 e) ∈ vaughanCanonicalDyadicRectangles N u v ∧
      (d, e) ∈ vaughanCanonicalDyadicRectangleBlock N u v
        (Nat.log 2 d, Nat.log 2 e) := by
  exact ⟨Finset.mem_product.mpr
      ⟨(mem_own_vaughanCanonicalDyadicBlock hd).1,
        (mem_own_vaughanCanonicalDyadicBlock he).1⟩,
    Finset.mem_product.mpr
      ⟨(mem_own_vaughanCanonicalDyadicBlock hd).2,
        (mem_own_vaughanCanonicalDyadicBlock he).2⟩⟩

/-- Membership of a pair determines its canonical rectangle uniquely. -/
theorem vaughanCanonicalDyadicRectangleBlock_level_unique
    {N u v d e : ℕ} {kl₁ kl₂ : ℕ × ℕ}
    (h₁ : (d, e) ∈ vaughanCanonicalDyadicRectangleBlock N u v kl₁)
    (h₂ : (d, e) ∈ vaughanCanonicalDyadicRectangleBlock N u v kl₂) :
    kl₁ = kl₂ := by
  apply Prod.ext
  · exact vaughanCanonicalDyadicBlock_level_unique
      (Finset.mem_product.mp h₁).1 (Finset.mem_product.mp h₂).1
  · exact vaughanCanonicalDyadicBlock_level_unique
      (Finset.mem_product.mp h₁).2 (Finset.mem_product.mp h₂).2

/-- Distinct canonical rectangles are pairwise disjoint. -/
theorem vaughanCanonicalDyadicRectangleBlock_disjoint
    {N u v : ℕ} {kl₁ kl₂ : ℕ × ℕ} (h : kl₁ ≠ kl₂) :
    Disjoint (vaughanCanonicalDyadicRectangleBlock N u v kl₁)
      (vaughanCanonicalDyadicRectangleBlock N u v kl₂) := by
  rw [Finset.disjoint_left]
  intro de hde₁ hde₂
  exact h (vaughanCanonicalDyadicRectangleBlock_level_unique hde₁ hde₂)

/-- The rectangle family is an exact disjoint cover of all pairs satisfying
`u < d ≤ N` and `v < e ≤ N`. -/
theorem biUnion_vaughanCanonicalDyadicRectangleBlock (N u v : ℕ) :
    (vaughanCanonicalDyadicRectangles N u v).biUnion
      (vaughanCanonicalDyadicRectangleBlock N u v) =
        vaughanTypeIIRange N u ×ˢ vaughanTypeIIRange N v := by
  ext de
  constructor
  · simp only [Finset.mem_biUnion]
    rintro ⟨kl, hkl, hde⟩
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hde).1).1,
        (Finset.mem_filter.mp (Finset.mem_product.mp hde).2).1⟩
  · intro hde
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hde
    exact Finset.mem_biUnion.mpr
      ⟨(Nat.log 2 de.1, Nat.log 2 de.2),
        (mem_own_vaughanCanonicalDyadicRectangleBlock hd he).1,
        (mem_own_vaughanCanonicalDyadicRectangleBlock hd he).2⟩

/-- Precise `O(log² N)` natural-number rectangle count. -/
theorem card_vaughanCanonicalDyadicRectangles_le (N u v : ℕ) :
    (vaughanCanonicalDyadicRectangles N u v).card ≤ (Nat.log 2 N + 1) ^ 2 := by
  rw [vaughanCanonicalDyadicRectangles, Finset.card_product, pow_two]
  exact Nat.mul_le_mul (card_vaughanCanonicalDyadicBases_le N u)
    (card_vaughanCanonicalDyadicBases_le N v)

/-- The actual nested Vaughan Type-II factor at `n`, with complex weights. -/
def vaughanTypeIIFullAt (n u v : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => v < e),
      vaughanMoebiusCoeff d * vaughanMangoldtCoeff e

/-- The complex nested factor is literally the cast of Vaughan's real
`vaughanThird` (the public Type-II factor). -/
theorem vaughanTypeIIFullAt_eq_vaughanThird (n u v : ℕ) :
    vaughanTypeIIFullAt n u v = (Sieve.vaughanThird n u v : ℂ) := by
  unfold vaughanTypeIIFullAt Sieve.vaughanThird
    vaughanMoebiusCoeff vaughanMangoldtCoeff
  push_cast
  rfl

/-- On a positive prefix `n ≤ N`, the nested divisor factor is exactly the
bounded rectangular divisibility sum. -/
theorem vaughanTypeIIFullAt_eq_bounded_rectangular {n N u v : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    vaughanTypeIIFullAt n u v =
      ∑ d ∈ vaughanTypeIIRange N u,
        ∑ e ∈ vaughanTypeIIRange N v,
          if d * e ∣ n then
            vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0 := by
  unfold vaughanTypeIIFullAt
  have hdset : n.divisors.filter (fun d => u < d) =
      (vaughanTypeIIRange N u).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hud⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨mem_vaughanTypeIIRange.mpr
        ⟨hdpos, (Nat.le_of_dvd hn hdn).trans hnN, hud⟩, hdn⟩
    · rintro ⟨hd, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩,
        (mem_vaughanTypeIIRange.mp hd).2.2⟩
  rw [hdset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdpos : 0 < d := (mem_vaughanTypeIIRange.mp hd).1
    have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have heset : (n / d).divisors.filter (fun e => v < e) =
        (vaughanTypeIIRange N v).filter (fun e => d * e ∣ n) := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hed, _⟩, hve⟩
        have hmul : d * e ∣ n := (Nat.dvd_div_iff_mul_dvd hdn).mp hed
        have hepos : 0 < e := Nat.pos_of_dvd_of_pos hed hndpos
        have hen : e ≤ n := Nat.le_of_dvd hn ((dvd_mul_left e d).trans hmul)
        exact ⟨mem_vaughanTypeIIRange.mpr ⟨hepos, hen.trans hnN, hve⟩, hmul⟩
      · rintro ⟨he, hmul⟩
        have hed : e ∣ n / d := (Nat.dvd_div_iff_mul_dvd hdn).mpr hmul
        exact ⟨⟨hed, hndpos.ne'⟩,
          (mem_vaughanTypeIIRange.mp he).2.2⟩
    rw [heset, Finset.sum_filter]
  · have hde : ∀ e : ℕ, ¬ d * e ∣ n := by
      intro e h
      exact hdn ((dvd_mul_right d e).trans h)
    simp [hdn, hde]

/-- Pointwise two-dimensional canonical partition of the full Type-II factor. -/
theorem vaughanTypeIIFullAt_eq_sum_canonical_blocks {n N u v : ℕ}
    (hn : 0 < n) (hnN : n ≤ N) :
    vaughanTypeIIFullAt n u v =
      ∑ k ∈ vaughanCanonicalDyadicBases N u,
        ∑ l ∈ vaughanCanonicalDyadicBases N v,
          ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
            ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
              if d * e ∣ n then
                vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0 := by
  rw [vaughanTypeIIFullAt_eq_bounded_rectangular hn hnN]
  rw [← sum_vaughanCanonicalDyadicBlock N u (fun d =>
    ∑ e ∈ vaughanTypeIIRange N v,
      if d * e ∣ n then
        vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  -- Partition the `e` range using the one-dimensional ledger, then restore `d,e` order.
  rw [Finset.sum_comm, ← sum_vaughanCanonicalDyadicBlock N v]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

/-- One canonical rectangle before the `n=d*e*m` substitution. -/
def vaughanTypeIICanonicalBlockPrefix
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) *
      ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
        ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
          if d * e ∣ n then
            vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0

/-- The separated bilinear form attached to one canonical rectangle. -/
def vaughanTypeIICanonicalBilinearBlock
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
    (vaughanMoebiusCoeff d * χ.1 (d : ZMod q)) *
      ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
        (vaughanMangoldtCoeff e * χ.1 (e : ZMod q)) *
          ∑ m ∈ Finset.Icc 1 (y / (d * e)),
            b (d * e * m) * χ.1 (m : ZMod q)

/-- Exact finite substitution and character separation on a canonical block.
Positivity is obtained from block membership, so no global assumption on
`N,u,v,k,l` is needed. -/
theorem vaughanTypeIICanonicalBlockPrefix_eq_bilinear
    (b : ℕ → ℂ) (y N u v k l q : ℕ) (χ : PrimitiveCharacter q) :
    vaughanTypeIICanonicalBlockPrefix b y N u v k l q χ =
      vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
  unfold vaughanTypeIICanonicalBlockPrefix vaughanTypeIICanonicalBilinearBlock
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hdpos : 0 < d := (mem_vaughanCanonicalDyadicBlock.mp hd).1
  have hepos : 0 < e := (mem_vaughanCanonicalDyadicBlock.mp he).1
  have hkpos : 0 < d * e := Nat.mul_pos hdpos hepos
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [sum_multiples_Icc_reindex
    (fun n => b n * χ.1 (n : ZMod q) *
      (vaughanMoebiusCoeff d * vaughanMangoldtCoeff e)) hkpos]
  apply Finset.sum_congr rfl
  intro m hm
  have hcast : ((d * e * m : ℕ) : ZMod q) =
      (d : ZMod q) * (e : ZMod q) * (m : ZMod q) := by
    simp only [Nat.cast_mul]
  rw [hcast, map_mul, map_mul]
  ring

/-- The complete Vaughan Type-II prefix (before any analytic inequality). -/
def vaughanTypeIIFullPrefix
    (b : ℕ → ℂ) (y u v q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIIFullAt n u v

/-- Full Type-II ledger: the literal prefix is exactly the finite sum of the
canonical dyadic rectangles, each already in separated bilinear form.  The
hypothesis `y ≤ N` is precisely what turns divisors of prefix indices into the
bounds `d,e ≤ N`; all strict-cutoff and empty-range boundary cases remain
literal in the definitions. -/
theorem vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear
    (b : ℕ → ℂ) (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix b y u v q χ =
      ∑ k ∈ vaughanCanonicalDyadicBases N u,
        ∑ l ∈ vaughanCanonicalDyadicBases N v,
          vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
  calc
    vaughanTypeIIFullPrefix b y u v q χ =
        ∑ n ∈ Finset.Icc 1 y,
          b n * χ.1 (n : ZMod q) *
            (∑ k ∈ vaughanCanonicalDyadicBases N u,
              ∑ l ∈ vaughanCanonicalDyadicBases N v,
                ∑ d ∈ vaughanCanonicalDyadicBlock N u k,
                  ∑ e ∈ vaughanCanonicalDyadicBlock N v l,
                    if d * e ∣ n then
                      vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0) := by
      unfold vaughanTypeIIFullPrefix
      apply Finset.sum_congr rfl
      intro n hn
      rw [vaughanTypeIIFullAt_eq_sum_canonical_blocks
        (Finset.mem_Icc.mp hn).1 ((Finset.mem_Icc.mp hn).2.trans hyN)]
    _ = ∑ k ∈ vaughanCanonicalDyadicBases N u,
          ∑ l ∈ vaughanCanonicalDyadicBases N v,
            vaughanTypeIICanonicalBlockPrefix b y N u v k l q χ := by
      unfold vaughanTypeIICanonicalBlockPrefix
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k ∈ vaughanCanonicalDyadicBases N u,
          ∑ l ∈ vaughanCanonicalDyadicBases N v,
            vaughanTypeIICanonicalBilinearBlock b y N u v k l q χ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      exact vaughanTypeIICanonicalBlockPrefix_eq_bilinear b y N u v k l q χ

/-- A compact package for handing the full Type-II lane to a bilinear large
sieve: exact equality plus the natural rectangle-count budget. -/
theorem vaughanTypeIIFullLedger
    (b : ℕ → ℂ) (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix b y u v q χ =
        ∑ kl ∈ vaughanCanonicalDyadicRectangles N u v,
          vaughanTypeIICanonicalBilinearBlock b y N u v kl.1 kl.2 q χ ∧
      (vaughanCanonicalDyadicRectangles N u v).card ≤
        (Nat.log 2 N + 1) ^ 2 := by
  constructor
  · rw [vaughanCanonicalDyadicRectangles, Finset.sum_product]
    exact vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear b y N u v q χ hyN
  · exact card_vaughanCanonicalDyadicRectangles_le N u v

end

end AnalyticNumberTheory.LargeSieve
