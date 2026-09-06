import AnalyticNumberTheory.LargeSieve.Duality
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.WellSpaced

## Well-spaced points and the Schur test

This module combines the dual quadratic-form identity
(`dualQuadraticIdentity_Icc`, `Duality.lean`) with the interval
geometric-sum bound (`geomSum_exp_bound_Icc`, `GeomSum.lean`) to prove
an additive large-sieve inequality with an explicit weaker constant.

The spacing condition is parametrized by `ℝ`: a set `X ⊆ ℝ` is
`δ`-well-spaced modulo 1 if any two distinct points have distance
`distToInt` at least `δ`. This corresponds to `wellSpaced` on
`AddCircle 1` in `Additive.lean`, while keeping the counting geometry
in the real numbers and their fractional parts. The circle formulation
requires a separate bridge.

Proof structure (the classical Montgomery framework, with a weaker constant):

1. **Counting**: a set in `[a, a+L]` with pairwise real distances at
   least `δ` has at most `L/δ + 1` points (`sepCard_le_interval`,
   by induction on the largest point). Splitting fractional parts into
   `[0,r]` and `[1−r,1]` gives the ball count
   `#{y : distToInt(x−y) ≤ r} ≤ 2r/δ + 2`
   (`wellSpaced_ball_card_le`).
2. **Dyadic-shell row sum**: for fixed `x`, group `Σ_y |K(x,y)|`
   by dyadic shells of `distToInt(x−y)`. Each shell has at most
   `2·2^{-j}/δ + 2` points; the geometric bound `≤ 1/(2ρ)` gives
   `Σ_{y∈X} |Σ_{M<n≤M+N} e(n(x−y))| ≤ N + (2K+12)/δ`,
   where `K = ⌈log₂(1/δ)⌉` (`wellSpacedRowSum`).
3. **Schur/Cauchy--Schwarz test** (`quadraticFormBound`):
   for a kernel with symmetric norms (`|K xy| = |K yx|`), as for
   a Hermitian kernel, row sums at most `C` imply
   `|Σ_x Σ_y b_x·conj(b_y)·K_xy| ≤ C·Σ_x |b_x|²`.
4. **Assembly**: the dual identity, row-sum bound, and Schur test give
   `largeSieveDual_wellSpaced`; `largeSieveDuality` then gives
   `largeSievePrimal_wellSpaced`.

The explicit weaker constant is
`C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`, with the ceiling taken in `ℕ`.
The classical sharp constant `N + 1/δ` requires Montgomery's
positive-kernel/Parseval method (a Fejér-kernel majorant or a
Hilbert-type quadratic-form estimate). It is not proved here:
naive dyadic-shell counting and the Schur test incur a `log(1/δ)` factor.

References: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/-! ## 1. Real-parametrized well-spaced sets and basic distance properties -/

/-- `X ⊆ ℝ` is `δ`-well-spaced modulo 1: any two distinct points have
distance modulo 1 at least `δ`. This corresponds to `wellSpaced` on
`AddCircle 1` in `Additive.lean`. -/
def wellSpacedReal (X : Finset ℝ) (δ : ℝ) : Prop :=
  ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → x ≠ y → δ ≤ distToInt (x - y)

/-- Distance modulo 1 is bounded by every integer translate:
`‖z‖ ≤ |z − k|` (`k : ℤ`). -/
theorem distToInt_le_sub (z : ℝ) (k : ℤ) : distToInt z ≤ |z - (k : ℝ)| := by
  dsimp [distToInt]
  by_cases hk : (k : ℝ) ≤ ⌊z⌋
  · have hnonneg : 0 ≤ z - (k : ℝ) := by
      have hz : (k : ℝ) ≤ z := le_trans hk (Int.floor_le z)
      linarith
    have hz : z - (k : ℝ) = Int.fract z + ((⌊z⌋ : ℝ) - (k : ℝ)) := by
      rw [← Int.self_sub_floor z]
      ring
    rw [abs_of_nonneg hnonneg, hz]
    have h1 : Int.fract z ≤ Int.fract z + ((⌊z⌋ : ℝ) - (k : ℝ)) := by linarith
    exact le_trans (min_le_left _ _) h1
  · have hklt : ⌊z⌋ < (k : ℝ) := lt_of_not_ge hk
    have hkz : ⌊z⌋ < k := by exact_mod_cast hklt
    have hk1 : ⌊z⌋ + 1 ≤ k := by omega
    have hk1r : (⌊z⌋ : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk1
    have hnonneg : 0 ≤ (k : ℝ) - z := by
      have hzlt : z < (k : ℝ) := lt_of_lt_of_le (Int.lt_floor_add_one z) hk1r
      linarith
    have hz : (k : ℝ) - z = ((k : ℝ) - (⌊z⌋ : ℝ)) - Int.fract z := by
      rw [← Int.self_sub_floor z]
      ring
    rw [abs_sub_comm, abs_of_nonneg hnonneg, hz]
    have h1 : 1 - Int.fract z ≤ ((k : ℝ) - (⌊z⌋ : ℝ)) - Int.fract z := by
      have hkdiff : 1 ≤ (k : ℝ) - (⌊z⌋ : ℝ) := by linarith
      linarith [Int.fract_lt_one z]
    exact le_trans (min_le_right _ _) h1

/-- Distance modulo 1 is bounded by the difference of fractional parts:
`‖a−b‖ ≤ |fract a − fract b|`, using the integer translate `⌊a⌋ − ⌊b⌋`. -/
theorem distToInt_le_fract (a b : ℝ) :
    distToInt (a - b) ≤ |Int.fract a - Int.fract b| := by
  have hsub : a - b - ((⌊a⌋ : ℝ) - (⌊b⌋ : ℝ)) = Int.fract a - Int.fract b := by
    rw [← Int.self_sub_floor a, ← Int.self_sub_floor b]
    ring
  have hd := distToInt_le_sub (a - b) (⌊a⌋ - ⌊b⌋)
  simpa [hsub] using hd

/-- Distance modulo 1 is even: `‖−w‖ = ‖w‖`. -/
theorem distToInt_neg (w : ℝ) : distToInt (-w) = distToInt w := by
  unfold distToInt
  by_cases hw : Int.fract w = 0
  · rw [Int.fract_neg_eq_zero.mpr hw, hw]
  · rw [Int.fract_neg hw, sub_sub_cancel, min_comm]

/-- Symmetry of distance modulo 1: `‖a−b‖ = ‖b−a‖`. -/
theorem distToInt_sub_comm (a b : ℝ) : distToInt (a - b) = distToInt (b - a) := by
  simpa only [neg_sub] using distToInt_neg (b - a)

/-- `distToInt z = 0` if and only if `z ∈ ℤ`. -/
theorem distToInt_eq_zero_iff (z : ℝ) : distToInt z = 0 ↔ ∃ k : ℤ, (k : ℝ) = z := by
  have hfract : distToInt z = 0 ↔ Int.fract z = 0 := by
    unfold distToInt
    rw [min_eq_iff]
    have hright : 0 < 1 - Int.fract z := sub_pos.mpr (Int.fract_lt_one z)
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · linarith
    · intro h
      exact Or.inl ⟨h, h.le.trans hright.le⟩
  exact hfract.trans Int.fract_eq_zero_iff

/-- Distinct points of a well-spaced set have real distance at least `δ`:
separation modulo 1 implies separation on the real line. -/
theorem wellSpacedReal_abs_le {X : Finset ℝ} {δ : ℝ} (hws : wellSpacedReal X δ)
    {x y : ℝ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) : δ ≤ |x - y| := by
  exact le_trans (hws hx hy hxy) (by simpa using distToInt_le_sub (x - y) 0)

/-! ## 2. Counting lemmas -/

/-- **Interval count**: a set in `[a, a+L]` with pairwise distances at
least `δ` has at most `L/δ + 1` points. Choose its largest point `m`;
the remaining points lie in `[a, m−δ]`, so induction applies. -/
theorem sepCard_le_interval (a L : ℝ) {δ : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (S : Finset ℝ)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ a + L)
    (hsep : ∀ ⦃x : ℝ⦄, x ∈ S → ∀ ⦃y : ℝ⦄, y ∈ S → x ≠ y → δ ≤ |x - y|) :
    (S.card : ℝ) ≤ L / δ + 1 := by
  have hmain : ∀ n : ℕ, ∀ S : Finset ℝ, S.card = n →
      ∀ L : ℝ, 0 ≤ L → (∀ x ∈ S, a ≤ x ∧ x ≤ a + L) →
      (∀ ⦃x : ℝ⦄, x ∈ S → ∀ ⦃y : ℝ⦄, y ∈ S → x ≠ y → δ ≤ |x - y|) →
      (S.card : ℝ) ≤ L / δ + 1 := by
    intro n
    induction n with
    | zero =>
        intro S hcard L' hL' hS' hsep'
        have h0 : (S.card : ℝ) = 0 := by simp [hcard]
        rw [h0]
        have h1 : 0 ≤ L' / δ := div_nonneg hL' (le_of_lt hδ)
        nlinarith
    | succ n ih =>
        intro S hcard L' hL' hS' hsep'
        have hne : S.Nonempty := Finset.card_pos.mp (by omega)
        let m : ℝ := S.max' hne
        let S' : Finset ℝ := S.erase m
        have hm : m ∈ S := S.max'_mem hne
        have hcard' : S'.card + 1 = S.card := by
          dsimp [S']
          exact Finset.card_erase_add_one hm
        have hcardS' : S'.card = n := by omega
        have hS'' : ∀ x ∈ S', a ≤ x ∧ x ≤ m - δ := by
          intro x hx
          have hxS : x ∈ S := (Finset.erase_subset m S) hx
          have hxm : x ≤ m := by
            dsimp [m]
            exact S.le_max' x hxS
          have hxne : x ≠ m := (Finset.mem_erase.mp hx).1
          have hδx : δ ≤ m - x := by
            simpa only [abs_of_nonneg (sub_nonneg.mpr hxm)] using hsep' hm hxS hxne.symm
          exact ⟨(hS' x hxS).1, by linarith⟩
        have hsep'' : ∀ ⦃x : ℝ⦄, x ∈ S' → ∀ ⦃y : ℝ⦄, y ∈ S' → x ≠ y → δ ≤ |x - y| := by
          intro x hx y hy hxy
          exact hsep' (Finset.erase_subset m S hx) (Finset.erase_subset m S hy) hxy
        by_cases hS'empty : S' = ∅
        · have hS'card0 : S'.card = 0 := by
            simpa using congrArg Finset.card hS'empty
          have hcardS : S.card = 1 := by omega
          have hc1 : (S.card : ℝ) = 1 := by exact_mod_cast hcardS
          rw [hc1]
          have h1 : 0 ≤ L' / δ := div_nonneg hL' (le_of_lt hδ)
          nlinarith
        · have hS'ne : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS'empty
          rcases hS'ne with ⟨w, hw⟩
          have hw1 : a ≤ w := (hS'' w hw).1
          have hw2 : w ≤ m - δ := (hS'' w hw).2
          have hL'' : 0 ≤ m - δ - a := by linarith
          have hIH := ih S' hcardS' (m - δ - a) hL''
            (by
              intro x hx
              have hx' := hS'' x hx
              exact ⟨hx'.1, by linarith [hx'.2]⟩) hsep''
          have hmle : m ≤ a + L' := (hS' m hm).2
          calc
            (S.card : ℝ) = (S'.card : ℝ) + 1 := by
              exact_mod_cast hcard'.symm
            _ ≤ ((m - δ - a) / δ + 1) + 1 := by linarith [hIH]
            _ = (m - a) / δ + 1 := by
              field_simp [hδ.ne']
              ring
            _ ≤ L' / δ + 1 := by
              have hma : m - a ≤ L' := by linarith
              have hd : (m - a) / δ ≤ L' / δ := div_le_div_of_nonneg_right hma (le_of_lt hδ)
              linarith
  exact hmain S.card S rfl L hL hS hsep

/-- Translation and reflection preserve the lower bound on distance modulo one. -/
private lemma distToInt_sub_le_fract_sub (x y z : ℝ) :
    distToInt (y - z) ≤ |Int.fract (x - y) - Int.fract (x - z)| := by
  have h := distToInt_le_fract (x - y) (x - z)
  rw [show (x - y) - (x - z) = -(y - z) by ring, distToInt_neg] at h
  exact h

/-- **Left-arc count**: at most `r/δ + 1` well-spaced points satisfy
`fract(x−y) ≤ r`. -/
theorem wellSpaced_fract_left_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((X.filter fun y => Int.fract (x - y) ≤ r).card : ℝ) ≤ r / δ + 1 := by
  let S : Finset ℝ := X.filter fun y => Int.fract (x - y) ≤ r
  let T : Finset ℝ := S.image fun y => Int.fract (x - y)
  have hcard : T.card = S.card := by
    dsimp [T]
    apply Finset.card_image_of_injOn
    intro y hy z hz hfz
    by_contra hyz
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    have hdiff : |Int.fract (x - y) - Int.fract (x - z)| = 0 := by
      have hfz' : Int.fract (x - y) = Int.fract (x - z) := by simpa using hfz
      rw [hfz']
      norm_num
    linarith
  have hT : ∀ t ∈ T, 0 ≤ t ∧ t ≤ r := by
    intro t ht
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    exact ⟨Int.fract_nonneg (x - y), (Finset.mem_filter.mp hy).2⟩
  have hTsep : ∀ ⦃t : ℝ⦄, t ∈ T → ∀ ⦃u : ℝ⦄, u ∈ T → t ≠ u → δ ≤ |t - u| := by
    intro t ht u hu htu
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    rcases (Finset.mem_image.mp hu) with ⟨z, hz, rfl⟩
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hyz : y ≠ z := by
      intro hyz
      apply htu
      congr
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    linarith
  have hcardT : (T.card : ℝ) ≤ r / δ + 1 :=
    sepCard_le_interval 0 r hδ hr T (by simpa using hT) hTsep
  change (S.card : ℝ) ≤ r / δ + 1
  rw [← hcard]
  exact hcardT

/-- **Right-arc count**: at most `r/δ + 1` well-spaced points satisfy
`1 − fract(x−y) ≤ r`. -/
theorem wellSpaced_fract_right_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ((X.filter fun y => 1 - Int.fract (x - y) ≤ r).card : ℝ) ≤ r / δ + 1 := by
  let S : Finset ℝ := X.filter fun y => 1 - Int.fract (x - y) ≤ r
  let T : Finset ℝ := S.image fun y => Int.fract (x - y)
  have hcard : T.card = S.card := by
    dsimp [T]
    apply Finset.card_image_of_injOn
    intro y hy z hz hfz
    by_contra hyz
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    have hdiff : |Int.fract (x - y) - Int.fract (x - z)| = 0 := by
      have hfz' : Int.fract (x - y) = Int.fract (x - z) := by simpa using hfz
      rw [hfz']
      norm_num
    linarith
  have hT : ∀ t ∈ T, 1 - r ≤ t ∧ t ≤ 1 := by
    intro t ht
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    have hyr : 1 - Int.fract (x - y) ≤ r := (Finset.mem_filter.mp hy).2
    exact ⟨by linarith, le_of_lt (Int.fract_lt_one (x - y))⟩
  have hTsep : ∀ ⦃t : ℝ⦄, t ∈ T → ∀ ⦃u : ℝ⦄, u ∈ T → t ≠ u → δ ≤ |t - u| := by
    intro t ht u hu htu
    rcases (Finset.mem_image.mp ht) with ⟨y, hy, rfl⟩
    rcases (Finset.mem_image.mp hu) with ⟨z, hz, rfl⟩
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
    have hyz : y ≠ z := by
      intro hyz
      apply htu
      congr
    have hδyz : δ ≤ distToInt (y - z) := hws hyX hzX hyz
    have hle := distToInt_sub_le_fract_sub x y z
    linarith
  have hcardT : (T.card : ℝ) ≤ r / δ + 1 :=
    sepCard_le_interval (1 - r) r hδ hr T (by simpa [sub_add_cancel] using hT) hTsep
  change (S.card : ℝ) ≤ r / δ + 1
  rw [← hcard]
  exact hcardT

/-- **Ball count modulo 1**: a ball of radius `r ≤ 1/2` contains at most
`2r/δ + 2` well-spaced points. Split fractional parts into left and
right intervals, each containing at most `r/δ + 1` points. -/
theorem wellSpaced_ball_card_le (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hws : wellSpacedReal X δ) (x : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (_hr1 : r ≤ 1 / 2) :
    ((X.filter fun y => distToInt (x - y) ≤ r).card : ℝ) ≤ 2 * r / δ + 2 := by
  let B : Finset ℝ := X.filter fun y => distToInt (x - y) ≤ r
  let L : Finset ℝ := X.filter fun y => Int.fract (x - y) ≤ r
  let R : Finset ℝ := X.filter fun y => 1 - Int.fract (x - y) ≤ r
  have hsub : B ⊆ L ∪ R := by
    intro y hy
    have hyX : y ∈ X := (Finset.mem_filter.mp hy).1
    have hyB : distToInt (x - y) ≤ r := (Finset.mem_filter.mp hy).2
    have hmin : min (Int.fract (x - y)) (1 - Int.fract (x - y)) ≤ r := by
      dsimp [distToInt] at hyB
      exact hyB
    rcases (min_le_iff.mp hmin) with hf | hf
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hyX, hf⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyX, hf⟩))
  have hB : B.card ≤ L.card + R.card := by
    have h1 : B.card ≤ (L ∪ R).card := Finset.card_le_card hsub
    exact le_trans h1 (Finset.card_union_le L R)
  have hL : (L.card : ℝ) ≤ r / δ + 1 := wellSpaced_fract_left_card_le X hδ hws x hr0
  have hR : (R.card : ℝ) ≤ r / δ + 1 := wellSpaced_fract_right_card_le X hδ hws x hr0
  calc
    (B.card : ℝ) ≤ (L.card : ℝ) + (R.card : ℝ) := by exact_mod_cast hB
    _ ≤ (r / δ + 1) + (r / δ + 1) := by linarith
    _ = 2 * r / δ + 2 := by ring

/-! ## 3. Interval-kernel properties and dyadic-shell row sums -/

/-- `e(0) = 1`. -/
theorem charReal_zero : charReal 0 = 1 := by
  dsimp [charReal]
  simp

/-- The interval exponential sum at zero: `Σ_{M<n≤M+N} e(n·0) = N`. -/
theorem charRealSubIcc_zero (M : ℤ) (N : ℕ) : charRealSubIcc M N 0 = (N : ℂ) := by
  simp [charRealSubIcc_eq_shift, charReal_zero]

/-- Conjugation of the interval kernel:
`Σ_n e(n·(−z)) = conj(Σ_n e(nz))`. -/
theorem charRealSubIcc_neg (M : ℤ) (N : ℕ) (z : ℝ) :
    charRealSubIcc M N (-z) = star (charRealSubIcc M N z) := by
  simp only [charRealSubIcc, mul_neg, charReal_neg, star_sum]

/-- Kernel norm symmetry:
`|Σ_n e(n(x−y))| = |Σ_n e(n(y−x))|`. -/
theorem charRealSubIcc_norm_sym (M : ℤ) (N : ℕ) (x y : ℝ) :
    ‖charRealSubIcc M N (x - y)‖ = ‖charRealSubIcc M N (y - x)‖ := by
  rw [show y - x = -(x - y) from (neg_sub x y).symm, charRealSubIcc_neg, norm_star]

/-- Pointwise shell bound: if `0 < ρ ≤ 1/2` and `(1/2)^J < ρ`, then
`1/(2ρ) ≤ Σ_{2≤j≤J} 2^{j-1}·1_{ρ ≤ (1/2)^{j-1}}`.
Choose the least `k` with `(1/2)^k < ρ`. Then `2 ≤ k ≤ J`,
`1/(2ρ) < 2^{k-1}`, and every shell index `j ∈ [2,k]` contributes. -/
theorem shell_geom_bound {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2) {J : ℕ}
    (hJ : (1 / 2 : ℝ) ^ J < ρ) :
    1 / (2 * ρ) ≤
      ∑ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
  let p : ℕ → Prop := fun j => (1 / 2 : ℝ) ^ j < ρ
  have hp : ∃ j, p j := ⟨J, hJ⟩
  let k : ℕ := Nat.find hp
  have hk : p k := Nat.find_spec hp
  have hkmin : ∀ j < k, ¬p j := by
    intro j hj hj'
    have hle : Nat.find hp ≤ j := Nat.find_min' hp hj'
    omega
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with hk0 | hk1
    · have : (1 : ℝ) < ρ := by simpa [p, hk0] using hk
      linarith
    · have : (1 / 2 : ℝ) < ρ := by simpa [p, hk1] using hk
      linarith
  have hkJ : k ≤ J := by
    by_contra h
    have hJk : J < k := lt_of_not_ge h
    have hnp : ¬p J := hkmin J hJk
    exact hnp hJ
  have hρk : (1 / 2 : ℝ) ^ k < ρ := hk
  have h2ρ : (1 / 2 : ℝ) ^ (k - 1) < 2 * ρ := by
    have hmul : 2 * ((1 / 2 : ℝ) ^ k) < 2 * ρ := by
      exact mul_lt_mul_of_pos_left hρk (by norm_num : 0 < (2 : ℝ))
    have hred : 2 * ((1 / 2 : ℝ) ^ k) = (1 / 2 : ℝ) ^ (k - 1) := by
      have hkform : k = (k - 1) + 1 := by omega
      nth_rewrite 1 [hkform]
      rw [pow_succ']
      ring_nf
    rwa [hred] at hmul
  have hbound : 1 / (2 * ρ) < (2 : ℝ) ^ (k - 1) := by
    have hpos1 : 0 < (1 / 2 : ℝ) ^ (k - 1) := pow_pos (by norm_num) (k - 1)
    have hpos2 : 0 < 2 * ρ := by nlinarith [hρ0]
    have h1 : 1 / (2 * ρ) < 1 / ((1 / 2 : ℝ) ^ (k - 1)) :=
      one_div_lt_one_div_of_lt hpos1 h2ρ
    have h2 : 1 / ((1 / 2 : ℝ) ^ (k - 1)) = (2 : ℝ) ^ (k - 1) := by
      rw [one_div_pow]
      field_simp
    simpa [h2] using h1
  have hind : ∀ j ∈ Finset.Icc 2 k, ρ ≤ (1 / 2 : ℝ) ^ (j - 1) := by
    intro j hj
    have hj' : 2 ≤ j ∧ j ≤ k := Finset.mem_Icc.mp hj
    have hj1 : j - 1 < k := by omega
    have hnp : ¬p (j - 1) := hkmin (j - 1) hj1
    dsimp [p] at hnp
    exact le_of_not_gt hnp
  have hcong : (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1)) =
      ∑ j ∈ Finset.Icc 2 k,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (hind j hj)]
    ring
  have hsub : Finset.Icc 2 k ⊆ Finset.Icc 2 J := Finset.Icc_subset_Icc (by norm_num) hkJ
  have hnonneg : ∀ j ∈ Finset.Icc 2 J, j ∉ Finset.Icc 2 k →
      0 ≤ (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    intro j hj hjn
    by_cases hc : ρ ≤ (1 / 2 : ℝ) ^ (j - 1)
    · rw [if_pos hc]
      positivity
    · rw [if_neg hc]
      positivity
  have hsum_low : (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1)) ≤
      ∑ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
    calc
      (∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1))
          = ∑ j ∈ Finset.Icc 2 k,
              (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := hcong
      _ ≤ ∑ j ∈ Finset.Icc 2 J,
              (2 : ℝ) ^ (j - 1) * if ρ ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hlast : (2 : ℝ) ^ (k - 1) ≤ ∑ j ∈ Finset.Icc 2 k, (2 : ℝ) ^ (j - 1) := by
    have hnon : ∀ j ∈ Finset.Icc 2 k, 0 ≤ (2 : ℝ) ^ (j - 1) := by
      intro j hj
      positivity
    have hk2mem : k ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨hk2, le_rfl⟩
    exact Finset.single_le_sum hnon hk2mem
  exact le_of_lt (lt_of_lt_of_le hbound (le_trans hlast hsum_low))

/-- `(1/2)^m · 2^m = 1`. -/
theorem half_pow_mul_two_pow (m : ℕ) : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
  rw [one_div_pow]
  exact div_mul_cancel₀ (1 : ℝ) (pow_ne_zero m (by norm_num))

/-- `(1/2)^m ≤ 1/2` for `1 ≤ m`. -/
theorem half_pow_le_half {m : ℕ} (hm : 1 ≤ m) : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
  rw [one_div_pow]
  have h2m : 2 ≤ (2 : ℝ) ^ m := by
    have hpow1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa using hpow1
  have hpos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  exact one_div_le_one_div_of_le (by norm_num : 0 < (2 : ℝ)) h2m

/-! ### 3½. The weaker constant and log₂ lemmas -/

/-- **Weaker additive large-sieve constant**:
`C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`, with a natural-number ceiling.
This is explicit; the logarithmic factor is the cost of naive
dyadic-shell counting and the Schur test. The sharp `N + 1/δ`
requires a positive-kernel argument not supplied here. -/
noncomputable def largeSieveBound (N : ℕ) (δ : ℝ) : ℝ :=
  (N : ℝ) + (2 * (Nat.ceil (Real.log (1 / δ) / Real.log 2) : ℝ) + 12) / δ

theorem largeSieveBound_nonneg (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ largeSieveBound N δ := by
  unfold largeSieveBound
  positivity

/-- `K := ⌈log₂(1/δ)⌉` satisfies `(1/2)^{K+1} < δ` for `0 < δ ≤ 1`. -/
theorem log2_ceil_half_lt {δ : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) :
    (1 / 2 : ℝ) ^ (Nat.ceil (Real.log (1 / δ) / Real.log 2) + 1) < δ := by
  -- Compare logarithms; the extra step above the ceiling makes the bound strict.
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : Real.log (1 / δ) / Real.log 2 <
      (Nat.ceil (Real.log (1 / δ) / Real.log 2) : ℝ) + 1 := by
    have hle := Nat.le_ceil (Real.log (1 / δ) / Real.log 2)
    linarith
  have hlog := (div_lt_iff₀ hlog2).mp hceil
  apply (Real.log_lt_log_iff (pow_pos (by norm_num) _) hδ).mp
  rw [Real.log_pow]
  simp only [Nat.cast_add, Nat.cast_one, one_div, Real.log_inv] at hlog ⊢
  nlinarith

/-- `K := ⌈log₂(1/δ)⌉` satisfies `2^K < 2/δ` for `0 < δ ≤ 1`. -/
theorem log2_ceil_two_pow_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ Nat.ceil (Real.log (1 / δ) / Real.log 2) < 2 / δ := by
  let a : ℝ := Real.log (1 / δ) / Real.log 2
  let K : ℕ := Nat.ceil a
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have h1d : 1 ≤ 1 / δ := one_le_one_div hδ hδ1
    have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h1d
    exact div_nonneg hlog (le_of_lt hlog2pos)
  have hK : (K : ℝ) < a + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one ha0
  have hmono : (2 : ℝ) ^ (K : ℝ) < (2 : ℝ) ^ (a + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hK
  have hmono' : (2 : ℝ) ^ K < (2 : ℝ) ^ (a + 1) := by
    simpa [Real.rpow_natCast] using hmono
  have h2a : (2 : ℝ) ^ a = 1 / δ := by
    dsimp [a]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    have harg : Real.log 2 * (Real.log (1 / δ) / Real.log 2) = Real.log (1 / δ) := by
      field_simp [hlog2pos.ne']
    have hpos : 0 < 1 / δ := by positivity
    calc
      Real.exp (Real.log 2 * (Real.log (1 / δ) / Real.log 2))
          = Real.exp (Real.log (1 / δ)) := by rw [harg]
      _ = 1 / δ := Real.exp_log hpos
  have h2 : (2 : ℝ) ^ (a + 1) = 2 / δ := by
    calc
      (2 : ℝ) ^ (a + 1) = (2 : ℝ) ^ a * (2 : ℝ) ^ 1 := Real.rpow_add (by norm_num) a 1
      _ = (1 / δ) * 2 := by
        rw [h2a]
        norm_num
      _ = 2 / δ := by ring
  exact lt_of_lt_of_eq hmono' h2

/-- **Dyadic-shell row sum (weaker constant)**: for a `δ`-well-spaced
set `X` modulo 1 and fixed `x ∈ X`,
`Σ_{y∈X} |Σ_{M<n≤M+N} e(n(x−y))| ≤ N + (2K+12)/δ`,
where `K = ⌈log₂(1/δ)⌉`. The logarithmic factor is the cost of
the naive Schur test. -/
theorem wellSpacedRowSum (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ)
    (hws : wellSpacedReal X δ) (x : ℝ) (hx : x ∈ X) :
    (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖) ≤ largeSieveBound N δ := by
  by_cases hδhalf : δ ≤ 1 / 2
  · let K : ℕ := Nat.ceil (Real.log (1 / δ) / Real.log 2)
    let J : ℕ := K + 1
    have hδle1 : δ ≤ 1 := le_trans hδhalf (by norm_num)
    have hJδ : (1 / 2 : ℝ) ^ J < δ := by
      dsimp [J, K]
      exact log2_ceil_half_lt hδ hδle1
    have hsplit : (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖) =
        (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
      calc
        (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖)
            = ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ + ‖charRealSubIcc M N (x - x)‖ := by
              exact (Finset.sum_erase_add X (fun y => ‖charRealSubIcc M N (x - y)‖) hx).symm
        _ = ‖charRealSubIcc M N (x - x)‖ + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
              rw [add_comm]
        _ = (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := by
              have hz : charRealSubIcc M N 0 = (N : ℂ) := charRealSubIcc_zero M N
              rw [show x - x = 0 by ring, hz]
              norm_num
    have hfar : (∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖) ≤
        ∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)) := by
      apply Finset.sum_le_sum
      intro y hy
      have hyX : y ∈ X := (Finset.erase_subset x X) hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hδy0 : δ ≤ distToInt (y - x) := hws hyX hx hyx
      have hδy : δ ≤ distToInt (x - y) := by
        rwa [distToInt_sub_comm y x] at hδy0
      have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = x - y := by
        intro hk
        have h0 : distToInt (x - y) = 0 := (distToInt_eq_zero_iff (x - y)).mpr hk
        linarith
      exact (geomSum_exp_bound_Icc M N (x - y)).2 hnotint
    have hpt : ∀ y ∈ X.erase x,
        1 / (2 * distToInt (x - y)) ≤
          ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
            if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
      intro y hy
      have hyX : y ∈ X := (Finset.erase_subset x X) hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      have hδy0 : δ ≤ distToInt (y - x) := hws hyX hx hyx
      have hδy : δ ≤ distToInt (x - y) := by
        rwa [distToInt_sub_comm y x] at hδy0
      have hρ0 : 0 < distToInt (x - y) := lt_of_lt_of_le hδ hδy
      have hρ : distToInt (x - y) ≤ 1 / 2 := distToInt_le_half (x - y)
      have hJρ : (1 / 2 : ℝ) ^ J < distToInt (x - y) := lt_of_lt_of_le hJδ hδy
      exact shell_geom_bound hρ0 hρ hJρ
    have hshell : (∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y))) ≤
        ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
          ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
      calc
        (∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)))
            ≤ ∑ y ∈ X.erase x,
                ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
                  if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
                  exact Finset.sum_le_sum hpt
        _ = ∑ j ∈ Finset.Icc 2 J,
                ∑ y ∈ X.erase x, (2 : ℝ) ^ (j - 1) *
                  if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0 := by
                  rw [Finset.sum_comm]
        _ ≤ ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
              ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
              apply Finset.sum_le_sum
              intro j hj
              have hle : (∑ y ∈ X.erase x, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) ≤
                  (∑ y ∈ X, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) := by
                exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset x X)
                  (by intro y hy hyneg; positivity)
              have hb : (∑ y ∈ X, (2 : ℝ) ^ (j - 1) *
                    if distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1) then (1 : ℝ) else 0) =
                  (2 : ℝ) ^ (j - 1) *
                    ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) := by
                rw [← Finset.mul_sum]
                congr 1
                exact Finset.sum_boole (fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)) X
              rw [← hb]
              exact hle
    have hballs : ∀ j ∈ Finset.Icc 2 J,
        ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ) ≤
          2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2 := by
      intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjm1 : 1 ≤ j - 1 := by omega
      have hjr : (1 / 2 : ℝ) ^ (j - 1) ≤ 1 / 2 := half_pow_le_half hjm1
      have hjr0 : 0 ≤ (1 / 2 : ℝ) ^ (j - 1) := by positivity
      exact wellSpaced_ball_card_le X hδ hws x hjr0 hjr
    have hshell2 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
          ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ)) ≤
        ∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hballs j hj) (pow_nonneg (by norm_num) (j - 1))
    have hterm : ∀ j ∈ Finset.Icc 2 J,
        (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2) =
          (2 : ℝ) / δ + (2 : ℝ) ^ j := by
      intro j hj
      have hcancel : (1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1) = 1 :=
        half_pow_mul_two_pow (j - 1)
      have h1 : (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ) = (2 : ℝ) / δ := by
        calc
          (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ)
              = (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1)) / δ := by ring
          _ = 2 * ((1 / 2 : ℝ) ^ (j - 1) * (2 : ℝ) ^ (j - 1)) / δ := by ring
          _ = 2 / δ := by rw [hcancel]; ring
      have h2 : (2 : ℝ) ^ (j - 1) * 2 = (2 : ℝ) ^ j := by
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        have hjj : j - 1 + 1 = j := by omega
        nth_rewrite 2 [← hjj]
        rw [pow_succ]
      calc
        (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)
            = (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ) + (2 : ℝ) ^ (j - 1) * 2 := by ring
        _ = (2 : ℝ) / δ + (2 : ℝ) ^ j := by rw [h1, h2]
    have hshell3 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) =
        (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) := by
      have hcong : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) =
          ∑ j ∈ Finset.Icc 2 J, ((2 : ℝ) / δ + (2 : ℝ) ^ j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j hj
      rw [hcong, Finset.sum_add_distrib]
    have hcardJ : ((Finset.Icc 2 J).card : ℝ) ≤ (J : ℝ) + 1 := by
      have hsub : Finset.Icc 2 J ⊆ Finset.range (J + 1) := by
        intro j hj
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        exact Finset.mem_range.mpr (by omega)
      have hc : (Finset.Icc 2 J).card ≤ (Finset.range (J + 1)).card := Finset.card_le_card hsub
      have hcr : (Finset.range (J + 1)).card = J + 1 := by simp
      have hc' : (Finset.Icc 2 J).card ≤ J + 1 := by
        rw [hcr] at hc
        exact hc
      exact_mod_cast hc'
    have hsum2 : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) ≤ (2 * (K : ℝ) + 4) / δ := by
      have hsc : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) =
          (2 / δ) * ((Finset.Icc 2 J).card : ℝ) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
        ring
      rw [hsc]
      have hpos : 0 ≤ 2 / δ := by positivity
      have hm : (2 / δ) * ((Finset.Icc 2 J).card : ℝ) ≤ (2 / δ) * ((J : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hcardJ hpos
      have hcalc : (2 / δ) * ((J : ℝ) + 1) = (2 * (K : ℝ) + 4) / δ := by
        have hJ : (J : ℝ) = (K : ℝ) + 1 := by
          simp [J]
        rw [hJ]
        ring
      exact le_trans hm (le_of_eq hcalc)
    have hsumj : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
      have hsub : Finset.Icc 2 J ⊆ Finset.range (J + 1) := by
        intro j hj
        have hj' : 2 ≤ j ∧ j ≤ J := Finset.mem_Icc.mp hj
        exact Finset.mem_range.mpr (by omega)
      have hle : (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤
          ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj hjn => by positivity)
      have hgeom : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) = (2 : ℝ) ^ (J + 1) - 1 := by
        have hg := geom_sum_mul (2 : ℝ) (J + 1)
        have htwo : (2 : ℝ) - 1 = 1 := by norm_num
        rw [htwo] at hg
        simpa using hg
      calc
        (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j) ≤ ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := hle
        _ = (2 : ℝ) ^ (J + 1) - 1 := hgeom
        _ ≤ (2 : ℝ) ^ (J + 1) := by linarith
    have hpowK : (2 : ℝ) ^ (K + 2) ≤ 8 / δ := by
      have hK : (2 : ℝ) ^ K < 2 / δ := log2_ceil_two_pow_lt hδ hδle1
      calc
        (2 : ℝ) ^ (K + 2) = (2 : ℝ) ^ K * (2 : ℝ) ^ 2 := by
          rw [pow_add]
        _ ≤ (2 / δ) * 4 := by nlinarith [hK]
        _ = 8 / δ := by ring
    have hpowJ : (2 : ℝ) ^ (J + 1) ≤ 8 / δ := by
      dsimp [J]
      simpa [Nat.add_assoc] using hpowK
    calc
      (∑ y ∈ X, ‖charRealSubIcc M N (x - y)‖)
          = (N : ℝ) + ∑ y ∈ X.erase x, ‖charRealSubIcc M N (x - y)‖ := hsplit
      _ ≤ (N : ℝ) + ∑ y ∈ X.erase x, 1 / (2 * distToInt (x - y)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hfar
      _ ≤ (N : ℝ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ (j - 1) *
            ((X.filter fun y => distToInt (x - y) ≤ (1 / 2 : ℝ) ^ (j - 1)).card : ℝ)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hshell
      _ ≤ (N : ℝ) + (∑ j ∈ Finset.Icc 2 J,
            (2 : ℝ) ^ (j - 1) * (2 * (1 / 2 : ℝ) ^ (j - 1) / δ + 2)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) hshell2
      _ = (N : ℝ) + ((∑ j ∈ Finset.Icc 2 J, (2 : ℝ) / δ) + (∑ j ∈ Finset.Icc 2 J, (2 : ℝ) ^ j)) := by
            rw [hshell3]
      _ ≤ (N : ℝ) + ((2 * (K : ℝ) + 4) / δ + (2 : ℝ) ^ (J + 1)) := by
            exact add_le_add (le_rfl : (N : ℝ) ≤ (N : ℝ)) (add_le_add hsum2 hsumj)
      _ ≤ (N : ℝ) + (2 * (K : ℝ) + 12) / δ := by
            have h1 : (2 * (K : ℝ) + 4) / δ + (2 : ℝ) ^ (J + 1) ≤ (2 * (K : ℝ) + 4) / δ + 8 / δ := by
              exact add_le_add (le_rfl : (2 * (K : ℝ) + 4) / δ ≤ (2 * (K : ℝ) + 4) / δ) hpowJ
            have h2 : (2 * (K : ℝ) + 4) / δ + 8 / δ = (2 * (K : ℝ) + 12) / δ := by ring
            linarith
      _ = largeSieveBound N δ := by
            dsimp [largeSieveBound, K]
  · -- Spacing greater than one half forces X to consist of the selected point.
    have hX : X = {x} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx, ?_⟩
      intro y hy
      by_contra hyx
      have hsep := hws hy hx hyx
      have hhalf := distToInt_le_half (y - x)
      linarith
    have hbound : (N : ℝ) ≤ largeSieveBound N δ := by
      unfold largeSieveBound
      exact le_add_of_nonneg_right (by positivity)
    simpa [hX, charRealSubIcc_zero] using hbound

/-! ## 4. The Schur test and the additive large sieve -/

/-- **Schur/Cauchy--Schwarz test**: if the kernel has symmetric norms
(`|K xy| = |K yx|`, as for a Hermitian kernel) and row sums at most `C`,
then `|Σ_x Σ_y b_x·conj(b_y)·K_xy| ≤ C·Σ_x |b_x|²`.
Use the triangle inequality and Cauchy--Schwarz for the complex
bilinear form on the product Finset. -/
theorem quadraticFormBound {ι : Type*} (s : Finset ι) (K : ι → ι → ℂ) (b : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C)
    (hsym : ∀ x ∈ s, ∀ y ∈ s, ‖K x y‖ = ‖K y x‖)
    (hrow : ∀ x ∈ s, (∑ y ∈ s, ‖K x y‖) ≤ C) :
    ‖(∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y : ℂ)‖ ≤ C * ∑ x ∈ s, ‖b x‖ ^ 2 := by
  let u : ι × ι → ℝ := fun p => ‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)
  let v : ι × ι → ℝ := fun p => ‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)
  have htri : ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖ ≤
      ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := by
    calc
      ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖
          ≤ ∑ x ∈ s, ‖∑ y ∈ s, b x * star (b y) * K x y‖ :=
            norm_sum_le s (fun x => ∑ y ∈ s, b x * star (b y) * K x y)
      _ ≤ ∑ x ∈ s, ∑ y ∈ s, ‖b x * star (b y) * K x y‖ := by
            apply Finset.sum_le_sum
            intro x hx
            exact norm_sum_le s (fun y => b x * star (b y) * K x y)
      _ = ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [norm_mul, norm_mul, norm_star]
  have hsumU : (∑ p ∈ s ×ˢ s, u p ^ 2) ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
    calc
      (∑ p ∈ s ×ˢ s, (‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)) ^ 2)
          = ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ ^ 2 * ‖K x y‖ := by
            rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ = ∑ x ∈ s, ‖b x‖ ^ 2 * (∑ y ∈ s, ‖K x y‖) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ s, ‖b x‖ ^ 2 * C := by
            apply Finset.sum_le_sum
            intro x hx
            exact mul_le_mul_of_nonneg_left (hrow x hx) (sq_nonneg _)
      _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hsumV : (∑ p ∈ s ×ˢ s, v p ^ 2) ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
    calc
      (∑ p ∈ s ×ˢ s, (‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)) ^ 2)
          = ∑ x ∈ s, ∑ y ∈ s, ‖b y‖ ^ 2 * ‖K x y‖ := by
            rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ = ∑ y ∈ s, ‖b y‖ ^ 2 * (∑ x ∈ s, ‖K x y‖) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ s, ‖b y‖ ^ 2 * C := by
            apply Finset.sum_le_sum
            intro y hy
            have hxy : (∑ x ∈ s, ‖K x y‖) = ∑ x ∈ s, ‖K y x‖ := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hsym x hx y hy
            have hle : (∑ x ∈ s, ‖K y x‖) ≤ C := hrow y hy
            rw [hxy]
            exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hcs : (∑ p ∈ s ×ˢ s, u p * v p) ≤
      Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ s) u v
  have htri2 : ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖ ≤
      ∑ p ∈ s ×ˢ s, u p * v p := by
    calc
      ‖∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y‖
          ≤ ∑ x ∈ s, ∑ y ∈ s, ‖b x‖ * ‖b y‖ * ‖K x y‖ := htri
      _ = ∑ p ∈ s ×ˢ s, ‖b p.1‖ * ‖b p.2‖ * ‖K p.1 p.2‖ := by
            rw [Finset.sum_product]
      _ = ∑ p ∈ s ×ˢ s, u p * v p := by
            apply Finset.sum_congr rfl
            intro p hp
            dsimp [u, v]
            have hsq : Real.sqrt (‖K p.1 p.2‖) * Real.sqrt (‖K p.1 p.2‖) = ‖K p.1 p.2‖ := by
              rw [← pow_two, Real.sq_sqrt (norm_nonneg _)]
            calc
              ‖b p.1‖ * ‖b p.2‖ * ‖K p.1 p.2‖
                  = (‖b p.1‖ * Real.sqrt (‖K p.1 p.2‖)) *
                      (‖b p.2‖ * Real.sqrt (‖K p.1 p.2‖)) := by
                    conv_lhs =>
                      rw [hsq.symm]
                    ring
              _ = u p * v p := rfl
  have hS : 0 ≤ ∑ x ∈ s, ‖b x‖ ^ 2 := Finset.sum_nonneg (fun x hx => sq_nonneg _)
  have hCS : 0 ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := mul_nonneg hC hS
  calc
    ‖(∑ x ∈ s, ∑ y ∈ s, b x * star (b y) * K x y : ℂ)‖
        ≤ ∑ p ∈ s ×ˢ s, u p * v p := htri2
    _ ≤ Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) := hcs
    _ ≤ C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
          have hU : Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) ≤
              Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
            (Real.sqrt_le_sqrt_iff hCS).2 hsumU
          have hV : Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2) ≤
              Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
            (Real.sqrt_le_sqrt_iff hCS).2 hsumV
          calc
            Real.sqrt (∑ p ∈ s ×ˢ s, u p ^ 2) * Real.sqrt (∑ p ∈ s ×ˢ s, v p ^ 2)
                ≤ Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) * Real.sqrt (C * ∑ x ∈ s, ‖b x‖ ^ 2) :=
                  mul_le_mul hU hV (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            _ = C * (∑ x ∈ s, ‖b x‖ ^ 2) := by
                  rw [← pow_two, Real.sq_sqrt hCS]

/-- **Dual additive large sieve (real version, weaker constant)**:
for a `δ`-well-spaced set `X` modulo 1,
`Σ_{M<n≤M+N} |Σ_{x∈X} conj(e(nx))·b_x|² ≤ C(N,δ)·Σ_{x∈X} |b_x|²`. -/
theorem largeSieveDual_wellSpaced (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hws : wellSpacedReal X δ) (b : ℝ → ℂ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2)
      ≤ largeSieveBound N δ * (∑ x ∈ X, ‖b x‖ ^ 2) := by
  let S : ℝ := ∑ n ∈ Finset.Icc (M + 1) (M + N),
    ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hnorm : S = ‖(S : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hS]
  have hdq := dualQuadraticIdentity_Icc M N X b
  have hinner : ∀ x y : ℝ,
      (∑ n ∈ Finset.Icc (M + 1) (M + N), star (charReal ((n : ℝ) * (x - y)))) =
        star (charRealSubIcc M N (x - y)) := by
    intro x y
    have hm1 := star_sum (s := Finset.Icc (M + 1) (M + N))
      (fun n : ℤ => charReal ((n : ℝ) * (x - y)))
    exact hm1.symm
  have hqb := quadraticFormBound X (fun x y => star (charRealSubIcc M N (x - y))) b
    (largeSieveBound_nonneg N hδ)
    (by
      intro x hx y hy
      rw [norm_star, norm_star, charRealSubIcc_norm_sym])
    (by
      intro x hx
      simpa [norm_star] using wellSpacedRowSum M N hδ X hws x hx)
  have hchain : (↑(∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charReal ((n : ℝ) * x)) * b x‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ X, ∑ y ∈ X, b x * star (b y) * star (charRealSubIcc M N (x - y)) := by
    rw [hdq]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [hinner x y]
  calc
    S = ‖(S : ℂ)‖ := hnorm
    _ = ‖(∑ x ∈ X, ∑ y ∈ X, b x * star (b y) * star (charRealSubIcc M N (x - y)) : ℂ)‖ := by
          rw [hchain]
    _ ≤ largeSieveBound N δ * (∑ x ∈ X, ‖b x‖ ^ 2) := hqb

/-- **Additive large sieve (real version, weaker constant)**:
for a `δ`-well-spaced set `X` modulo 1 and any finitely supported
complex sequence `a`, the primal bound is
`Σ_{x∈X} |Σ_{M<n≤M+N} a_n·e(nx)|² ≤ C(N,δ)·Σ_n |a_n|²`.
It follows from the dual bound by `largeSieveDuality`. -/
theorem largeSievePrimal_wellSpaced (M : ℤ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hws : wellSpacedReal X δ) (a : ℤ → ℂ) :
    (∑ x ∈ X, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2)
      ≤ largeSieveBound N δ * (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := by
  have hdual := largeSieveDual_wellSpaced M N hδ X hws
  exact (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
    (A := fun x n => (charReal ((n : ℝ) * x) : ℂ)) (largeSieveBound_nonneg N hδ)).2 hdual a
