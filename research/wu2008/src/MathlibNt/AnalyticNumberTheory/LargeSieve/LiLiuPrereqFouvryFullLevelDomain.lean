import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryFrequencyBlocks

/-!
# The genuine full-level modulus carrier

Only the complete positive interval is used here. No arbitrary membership
mask is absorbed into a well-factorable coefficient. The inner factor has
an exact floor interval and explicitly retained arithmetic restrictions;
the filtered fiber is not asserted to be an unweighted interval.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem mem_reducedModuli_fullLevel_iff (L : ℝ) (a : ℤ) (q : ℕ) :
    q ∈ reducedModuli (Ioc 0 ⌊L⌋₊) a ↔
      q ∈ Ioc 0 ⌊L⌋₊ ∧ a.natAbs.Coprime q := by
  rw [reducedModuli, Finset.mem_filter]
  simp only [Int.gcd_def, Int.natAbs_natCast,
    Nat.coprime_iff_gcd_eq_one]


theorem supported_product_mem_fullLevel {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    {r s : ℕ} (hr : r ∈ Ioc 0 ⌊R⌋₊) (hs : s ∈ Ioc 0 ⌊S⌋₊) :
    r * s ∈ Ioc 0 ⌊R * S⌋₊ := by
  obtain ⟨hr0, hrR⟩ := mem_Ioc.mp hr
  obtain ⟨hs0, hsS⟩ := mem_Ioc.mp hs
  refine mem_Ioc.mpr ⟨Nat.mul_pos hr0 hs0, Nat.le_floor ?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul
    ((Nat.cast_le.mpr hrR).trans (Nat.floor_le hR))
    ((Nat.cast_le.mpr hsS).trans (Nat.floor_le hS)) (Nat.cast_nonneg _) hR

theorem supported_product_reduced_fullLevel_iff {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S) {r s : ℕ}
    (hr : r ∈ Ioc 0 ⌊R⌋₊) (hs : s ∈ Ioc 0 ⌊S⌋₊) (a : ℤ) :
    r * s ∈ reducedModuli (Ioc 0 ⌊R * S⌋₊) a ↔
      a.natAbs.Coprime r ∧ a.natAbs.Coprime s := by
  rw [mem_reducedModuli_fullLevel_iff]
  simp only [supported_product_mem_fullLevel hR hS hr hs, true_and,
    Nat.coprime_mul_iff_right]

/-- The real interval for a positive varying factor. Both coordinate caps
in the broad extraction box are consequences of the product cap. -/
theorem positive_factor_box_iff {d k F : ℕ} (hd : 0 < d) (hk : 0 < k) :
    d ∈ Ioc 0 F ∧ k ∈ Ioc 0 F ∧ d * k ≤ F ↔ k ∈ Ioc 0 (F / d) := by
  simp only [mem_Ioc, hd, hk, true_and, Nat.le_div_iff_mul_le hd, mul_comm k d]
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨(Nat.le_mul_of_pos_right d hk).trans h,
      (Nat.le_mul_of_pos_left k hd).trans h, h⟩

/-- Residual restrictions on `r'` after the full modulus interval has been
resolved. They are not dropped when applying partial summation or Cauchy. -/
def wRPrimeResidual (a : ℤ) (P : WOriginalTuple → Prop)
    (Δ Δ' s' q₁ n₁ n₂ r' : ℕ) : Prop :=
  let q₂ := (Δ * r') * (Δ' * s')
  a.natAbs.Coprime r' ∧ n₂.Coprime r' ∧
    Nat.ModEq (q₁.gcd q₂) n₁ n₂ ∧
    P ((q₁, q₂), (n₁, n₂)) ∧
    wSecondExtractionDivisor ((q₁, q₂), (n₁, n₂)) = Δ * Δ'


/-- A nonzero retained frequency gives a strict lower endpoint. This
uses the ceiling convention in the actual `wUniformCutoff`, including
`|h| = 1`, for which the lower endpoint is zero. -/
theorem wUniformCutoff_frequency_iff {M Z : ℝ} (q r : ℕ)
    {h : ℤ} (hh : h ≠ 0) :
    h.natAbs ≤ wUniformCutoff M Z q r ↔
      ((h.natAbs - 1 : ℕ) : ℝ) < (q.lcm r : ℝ) / M * Z := by
  have hn : h.natAbs - 1 + 1 = h.natAbs := by
    have hp := Int.natAbs_ne_zero.mpr hh
    omega
  unfold wUniformCutoff
  conv_lhs => rw [← hn]
  exact Nat.add_one_le_ceil_iff

/-- On a fixed gcd fiber the original modulus-dependent cutoff is an
honest lower floor endpoint for the varying factor `k`. This is not an
enlargement to a common cutoff. -/
theorem wUniformCutoff_factor_interval_iff {M Z : ℝ} (hM : 0 < M) (hZ : 0 < Z)
    {q d k δ : ℕ} (hq : 0 < q) (hd : 0 < d) (hk : 0 < k)
    (hg : q.gcd (d * k) = δ) {h : ℤ} (hh : h ≠ 0) :
    h.natAbs ≤ wUniformCutoff M Z q (d * k) ↔
      ⌊((h.natAbs - 1 : ℕ) : ℝ) * M * δ / ((q : ℝ) * d * Z)⌋₊ < k := by
  have hδ : 0 < δ := hg ▸ Nat.gcd_pos_of_pos_left (d * k) hq
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hdr : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hδr : (0 : ℝ) < δ := Nat.cast_pos.mpr hδ
  have hl : (q.lcm (d * k) : ℝ) = (q : ℝ) * d * k / δ := by
    apply (eq_div_iff hδr.ne').mpr
    have he := Nat.gcd_mul_lcm q (d * k)
    rw [hg] at he
    have he' : (δ : ℝ) * (q.lcm (d * k) : ℝ) = (q : ℝ) * (d * k) := by
      exact_mod_cast he
    nlinarith
  rw [wUniformCutoff_frequency_iff q (d * k) hh, Nat.floor_lt' hk.ne', hl]
  rw [div_lt_iff₀ (by positivity : 0 < (q : ℝ) * d * Z)]
  rw [div_mul_eq_mul_div, lt_div_iff₀ hM, div_mul_eq_mul_div, lt_div_iff₀ hδr]
  constructor <;> intro he <;> nlinarith


theorem wExtractedOriginal_reducedModuli {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {z : WExtractedTuple}
    (hz : z ∈ wFactorExtractionTuples N Q a P R S ξ) :
    (wExtractedOriginal z).1.1 ∈ reducedModuli Q a ∧
      (wExtractedOriginal z).1.2 ∈ reducedModuli Q a := by
  have he := mem_wFactorExtractionTuples_iff.mp hz
  dsimp only [wExtractedOriginal]
  tauto

theorem wUniformCutoff_le_fullLevel {M Z L : ℝ}
    (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    {q r : ℕ} (hq : q ∈ Ioc 0 ⌊L⌋₊) (hr : r ∈ Ioc 0 ⌊L⌋₊) :
    wUniformCutoff M Z q r ≤ ⌈L ^ 2 / M * Z⌉₊ := by
  obtain ⟨hq0, hqL⟩ := mem_Ioc.mp hq
  obtain ⟨hr0, hrL⟩ := mem_Ioc.mp hr
  have hl : q.lcm r ≤ q * r := by
    calc
      q.lcm r ≤ q.gcd r * q.lcm r :=
        Nat.le_mul_of_pos_left _ (Nat.gcd_pos_of_pos_left r hq0)
      _ = q * r := Nat.gcd_mul_lcm q r
  have hqr : (q.lcm r : ℝ) ≤ L ^ 2 := by
    calc
      (q.lcm r : ℝ) ≤ (q * r : ℕ) := Nat.cast_le.mpr hl
      _ ≤ L * L := by
        rw [Nat.cast_mul]
        exact mul_le_mul
          ((Nat.cast_le.mpr hqL).trans (Nat.floor_le hL))
          ((Nat.cast_le.mpr hrL).trans (Nat.floor_le hL)) (Nat.cast_nonneg _) hL
      _ = L ^ 2 := (pow_two L).symm
  exact Nat.ceil_mono
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hqr hM.le) hZ)

/-- A scale-only dyadic count bound, uniform in the residue, the
coefficients, and every surviving arithmetic mask. -/
theorem wExtractedMaxFrequency_le_fullLevel {M Z L : ℝ}
    (hM : 0 < M) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (N : Finset ℕ) (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ) :
    wExtractedMaxFrequency (wUniformCutoff M Z) N (Ioc 0 ⌊L⌋₊) a P R S ξ ≤
      ⌈L ^ 2 / M * Z⌉₊ := by
  unfold wExtractedMaxFrequency
  apply Finset.sup_le
  intro z hz
  obtain ⟨hq, hr⟩ := wExtractedOriginal_reducedModuli hz
  exact wUniformCutoff_le_fullLevel hM hZ hL
    (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
