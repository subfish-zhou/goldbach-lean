import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedPhase

/-!
# Actual phase scales and nonempty-key guards

The source slow phase is estimated using the original beta coordinate
`N₁ = d*d₁*n₁`, not the reduced coordinate `n₁`. In particular
`|a| <= 4*M*T` and `N₁ >= T` give `|a|/N₁ <= 4*M`, uniformly in `a`.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def WExtractedKey.D (K : WExtractedKey) : ℕ :=
  K.1.2.2.1 * K.1.2.2.2.1 * K.1.2.2.2.2

def WExtractedKey.D' (K : WExtractedKey) : ℕ :=
  K.1.1 * K.1.2.1 * K.D

theorem wExtractedKeyFiber_moduli {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    (wGCDTuple (wExtractedOriginal t.1)).D = K.D ∧
      (wGCDTuple (wExtractedOriginal t.1)).D' = K.D' := by
  have hk := (wExtractedKeyFiber_spec ht).1
  constructor
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ =>
      v.2.2.1 * v.2.2.2.1 * v.2.2.2.2) hk
  · exact congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ =>
      v.1 * v.2.1 * (v.2.2.1 * v.2.2.2.1 * v.2.2.2.2)) hk

/-- Positivity follows from a real member; no positivity is inferred from
membership of the enclosing key box. -/
theorem wExtractedKeyFiber_positive {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wExtractedKeyFiber H N Q a P R S ξ b K) :
    0 < K.D ∧ 0 < K.D' ∧ 0 < K.2 ∧ 0 < t.1.1.1.2 ∧
      0 < (wGCDTuple (wExtractedOriginal t.1)).k₁ ∧
      0 < (wGCDTuple (wExtractedOriginal t.1)).n₁ ∧
      0 < t.1.1.2.1 ∧ 0 < t.1.1.2.2 ∧ t.2 ≠ 0 := by
  have hb := (mem_wExtractedKeyFiber_iff.mp ht).1
  have hz := (mem_wExtractedFrequencies_iff.mp (mem_filter.mp hb).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have he := wExtractedKeyFiber_moduli ht
  have hs := wExtractedKeyFiber_spec ht
  have hmem := mem_wFactorExtractionTuples_iff.mp hz
  exact ⟨he.1 ▸ hv.D_pos, he.2 ▸ hv.D'_pos, hs.2.2.1, hs.2.2.2.1,
    hv.k₁_pos, hv.n₁_pos, (mem_Ioc.mp hmem.2.2.1).1,
    (mem_Ioc.mp hmem.2.2.2.1).1, (mem_filter.mp hb).2.1⟩

/-- The constants of the analytic weight are genuinely fixed on a key. -/
theorem wExtractedKeyExponential_eq_fixedWeight
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (H : ℕ → ℕ → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) (u : ℝ) :
    wExtractedKeyExponential H N Q β c₁ γ ζ a P R S ξ b K u =
      ∑ t ∈ wExtractedKeyFiber H N Q a P R S ξ b K,
        let v := wGCDTuple (wExtractedOriginal t.1)
        (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
          wExtractedArithmeticPhase a t.2 t.1 *
          wAnalyticWeight K.D K.D' a u t.2 v.k₁ v.n₁ t.1.1.2.1 t.1.1.2.2 := by
  rw [wExtractedKeyExponential_eq_analyticWeight hN hQ]
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [(wExtractedKeyFiber_moduli ht).1, (wExtractedKeyFiber_moduli ht).2]

theorem WGCDData.Valid.slow_denominator {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) :
    v.n₁ * v.k₁ * v.k₂ * v.D' = N₁ * q.lcm r := by
  rw [hv.N₁_eq, hv.lcm_eq]
  unfold WGCDData.D'
  ring

/-- A scale bound for the two smooth phase monomials, retaining the
original beta support and the uniform large-residue range. -/
theorem wAnalytic_phase_budget
    {v : WGCDData} {q r N₁ N₂ : ℕ} (hv : v.Valid q r N₁ N₂)
    {M T x u : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hNT : T ≤ (N₁ : ℝ)) (hx : x = 4 * M * T) {a : ℤ}
    (ha : |(a : ℝ)| ≤ x) (hu : |u| ≤ 3 * M) (h : ℤ) :
    |(h : ℝ)| * (|u| / (v.D * v.k₁ * v.k₂ : ℕ) +
      |(a : ℝ)| / (v.n₁ * v.k₁ * v.k₂ * v.D' : ℕ)) ≤
        7 * M * |(h : ℝ)| / (q.lcm r : ℝ) := by
  have hN₁ : (0 : ℝ) < N₁ := hT.trans_le hNT
  have hl : (0 : ℝ) < q.lcm r := by
    rw [hv.lcm_eq]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hv.D_pos hv.k₁_pos) hv.k₂_pos
  have ha' : |(a : ℝ)| ≤ 4 * M * (N₁ : ℝ) :=
    ha.trans (hx ▸ mul_le_mul_of_nonneg_left hNT (by positivity))
  rw [hv.slow_denominator, ← hv.lcm_eq, Nat.cast_mul]
  have hb : |(a : ℝ)| / ((N₁ : ℝ) * (q.lcm r : ℝ)) ≤
      4 * M / (q.lcm r : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hN₁ hl) hl).mpr
    nlinarith [mul_le_mul_of_nonneg_right ha' hl.le]
  have hb' := add_le_add (div_le_div_of_nonneg_right hu hl.le) hb
  calc
    _ ≤ |(h : ℝ)| * (3 * M / (q.lcm r : ℝ) + 4 * M / (q.lcm r : ℝ)) :=
      mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    _ = _ := by ring

/-- The actual ceiling cutoff only supplies `Z + M/lcm`. This explicitly
records the boundary-frequency issue before any small-power variation claim. -/
theorem wUniformCutoff_phase_scale_le {M Z : ℝ} (hM : 0 < M) (hZ : 0 ≤ Z)
    {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) {h : ℤ}
    (hh : h.natAbs ≤ wUniformCutoff M Z q r) :
    M * |(h : ℝ)| / (q.lcm r : ℝ) ≤ Z + M / (q.lcm r : ℝ) := by
  have hl : (0 : ℝ) < q.lcm r :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq hr))
  have hh' : |(h : ℝ)| ≤ (wUniformCutoff M Z q r : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using (Nat.cast_le (α := ℝ)).mpr hh
  have hceil : (wUniformCutoff M Z q r : ℝ) ≤ (q.lcm r : ℝ) / M * Z + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  calc
    _ ≤ M * ((q.lcm r : ℝ) / M * Z + 1) / (q.lcm r : ℝ) := by
      gcongr
      exact hh'.trans hceil
    _ = _ := by field_simp

/-- Positive dyadic reference scales enlarge the phase budget by at most
sixteen. The estimate is for the complete rectangle, not just its masked
arithmetic points. -/
theorem wAnalytic_reference_budget
    {D D' h k n r s H K N R S : ℝ}
    (hD : 0 < D) (hD' : 0 < D') (hk : 0 < k) (hn : 0 < n)
    (hr : 0 < r) (hs : 0 < s) (hK : 0 < K) (hN : 0 < N)
    (hR : 0 < R) (hS : 0 < S)
    (hH : 0 ≤ H) (hHh : H ≤ |h|)
    (hkK : k ≤ 2 * K) (hnN : n ≤ 2 * N)
    (hrR : r ≤ 2 * R) (hsS : s ≤ 2 * S) (u a : ℝ) :
    H * (|u| / (D * K * R * S) + |a| / (N * K * R * S * D')) ≤
      16 * (|h| * (|u| / (D * k * r * s) + |a| / (n * k * r * s * D'))) := by
  have hprod : D * k * r * s ≤ 16 * (D * K * R * S) := by
    calc
      _ ≤ D * (2 * K) * (2 * R) * (2 * S) := by gcongr
      _ ≤ _ := by nlinarith [show 0 ≤ D * K * R * S by positivity]
  have hprod' : n * k * r * s * D' ≤ 16 * (N * K * R * S * D') := by
    calc
      _ ≤ (2 * N) * (2 * K) * (2 * R) * (2 * S) * D' := by gcongr
      _ = _ := by ring
  have hu : |u| / (D * K * R * S) ≤ 16 * (|u| / (D * k * r * s)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg u)]
  have ha : |a| / (N * K * R * S * D') ≤ 16 * (|a| / (n * k * r * s * D')) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprod' (abs_nonneg a)]
  calc
    _ ≤ H * (16 * (|u| / (D * k * r * s)) +
      16 * (|a| / (n * k * r * s * D'))) :=
      mul_le_mul_of_nonneg_left (add_le_add hu ha) hH
    _ ≤ |h| * (16 * (|u| / (D * k * r * s)) +
      16 * (|a| / (n * k * r * s * D'))) :=
      mul_le_mul_of_nonneg_right hHh (by positivity)
    _ = _ := by ring

/-- Exact normalization of the concrete five-variable weight. The two
real parameters displayed here are the ones controlled by the reference
budget; no arithmetic coefficient is part of this function. -/
theorem wAnalyticWeight_normalize (D D' : ℕ) (a : ℤ)
    (u H K N R S : ℝ) (v : Fin 5 → ℝ) :
    wAnalyticWeight D D' a u (H * v 0) (K * v 1) (N * v 2)
        (R * v 3) (S * v 4) =
      (((D : ℝ) * K * R * S)⁻¹ : ℂ) *
        (((v 1 * v 3 * v 4)⁻¹ : ℝ) : ℂ) *
        (Real.fourierChar
          ((-H * u / ((D : ℝ) * K * R * S)) * v 0 / (v 1 * v 3 * v 4) +
            (H * (a : ℝ) / (N * K * R * S * D')) *
              v 0 / (v 1 * v 2 * v 3 * v 4)) : ℂ) := by
  unfold wAnalyticWeight
  have he : (D : ℝ) * (K * v 1) * (R * v 3) * (S * v 4) =
      ((D : ℝ) * K * R * S) * (v 1 * v 3 * v 4) := by ring
  have he' : (N * v 2) * (K * v 1) * (R * v 3) * (S * v 4) * D' =
      (N * K * R * S * D') * (v 1 * v 2 * v 3 * v 4) := by ring
  simp only [he, he', mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv,
    div_eq_mul_inv]
  congr 1
  · ring
  · congr 2
    ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
