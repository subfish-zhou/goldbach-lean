import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryExtractedKeyBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWSmallRoot

/-!
# The actual extracted exponential kernel in source phase coordinates

Fouvry (1987), pp. 627--628, (3.11)--(3.13). The negative Fourier
phase is `-u*h/lcm`; `a` occurs in the CRT phase, not a second time in
this Fourier phase. All arithmetic coefficients and carrier restrictions
remain outside the smooth weight.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wReciprocalPhase (v : WGCDData) (a : ℤ) : UnitAddCircle :=
  (((a : ℝ) * ((v.d₁ : ℝ) * v.n₁ - v.n₂) *
    wPhaseInverse (v.D' * v.n₂ * v.k₁) (v.n₁ * v.k₂) /
    ((v.n₁ : ℝ) * v.k₂) : ℝ) : UnitAddCircle)

/-- The reciprocal amplitude and both genuinely smooth phases. -/
def wAnalyticWeight (D D' : ℕ) (a : ℤ) (u h k n r s : ℝ) : ℂ :=
  (((D : ℝ) * k * r * s)⁻¹ : ℂ) *
    (Real.fourierChar
      (h * (-u / ((D : ℝ) * k * r * s) +
        (a : ℝ) / (n * k * r * s * D'))) : ℂ)

theorem fourier_real_eq_fourierChar (h : ℤ) (v : ℝ) :
    fourier h (v : UnitAddCircle) = (Real.fourierChar ((h : ℝ) * v) : ℂ) := by
  rw [fourier_coe_apply, Real.fourierChar_apply]
  push_cast
  congr 1
  ring

private theorem fourier_add_phase (h : ℤ) (v w : UnitAddCircle) :
    fourier h (v + w) = fourier h v * fourier h w := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Pointwise transport uses the already constructed three-phase identity.
No coprimality or residue phase is replaced by a bound. -/
theorem wFourierExponential_eq_analyticWeight
    {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) (hc : WCompatible q r N₁ N₂)
    (a h : ℤ) (u : ℝ) :
    wFourierExponential a q r N₁ N₂ h u =
      wAnalyticWeight v.D v.D' a u h v.k₁ v.n₁ v.k₂ 1 *
        fourier h (wSmallRootPhase v.d v.d₁ v.δ v.δ₁ v.δ₂
          v.k₁ v.k₂ v.n₁ v.n₂ a) *
        fourier h (wReciprocalPhase v a) := by
  unfold wFourierExponential
  rw [productCRTResidue_phase_smallRoot hv hc a, fourier_add_phase, fourier_add_phase,
    fourier_real_eq_fourierChar]
  unfold wAnalyticWeight wReciprocalPhase
  rw [hv.lcm_eq]
  push_cast
  simp only [mul_one]
  rw [mul_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  have he : - (u * ((h : ℝ) / ((v.D : ℝ) * v.k₁ * v.k₂))) =
      (h : ℝ) * (-u / ((v.D : ℝ) * v.k₁ * v.k₂)) := by ring
  rw [he]
  ring

/-- The arithmetic and positivity facts are derived from actual membership. -/
theorem wExtractedOriginal_valid {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {z : WExtractedTuple} (hz : z ∈ wFactorExtractionTuples N Q a P R S ξ) :
    (wGCDTuple (wExtractedOriginal z)).Valid
      (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2
      (wExtractedOriginal z).2.1 (wExtractedOriginal z).2.2 ∧
    WCompatible (wExtractedOriginal z).1.1 (wExtractedOriginal z).1.2
      (wExtractedOriginal z).2.1 (wExtractedOriginal z).2.2 := by
  obtain ⟨_, _, _, _, _, _, hq, hn₁, hn₂, hr, hc, _⟩ :=
    mem_wFactorExtractionTuples_iff.mp hz
  exact ⟨wGCDData_valid (hQ _ (mem_filter.mp hq).1)
    (hQ _ (mem_filter.mp hr).1) (hN _ hn₁) (hN _ hn₂), hc⟩

/-- The second free canonical modulus is exactly `r'*s'`, not merely a
divisor or a factorization supplied by a caller. -/
theorem wExtracted_k₂_eq {N Q : Finset ℕ} {a : ℤ}
    {P : WOriginalTuple → Prop} {R S ξ : ℝ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {z : WExtractedTuple} (hz : z ∈ wFactorExtractionTuples N Q a P R S ξ) :
    (wGCDTuple (wExtractedOriginal z)).k₂ = z.1.2.1 * z.1.2.2 := by
  obtain ⟨hv, _⟩ := wExtractedOriginal_valid hN hQ hz
  obtain ⟨_, _, he, _⟩ := wExtracted_extraction_spec hz
  apply Nat.mul_left_cancel (Nat.mul_pos hv.δ_pos hv.δ₂_pos)
  rw [← hv.r_eq, ← he]
  dsimp [wExtractedOriginal]
  ring

def wExtractedArithmeticPhase (a h : ℤ) (z : WExtractedTuple) : ℂ :=
  let v := wGCDTuple (wExtractedOriginal z)
  fourier h (wSmallRootPhase v.d v.d₁ v.δ v.δ₁ v.δ₂
    v.k₁ v.k₂ v.n₁ v.n₂ a) * fourier h (wReciprocalPhase v a)

theorem norm_wExtractedArithmeticPhase (a h : ℤ) (z : WExtractedTuple) :
    ‖wExtractedArithmeticPhase a h z‖ = 1 := by
  simp only [wExtractedArithmeticPhase, norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The fixed-key sum now has only a five-variable analytic weight.
The original cutoff, low-omega tests, compatibility, and signed coefficients
are still exactly those of `wExtractedKeyFiber`. -/
theorem wExtractedKeyExponential_eq_analyticWeight
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (H : ℕ → ℕ → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) (u : ℝ) :
    wExtractedKeyExponential H N Q β c₁ γ ζ a P R S ξ b K u =
      ∑ t ∈ wExtractedKeyFiber H N Q a P R S ξ b K,
        let v := wGCDTuple (wExtractedOriginal t.1)
        (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
          wExtractedArithmeticPhase a t.2 t.1 *
          wAnalyticWeight v.D v.D' a u t.2 v.k₁ v.n₁ t.1.1.2.1 t.1.1.2.2 := by
  unfold wExtractedKeyExponential wFourierExponentialSum
  apply sum_congr rfl
  intro t ht
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp ht).1).1).1
  obtain ⟨hv, hc⟩ := wExtractedOriginal_valid hN hQ hz
  rw [wFourierExponential_eq_analyticWeight hv hc]
  dsimp only
  unfold wExtractedArithmeticPhase
  have he := wExtracted_k₂_eq hN hQ hz
  have hw : wAnalyticWeight (wGCDTuple (wExtractedOriginal t.1)).D
      (wGCDTuple (wExtractedOriginal t.1)).D' a u t.2
      (wGCDTuple (wExtractedOriginal t.1)).k₁
      (wGCDTuple (wExtractedOriginal t.1)).n₁
      (wGCDTuple (wExtractedOriginal t.1)).k₂ 1 =
    wAnalyticWeight (wGCDTuple (wExtractedOriginal t.1)).D
      (wGCDTuple (wExtractedOriginal t.1)).D' a u t.2
      (wGCDTuple (wExtractedOriginal t.1)).k₁
      (wGCDTuple (wExtractedOriginal t.1)).n₁ t.1.1.2.1 t.1.1.2.2 := by
    rw [he]
    simp only [wAnalyticWeight, Nat.cast_mul, Complex.ofReal_mul,
      Complex.ofReal_one, mul_one, mul_assoc]
  rw [hw]
  ring

/-- A selected value may be zero. Only the other branch provides an actual
member and hence positive canonical parameters. -/
theorem wExtractedKeyExponential_zero_or_witness
    (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c₁ γ ζ : ℕ → ℝ)
    (a : ℤ) (P : WOriginalTuple → Prop) (R S ξ : ℝ)
    (b : ℕ) (K : WExtractedKey) (u : ℝ) :
    wExtractedKeyExponential H N Q β c₁ γ ζ a P R S ξ b K u = 0 ∨
      ∃ t ∈ wExtractedKeyFiber H N Q a P R S ξ b K,
        wExtractedCoefficient β c₁ γ ζ t.1 ≠ 0 := by
  by_cases he : wExtractedKeyExponential H N Q β c₁ γ ζ a P R S ξ b K u = 0
  · exact Or.inl he
  · right
    by_contra hn
    push Not at hn
    apply he
    unfold wExtractedKeyExponential wFourierExponentialSum
    exact sum_eq_zero (fun t ht => by dsimp only; rw [hn t ht]; simp)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
