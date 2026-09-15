import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryActualCoprimePartition
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryReciprocalCorrelation

/-!
# IV.3 correlation on the actual extracted carrier

Fouvry (1987), p. 632, (4.7)--(4.8). Lemma 7 supplies the cross
coprimalities; the original tuple conditions supply all other inverses.
The two terms share `k₁`, `r'`, and `n₁`. The small-root factors are
retained, and no interval estimate is applied to an arbitrary masked sum.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The common modulus has only one copy of the shared `n₁`. -/
def wActualCorrelationModulus (t u : WExtractedTuple × ℤ) : ℕ :=
  (wGCDTuple (wExtractedOriginal t.1)).n₁ * t.1.1.2.1 *
    t.1.1.2.2 * u.1.1.2.2

def wActualCorrelationNumerator (K : WExtractedKey) (a : ℤ)
    (t u : WExtractedTuple × ℤ) : ℤ :=
  iv3CorrelationNumerator K.1.2.1 (wGCDTuple (wExtractedOriginal t.1)).n₁
    (wGCDTuple (wExtractedOriginal t.1)).n₂ (wGCDTuple (wExtractedOriginal u.1)).n₂
    t.1.1.2.2 u.1.1.2.2 a t.2 u.2

def wActualReciprocalCorrelation (K : WExtractedKey) (a : ℤ)
    (t u : WExtractedTuple × ℤ) : ℂ :=
  fourier 1 (iv3ReciprocalCircle (wActualCorrelationModulus t u)
    (K.D' * (wGCDTuple (wExtractedOriginal t.1)).n₂ *
      (wGCDTuple (wExtractedOriginal u.1)).n₂ *
      (wGCDTuple (wExtractedOriginal t.1)).k₁)
    (wActualCorrelationNumerator K a t u))

/-- Kept as a factor on each original tuple, with no residue-freezing claim. -/
def wActualSmallRootFactor (a : ℤ) (t : WExtractedTuple × ℤ) : ℂ :=
  let v := wGCDTuple (wExtractedOriginal t.1)
  fourier t.2 (wSmallRootPhase v.d v.d₁ v.δ v.δ₁ v.δ₂ v.k₁ v.k₂ v.n₁ v.n₂ a)

theorem norm_wActualReciprocalCorrelation (K : WExtractedKey) (a : ℤ)
    (t u : WExtractedTuple × ℤ) :
    ‖wActualReciprocalCorrelation K a t u‖ = 1 := by
  simp only [wActualReciprocalCorrelation, fourier_apply, Circle.norm_coe]

theorem norm_wActualSmallRootFactor (a : ℤ) (t : WExtractedTuple × ℤ) :
    ‖wActualSmallRootFactor a t‖ = 1 := by
  simp only [wActualSmallRootFactor, fourier_apply, Circle.norm_coe]

section Actual

variable {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
  (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
  {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
  {U : Finset (WExtractedTuple × ℤ)}
  (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
    R S (highOmegaCutoff x) b K)
  {c : Finset (ℕ × ℕ)} {t u : WExtractedTuple × ℤ}
  (ht : t ∈ wCoprimeFiber x N S U c) (hu : u ∈ wCoprimeFiber x N S U c)
  (hk : (wGCDTuple (wExtractedOriginal t.1)).k₁ =
    (wGCDTuple (wExtractedOriginal u.1)).k₁)
  (hr : t.1.1.2.1 = u.1.1.2.1)
  (hn : (wGCDTuple (wExtractedOriginal t.1)).n₁ =
    (wGCDTuple (wExtractedOriginal u.1)).n₁)

include hN hQ hU ht hu hk hr hn

/-- The common inverse in IV.3 is a consequence of actual membership,
not an extra coprimality premise. The two `s'` need not be coprime. -/
theorem wCoprimeFiber_common_inverse_coprime :
    (K.D' * (wGCDTuple (wExtractedOriginal t.1)).n₂ *
      (wGCDTuple (wExtractedOriginal u.1)).n₂ *
      (wGCDTuple (wExtractedOriginal t.1)).k₁).Coprime
    ((wGCDTuple (wExtractedOriginal t.1)).n₁ * t.1.1.2.1 *
      t.1.1.2.2 * u.1.1.2.2) := by
  have htf := hU (mem_filter.mp ht).1
  have huf := hU (mem_filter.mp hu).1
  have htz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp htf).1).1).1
  have huz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp huf).1).1).1
  obtain ⟨hvt, hct⟩ := wExtractedOriginal_valid hN hQ htz
  obtain ⟨hvu, hcu⟩ := wExtractedOriginal_valid hN hQ huz
  obtain ⟨hDt, hkt, hnt⟩ := hvt.phase_coprime hct
  obtain ⟨hDu, hku, hnu⟩ := hvu.phase_coprime hcu
  have hDt' := hDt.symm
  have hDu' := hDu.symm
  rw [wExtracted_k₂_eq hN hQ htz, (wExtractedKeyFiber_moduli htf).2] at hDt'
  rw [wExtracted_k₂_eq hN hQ huz, (wExtractedKeyFiber_moduli huf).2,
    ← hk, ← hr, ← hn] at hDu'
  rw [wExtracted_k₂_eq hN hQ htz] at hkt hnt
  rw [← hk] at hku
  rw [wExtracted_k₂_eq hN hQ huz, ← hr, ← hn] at hku hnu
  have hcross := wCoprimeFiber_cross_coprime hN hQ hU ht hu
  dsimp only [wCoprimePair] at hcross
  rw [← hn] at hcross
  simp only [Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
    at hDt' hDu' hkt hnt hku hnu hcross ⊢
  tauto

/-- Exact IV.3 phase transport, with both `D'` and `d₁` frozen by the key
and all positivity and common-inverse conditions derived from membership. -/
theorem wCoprimeFiber_reciprocal_correlation :
    fourier t.2 (wReciprocalPhase (wGCDTuple (wExtractedOriginal t.1)) a) *
      star (fourier u.2 (wReciprocalPhase (wGCDTuple (wExtractedOriginal u.1)) a)) =
      wActualReciprocalCorrelation K a t u := by
  have htf := hU (mem_filter.mp ht).1
  have huf := hU (mem_filter.mp hu).1
  have htz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp htf).1).1).1
  have huz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp huf).1).1).1
  have hdt : (wGCDTuple (wExtractedOriginal t.1)).d₁ = K.1.2.1 :=
    congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) (wExtractedKeyFiber_spec htf).1
  have hdu : (wGCDTuple (wExtractedOriginal u.1)).d₁ = K.1.2.1 :=
    congrArg (fun v : ℕ × ℕ × ℕ × ℕ × ℕ => v.2.1) (wExtractedKeyFiber_spec huf).1
  have htp := wExtractedKeyFiber_positive hN hQ htf
  have hup := wExtractedKeyFiber_positive hN hQ huf
  rw [wReciprocalPhase_eq_iv3 (wExtracted_k₂_eq hN hQ htz),
    wReciprocalPhase_eq_iv3 (wExtracted_k₂_eq hN hQ huz),
    (wExtractedKeyFiber_moduli htf).2, (wExtractedKeyFiber_moduli huf).2,
    hdt, hdu, ← hk, ← hr, ← hn]
  exact iv3_reciprocal_correlation htp.2.2.2.2.2.1 htp.2.2.2.2.2.2.1
    htp.2.2.2.2.2.2.2.1 hup.2.2.2.2.2.2.2.1
    (wCoprimeFiber_common_inverse_coprime hN hQ hU ht hu hk hr hn) a t.2 u.2

/-- The complete arithmetic product retains the possibly varying
small-root product. Arbitrary signs of `a`, `h`, and `h'` are allowed. -/
theorem wCoprimeFiber_arithmetic_correlation :
    wExtractedArithmeticPhase a t.2 t.1 * star (wExtractedArithmeticPhase a u.2 u.1) =
      (wActualSmallRootFactor a t * star (wActualSmallRootFactor a u)) *
        wActualReciprocalCorrelation K a t u := by
  have he := wCoprimeFiber_reciprocal_correlation hN hQ hU ht hu hk hr hn
  rw [← he]
  simp only [wExtractedArithmeticPhase, wActualSmallRootFactor, star_mul]
  ring

/-- Zero numerator kills the reciprocal factor, not the small-root product. -/
theorem wCoprimeFiber_arithmetic_correlation_zero
    (hl : wActualCorrelationNumerator K a t u = 0) :
    wExtractedArithmeticPhase a t.2 t.1 * star (wExtractedArithmeticPhase a u.2 u.1) =
      wActualSmallRootFactor a t * star (wActualSmallRootFactor a u) := by
  rw [wCoprimeFiber_arithmetic_correlation hN hQ hU ht hu hk hr hn]
  simp [wActualReciprocalCorrelation, hl, iv3ReciprocalCircle]

end Actual

/-- These are precisely the coordinates shared in an IV.3 Cauchy pair. -/
def wCorrelationOuter (t : WExtractedTuple × ℤ) : ℕ × ℕ × ℕ :=
  ((wGCDTuple (wExtractedOriginal t.1)).k₁, t.1.1.2.1,
    (wGCDTuple (wExtractedOriginal t.1)).n₁)

def wCorrelationOuterFiber (x : ℝ) (N : Finset ℕ) (S : ℝ)
    (U : Finset (WExtractedTuple × ℤ)) (c : Finset (ℕ × ℕ)) (o : ℕ × ℕ × ℕ) :
    Finset (WExtractedTuple × ℤ) :=
  (wCoprimeFiber x N S U c).filter (fun t => wCorrelationOuter t = o)

/-- Only the outer labels are imaged; the inner sum still runs over
original tuples. Repeated arithmetic coordinates keep their multiplicity. -/
theorem sum_wCorrelationOuterFibers {A : Type*} [AddCommMonoid A]
    (x : ℝ) (N : Finset ℕ) (S : ℝ) (U : Finset (WExtractedTuple × ℤ))
    (c : Finset (ℕ × ℕ)) (F : WExtractedTuple × ℤ → A) :
    ∑ t ∈ wCoprimeFiber x N S U c, F t =
      ∑ o ∈ (wCoprimeFiber x N S U c).image wCorrelationOuter,
        ∑ t ∈ wCorrelationOuterFiber x N S U c o, F t := by
  exact (sum_fiberwise_of_maps_to
    (fun t ht => mem_image.mpr ⟨t, ht, rfl⟩) F).symm

section Gram

variable {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
  (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
  {a : ℤ} {x η R S : ℝ} {b : ℕ} {K : WExtractedKey}
  {U : Finset (WExtractedTuple × ℤ)}
  (hU : U ⊆ wExtractedKeyFiber H N Q a (c2FiveSmallMask x η)
    R S (highOmegaCutoff x) b K)

include hN hQ hU

/-- Exact finite Gram expansion on one actual outer-coordinate fiber.
`A` may contain arbitrary complex weights and additional masks. No
small-root phase has been discarded, and no positivity of `A` is used. -/
theorem wCorrelationOuterFiber_gram (c : Finset (ℕ × ℕ)) (o : ℕ × ℕ × ℕ)
    (A : WExtractedTuple × ℤ → ℂ) :
    ((‖∑ t ∈ wCorrelationOuterFiber x N S U c o,
      A t * wExtractedArithmeticPhase a t.2 t.1‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ wCorrelationOuterFiber x N S U c o,
        ∑ u ∈ wCorrelationOuterFiber x N S U c o,
          (A t * star (A u)) *
            (wActualSmallRootFactor a t * star (wActualSmallRootFactor a u)) *
            wActualReciprocalCorrelation K a t u := by
  push_cast
  rw [← Complex.mul_conj', map_sum, sum_mul_sum]
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro u hu
  obtain ⟨ht, hto⟩ := mem_filter.mp ht
  obtain ⟨hu, huo⟩ := mem_filter.mp hu
  have ho : wCorrelationOuter t = wCorrelationOuter u := hto.trans huo.symm
  have hk := congrArg Prod.fst ho
  have hr := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) ho
  have hn := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) ho
  change (A t * wExtractedArithmeticPhase a t.2 t.1) *
    star (A u * wExtractedArithmeticPhase a u.2 u.1) = _
  rw [star_mul]
  calc
    _ = (A t * star (A u)) *
        (wExtractedArithmeticPhase a t.2 t.1 *
          star (wExtractedArithmeticPhase a u.2 u.1)) := by ring
    _ = _ := by
      rw [wCoprimeFiber_arithmetic_correlation hN hQ hU ht hu hk hr hn]
      ring

/-- The finite Cauchy step followed by the exact IV.3 Gram expansion.
The outer cost counts occupied triples, not original tuple multiplicities.
The right side is an exact nonnegative Gram quantity; its summands need
not be nonnegative, and no unweighted interval bound is asserted. -/
theorem wCoprimeFiber_cauchy_correlation (c : Finset (ℕ × ℕ))
    (A : WExtractedTuple × ℤ → ℂ) :
    ‖∑ t ∈ wCoprimeFiber x N S U c, A t * wExtractedArithmeticPhase a t.2 t.1‖ ^ 2 ≤
      (((wCoprimeFiber x N S U c).image wCorrelationOuter).card : ℝ) *
        ∑ o ∈ (wCoprimeFiber x N S U c).image wCorrelationOuter,
          (∑ t ∈ wCorrelationOuterFiber x N S U c o,
            ∑ u ∈ wCorrelationOuterFiber x N S U c o,
              (A t * star (A u)) *
                (wActualSmallRootFactor a t * star (wActualSmallRootFactor a u)) *
                wActualReciprocalCorrelation K a t u).re := by
  let O := (wCoprimeFiber x N S U c).image wCorrelationOuter
  let B : ℕ × ℕ × ℕ → ℂ := fun o =>
    ∑ t ∈ wCorrelationOuterFiber x N S U c o,
      A t * wExtractedArithmeticPhase a t.2 t.1
  rw [sum_wCorrelationOuterFibers x N S U c]
  change ‖∑ o ∈ O, B o‖ ^ 2 ≤ _
  calc
    _ ≤ (∑ o ∈ O, ‖B o‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (O.card : ℝ) * ∑ o ∈ O, ‖B o‖ ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq O (fun _ => (1 : ℝ)) (fun o => ‖B o‖)
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro o _
      exact congrArg Complex.re (wCorrelationOuterFiber_gram hN hQ hU c o A)

end Gram

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
