import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWGCD

/-!
# Exact five-gcd reindexing of the retained W sum

All finite supports, signed coefficients, and frequencies are preserved.
The large-factor contribution is split off explicitly, not declared negligible.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev WOriginalTuple := (ℕ × ℕ) × (ℕ × ℕ)

def WGCDData.original (v : WGCDData) : WOriginalTuple :=
  ((v.δ * v.δ₁ * v.k₁, v.δ * v.δ₂ * v.k₂),
    (v.d * v.d₁ * v.n₁, v.d * v.n₂))

def wGCDTuple (t : WOriginalTuple) : WGCDData :=
  wGCDData t.1.1 t.1.2 t.2.1 t.2.2

theorem WGCDData.Valid.original_eq {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) : v.original = ((q, r), (N₁, N₂)) := by
  simp only [WGCDData.original, ← hv.q_eq, ← hv.r_eq, ← hv.N₁_eq, ← hv.N₂_eq]

theorem wGCDTuple_original {t : WOriginalTuple}
    (ht : 0 < t.1.1 ∧ 0 < t.1.2 ∧ 0 < t.2.1 ∧ 0 < t.2.2) :
    (wGCDTuple t).original = t :=
  (wGCDData_valid ht.1 ht.2.1 ht.2.2.1 ht.2.2.2).original_eq

def wOriginalTuples (N Q : Finset ℕ) (a : ℤ) : Finset WOriginalTuple :=
  ((reducedModuli Q a ×ˢ reducedModuli Q a) ×ˢ (N ×ˢ N)).filter
    (fun t ↦ WCompatible t.1.1 t.1.2 t.2.1 t.2.2)

def wGCDTuples (N Q : Finset ℕ) (a : ℤ) : Finset WGCDData :=
  (wOriginalTuples N Q a).image wGCDTuple

theorem wOriginalTuples_pos {N Q : Finset ℕ} {a : ℤ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {t : WOriginalTuple} (ht : t ∈ wOriginalTuples N Q a) :
    0 < t.1.1 ∧ 0 < t.1.2 ∧ 0 < t.2.1 ∧ 0 < t.2.2 := by
  have hp := (Finset.mem_filter.mp ht).1
  simp only [Finset.mem_product] at hp
  obtain ⟨⟨hq, hr⟩, hn₁, hn₂⟩ := hp
  exact ⟨hQ _ (Finset.mem_filter.mp hq).1, hQ _ (Finset.mem_filter.mp hr).1,
    hN _ hn₁, hN _ hn₂⟩

theorem wGCDTuple_injOn {N Q : Finset ℕ} {a : ℤ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q) :
    Set.InjOn wGCDTuple (wOriginalTuples N Q a) := by
  intro t ht u hu he
  have h := congrArg WGCDData.original he
  simpa only [wGCDTuple_original (wOriginalTuples_pos hN hQ ht),
    wGCDTuple_original (wOriginalTuples_pos hN hQ hu)] using h


/-- An exact change of variables for arbitrary additive weights. -/
theorem sum_wGCDTuples {A : Type*} [AddCommMonoid A]
    {N Q : Finset ℕ} {a : ℤ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (f : WGCDData → A) :
    (∑ v ∈ wGCDTuples N Q a, f v) =
      ∑ t ∈ wOriginalTuples N Q a, f (wGCDTuple t) := by
  exact Finset.sum_image (wGCDTuple_injOn hN hQ)

def wOriginalTerm (M : ℝ) (H : ℕ → ℕ → ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (t : WOriginalTuple) : ℝ :=
  (c t.1.1 * c t.1.2 * β t.2.1 * β t.2.2) *
    (∑ h ∈ Finset.Icc (-(H t.1.1 t.1.2 : ℤ)) (H t.1.1 t.1.2),
      wPoissonFrequency M a t.1.1 t.1.2 t.2.1 t.2.2 h).re

theorem truncatedWNonzeroMode_eq_originalTuples
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    truncatedWNonzeroMode M H N Q β c a =
      ∑ t ∈ wOriginalTuples N Q a, wOriginalTerm M H β c a t := by
  simp only [wOriginalTuples, Finset.sum_filter, Finset.sum_product,
    truncatedWNonzeroMode, wOriginalTerm]

def wGCDTerm (M : ℝ) (H : ℕ → ℕ → ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (v : WGCDData) : ℝ :=
  let t := v.original
  (c t.1.1 * c t.1.2 * β t.2.1 * β t.2.2) *
    (∑ h ∈ Finset.Icc (-(H t.1.1 t.1.2 : ℤ)) (H t.1.1 t.1.2),
      wThreeFactorPoissonFrequency M a t.1.1 t.1.2
        v.d v.d₁ v.D v.k₁ v.k₂ v.n₁ v.n₂ h).re

theorem wGCDTerm_eq_originalTerm {t : WOriginalTuple}
    (ht : 0 < t.1.1 ∧ 0 < t.1.2 ∧ 0 < t.2.1 ∧ 0 < t.2.2)
    (hc : WCompatible t.1.1 t.1.2 t.2.1 t.2.2)
    (M : ℝ) (H : ℕ → ℕ → ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    wGCDTerm M H β c a (wGCDTuple t) = wOriginalTerm M H β c a t := by
  unfold wGCDTerm
  rw [wGCDTuple_original ht]
  unfold wOriginalTerm
  dsimp only
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  exact (wPoissonFrequency_eq_canonical_threeFactor ht.1 ht.2.1 ht.2.2.1
    ht.2.2.2 hc M a h).symm

/-- The actual signed finite W remainder, now in canonical coordinates.
No coprimality or factorization hypotheses are supplied by the caller. -/
theorem truncatedWNonzeroMode_eq_gcdTuples
    (M : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q) :
    truncatedWNonzeroMode M H N Q β c a =
      ∑ v ∈ wGCDTuples N Q a, wGCDTerm M H β c a v := by
  rw [sum_wGCDTuples hN hQ, truncatedWNonzeroMode_eq_originalTuples]
  apply Finset.sum_congr rfl
  intro t ht
  exact (wGCDTerm_eq_originalTerm (wOriginalTuples_pos hN hQ ht)
    (Finset.mem_filter.mp ht).2 M H β c a).symm

def WGCDData.key (v : WGCDData) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (v.d, v.d₁, v.δ, v.δ₁, v.δ₂)


def WGCDData.Small (v : WGCDData) (Y : ℝ) : Prop :=
  (v.d : ℝ) ≤ Y ∧ (v.d₁ : ℝ) ≤ Y ∧ (v.δ : ℝ) ≤ Y ∧
    (v.δ₁ : ℝ) ≤ Y ∧ (v.δ₂ : ℝ) ≤ Y

theorem WGCDData.Small.moduli {v : WGCDData} {Y : ℝ} (hY : 0 ≤ Y)
    (hv : v.Small Y) : (v.D : ℝ) ≤ Y ^ 3 ∧ (v.D' : ℝ) ≤ Y ^ 5 :=
  WGCDData.Valid.small_moduli hY hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2

def wGCDSmallSum (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) : ℝ := by
  classical
  exact ∑ v ∈ (wGCDTuples N Q a).filter (fun v ↦ v.Small Y), wGCDTerm M H β c a v

def wGCDLargeSum (M Y : ℝ) (H : ℕ → ℕ → ℕ) (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) : ℝ := by
  classical
  exact ∑ v ∈ (wGCDTuples N Q a).filter (fun v ↦ ¬v.Small Y), wGCDTerm M H β c a v


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
