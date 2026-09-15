import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryPrimeSupport
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWPhaseThreeFactor

/-!
# The canonical five-gcd coordinates of W

Fouvry (1984), pp. 235--237, before any large-factor terms are discarded.
The five outer coordinates are `d,d₁,δ,δ₁,δ₂`. The four remaining coordinates
recover the original moduli and beta indices exactly.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

@[ext] structure WGCDData where
  d : ℕ
  d₁ : ℕ
  δ : ℕ
  δ₁ : ℕ
  δ₂ : ℕ
  k₁ : ℕ
  k₂ : ℕ
  n₁ : ℕ
  n₂ : ℕ
  deriving DecidableEq

def wGCDData (q r N₁ N₂ : ℕ) : WGCDData :=
  let d := N₁.gcd N₂
  let δ := q.gcd r
  { d := d, d₁ := supportedPart (N₁ / d) d
    δ := δ, δ₁ := supportedPart (q / δ) δ, δ₂ := supportedPart (r / δ) δ
    k₁ := coprimePart (q / δ) δ, k₂ := coprimePart (r / δ) δ
    n₁ := coprimePart (N₁ / d) d, n₂ := N₂ / d }

def WGCDData.D (v : WGCDData) : ℕ := v.δ * v.δ₁ * v.δ₂

def WGCDData.D' (v : WGCDData) : ℕ := v.d * v.d₁ * v.D

/-- Arithmetic facts, not distribution or phase estimates. -/
structure WGCDData.Valid (v : WGCDData) (q r N₁ N₂ : ℕ) : Prop where
  d_pos : 0 < v.d
  d₁_pos : 0 < v.d₁
  δ_pos : 0 < v.δ
  δ₁_pos : 0 < v.δ₁
  δ₂_pos : 0 < v.δ₂
  k₁_pos : 0 < v.k₁
  k₂_pos : 0 < v.k₂
  n₁_pos : 0 < v.n₁
  n₂_pos : 0 < v.n₂
  q_eq : q = v.δ * v.δ₁ * v.k₁
  r_eq : r = v.δ * v.δ₂ * v.k₂
  N₁_eq : N₁ = v.d * v.d₁ * v.n₁
  N₂_eq : N₂ = v.d * v.n₂
  d_eq : v.d = N₁.gcd N₂
  δ_eq : v.δ = q.gcd r
  d₁_support : ∀ p : ℕ, p.Prime → p ∣ v.d₁ → p ∣ v.d
  δ₁_support : ∀ p : ℕ, p.Prime → p ∣ v.δ₁ → p ∣ v.δ
  δ₂_support : ∀ p : ℕ, p.Prime → p ∣ v.δ₂ → p ∣ v.δ
  n₁_d : v.n₁.Coprime v.d
  k₁_δ : v.k₁.Coprime v.δ
  k₂_δ : v.k₂.Coprime v.δ
  n_primitive : (v.d₁ * v.n₁).Coprime v.n₂
  k_primitive : (v.δ₁ * v.k₁).Coprime (v.δ₂ * v.k₂)

private theorem gcd_quotients_coprime {u v : ℕ} (hu : 0 < u) :
    (u / u.gcd v).Coprime (v / u.gcd v) := by
  have hg := Nat.gcd_pos_of_pos_left v hu
  change (u / u.gcd v).gcd (v / u.gcd v) = 1
  apply Nat.mul_left_cancel hg
  rw [← Nat.gcd_mul_left, Nat.mul_div_cancel' (Nat.gcd_dvd_left u v),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right u v), mul_one]

/-- The data are constructed for every positive original tuple, with no
compatibility, size cutoff, or analytic premise. -/
theorem wGCDData_valid {q r N₁ N₂ : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    (wGCDData q r N₁ N₂).Valid q r N₁ N₂ := by
  have hd := Nat.gcd_pos_of_pos_left N₂ hN₁
  have hδ := Nat.gcd_pos_of_pos_left r hq
  have hu := Nat.div_pos (Nat.le_of_dvd hN₁ (Nat.gcd_dvd_left N₁ N₂)) hd
  have hv := Nat.div_pos (Nat.le_of_dvd hN₂ (Nat.gcd_dvd_right N₁ N₂)) hd
  have hk := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hδ
  have hl := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hδ
  refine ⟨hd, supportedPart_pos _ _, hδ, supportedPart_pos _ _,
    supportedPart_pos _ _, coprimePart_pos _ _, coprimePart_pos _ _,
    coprimePart_pos _ _, hv, ?_, ?_, ?_, ?_, rfl, rfl,
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    (fun _ hp hps ↦ prime_dvd_supportedPart hp hps),
    coprimePart_coprime _ _, coprimePart_coprime _ _, coprimePart_coprime _ _,
    ?_, ?_⟩
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hk,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)]
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hl,
      Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)]
  · dsimp [wGCDData]
    rw [mul_assoc, supportedPart_mul_coprimePart hu,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left N₁ N₂)]
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right N₁ N₂)).symm
  · dsimp [wGCDData]
    rw [supportedPart_mul_coprimePart hu]
    exact gcd_quotients_coprime hN₁
  · dsimp [wGCDData]
    rw [supportedPart_mul_coprimePart hk, supportedPart_mul_coprimePart hl]
    exact gcd_quotients_coprime hq

namespace WGCDData.Valid

variable {v : WGCDData} {q r N₁ N₂ : ℕ} (hv : v.Valid q r N₁ N₂)

include hv

theorem D_pos : 0 < v.D := Nat.mul_pos (Nat.mul_pos hv.δ_pos hv.δ₁_pos) hv.δ₂_pos

theorem D'_pos : 0 < v.D' := Nat.mul_pos (Nat.mul_pos hv.d_pos hv.d₁_pos) hv.D_pos

theorem k₁_dvd : v.k₁ ∣ q := by rw [hv.q_eq]; exact dvd_mul_left _ _

theorem k₂_dvd : v.k₂ ∣ r := by rw [hv.r_eq]; exact dvd_mul_left _ _

theorem k_coprime : v.k₁.Coprime v.k₂ :=
  hv.k_primitive.of_dvd (dvd_mul_left _ _) (dvd_mul_left _ _)

theorem δ_coprime : v.δ₁.Coprime v.δ₂ :=
  hv.k_primitive.of_dvd (dvd_mul_right _ _) (dvd_mul_right _ _)

theorem lcm_eq : q.lcm r = v.D * v.k₁ * v.k₂ := by
  apply Nat.mul_left_cancel hv.δ_pos
  calc
    v.δ * q.lcm r = q * r := by rw [hv.δ_eq, Nat.gcd_mul_lcm]
    _ = v.δ * (v.D * v.k₁ * v.k₂) := by rw [hv.q_eq, hv.r_eq]; unfold D; ring

theorem k_D : (v.k₁ * v.k₂).Coprime v.D := by
  have hkδ := hv.k₁_δ.mul_left hv.k₂_δ
  exact (hkδ.mul_right (coprime_of_prime_support hkδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hkδ hv.δ₂_support)

theorem n₁_d₁ : v.n₁.Coprime v.d₁ :=
  coprime_of_prime_support hv.n₁_d hv.d₁_support

theorem n₁_n₂ : v.n₁.Coprime v.n₂ :=
  hv.n_primitive.of_dvd_left (dvd_mul_left _ _)

omit hv in
private theorem quotient_of_product {s n t : ℕ} (hs : 0 < s) (he : n = s * t) :
    n / s = t := by
  apply Nat.mul_left_cancel hs
  rw [Nat.mul_div_cancel' ⟨t, he⟩]
  exact he

/-- Uniqueness of all nine coordinates, not merely a choice of a compatible
factorization. This permits exact finite reindexing without multiplicity. -/
theorem eq_canonical : v = wGCDData q r N₁ N₂ := by
  have hq : q / v.δ = v.δ₁ * v.k₁ :=
    quotient_of_product hv.δ_pos (by rw [hv.q_eq, mul_assoc])
  have hr : r / v.δ = v.δ₂ * v.k₂ :=
    quotient_of_product hv.δ_pos (by rw [hv.r_eq, mul_assoc])
  have hN₁ : N₁ / v.d = v.d₁ * v.n₁ :=
    quotient_of_product hv.d_pos (by rw [hv.N₁_eq, mul_assoc])
  have hN₂ : N₂ / v.d = v.n₂ := quotient_of_product hv.d_pos hv.N₂_eq
  have hs₁ := prime_support_split_unique
    (show 0 < N₁ / v.d by rw [hN₁]; exact Nat.mul_pos hv.d₁_pos hv.n₁_pos)
    hN₁.symm hv.d₁_support hv.n₁_d
  have hs₂ := prime_support_split_unique
    (show 0 < q / v.δ by rw [hq]; exact Nat.mul_pos hv.δ₁_pos hv.k₁_pos)
    hq.symm hv.δ₁_support hv.k₁_δ
  have hs₃ := prime_support_split_unique
    (show 0 < r / v.δ by rw [hr]; exact Nat.mul_pos hv.δ₂_pos hv.k₂_pos)
    hr.symm hv.δ₂_support hv.k₂_δ
  apply WGCDData.ext
  · exact hv.d_eq
  · simpa only [wGCDData, ← hv.d_eq] using hs₁.1
  · exact hv.δ_eq
  · simpa only [wGCDData, ← hv.δ_eq] using hs₂.1
  · simpa only [wGCDData, ← hv.δ_eq] using hs₃.1
  · simpa only [wGCDData, ← hv.δ_eq] using hs₂.2
  · simpa only [wGCDData, ← hv.δ_eq] using hs₃.2
  · simpa only [wGCDData, ← hv.d_eq] using hs₁.2
  · simpa only [wGCDData, ← hv.d_eq] using hN₂.symm

/-- Original compatibility gives the two cross-coprimalities through the
common modulus, even when the original moduli are not coprime. -/
theorem N₁_D (hc : WCompatible q r N₁ N₂) : N₁.Coprime v.D := by
  have hNδ : N₁.Coprime v.δ := by
    rw [hv.δ_eq]
    exact hc.1.of_dvd_right (Nat.gcd_dvd_left q r)
  exact (hNδ.mul_right (coprime_of_prime_support hNδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hNδ hv.δ₂_support)

theorem N₂_D (hc : WCompatible q r N₁ N₂) : N₂.Coprime v.D := by
  have hNδ : N₂.Coprime v.δ := by
    rw [hv.δ_eq]
    exact hc.2.1.of_dvd_right (Nat.gcd_dvd_right q r)
  exact (hNδ.mul_right (coprime_of_prime_support hNδ hv.δ₁_support)).mul_right
    (coprime_of_prime_support hNδ hv.δ₂_support)

theorem n_congruence (hc : WCompatible q r N₁ N₂) :
    Nat.ModEq v.δ (v.d₁ * v.n₁) v.n₂ := by
  have hdδ : v.d.Coprime v.δ := by
    apply (hv.N₁_D hc).of_dvd
    · rw [hv.N₁_eq]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  apply Nat.ModEq.cancel_left_of_coprime hdδ.symm.gcd_eq_one
  simpa only [← hv.δ_eq, hv.N₁_eq, hv.N₂_eq, mul_assoc] using hc.2.2

/-- All the arithmetic hypotheses of the existing three-factor phase follow
from the canonical decomposition and the original W compatibility. -/
theorem phase_coprime (hc : WCompatible q r N₁ N₂) :
    (v.n₁ * v.k₁ * v.k₂).Coprime v.D' ∧
      v.k₁.Coprime (v.n₁ * v.k₂) ∧ v.n₂.Coprime (v.n₁ * v.k₂) := by
  have hN₁ : (v.d * v.d₁ * v.n₁).Coprime q := hv.N₁_eq ▸ hc.1
  have hN₂ : (v.d * v.n₂).Coprime r := hv.N₂_eq ▸ hc.2.1
  have hnq := hN₁.of_dvd_right hv.k₁_dvd
  have hnr := hN₂.of_dvd_right hv.k₂_dvd
  have hk₁d : v.k₁.Coprime v.d :=
    (hnq.of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).symm
  have hk₂d : v.k₂.Coprime v.d :=
    (hnr.of_dvd_left (dvd_mul_right _ _)).symm
  have hn₁D : v.n₁.Coprime v.D := by
    apply (hv.N₁_D hc).of_dvd_left
    rw [hv.N₁_eq]; exact dvd_mul_left _ _
  have hnd : (v.n₁ * v.k₁ * v.k₂).Coprime v.d :=
    (hv.n₁_d.mul_left hk₁d).mul_left hk₂d
  have hnd₁ := coprime_of_prime_support hnd hv.d₁_support
  have hnD : (v.n₁ * v.k₁ * v.k₂).Coprime v.D := by
    simpa only [mul_assoc] using hn₁D.mul_left hv.k_D
  refine ⟨(hnd.mul_right hnd₁).mul_right hnD, ?_, ?_⟩
  · exact (hnq.of_dvd_left (dvd_mul_left _ _)).symm.mul_right hv.k_coprime
  · exact hv.n₁_n₂.symm.mul_right (hnr.of_dvd_left (dvd_mul_left _ _))

omit hv in
/-- Uniform algebraic small-modulus bounds; no discarded contribution is
estimated here. -/
theorem small_moduli {Y : ℝ} (hY : 0 ≤ Y)
    (hd : (v.d : ℝ) ≤ Y) (hd₁ : (v.d₁ : ℝ) ≤ Y)
    (hδ : (v.δ : ℝ) ≤ Y) (hδ₁ : (v.δ₁ : ℝ) ≤ Y)
    (hδ₂ : (v.δ₂ : ℝ) ≤ Y) : (v.D : ℝ) ≤ Y ^ 3 ∧ (v.D' : ℝ) ≤ Y ^ 5 := by
  have hD : (v.D : ℝ) ≤ Y ^ 3 := by
    unfold D
    push_cast
    calc
      _ ≤ (Y * Y) * Y :=
        mul_le_mul (mul_le_mul hδ hδ₁ (by positivity) hY) hδ₂
          (by positivity) (by positivity)
      _ = _ := by ring
  refine ⟨hD, ?_⟩
  unfold D'
  push_cast
  calc
    _ ≤ (Y * Y) * Y ^ 3 :=
      mul_le_mul (mul_le_mul hd hd₁ (by positivity) hY) hD
        (by positivity) (by positivity)
    _ = _ := by ring

end WGCDData.Valid

/-- The real frequency on every positive compatible original tuple, with
all factorization and coprimality premises now constructed. -/
theorem wPoissonFrequency_eq_canonical_threeFactor
    {q r N₁ N₂ : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hc : WCompatible q r N₁ N₂)
    (M : ℝ) (a h : ℤ) :
    let v := wGCDData q r N₁ N₂
    wPoissonFrequency M a q r N₁ N₂ h =
      wThreeFactorPoissonFrequency M a q r v.d v.d₁ v.D v.k₁ v.k₂ v.n₁ v.n₂ h := by
  dsimp only
  let v := wGCDData q r N₁ N₂
  have hv : v.Valid q r N₁ N₂ := wGCDData_valid hq hr hN₁ hN₂
  have hp := hv.phase_coprime hc
  have hc' : WCompatible q r (v.d * v.d₁ * v.n₁) (v.d * v.n₂) := by
    simpa only [← hv.N₁_eq, ← hv.N₂_eq] using hc
  have he := wPoissonFrequency_eq_threeFactor hv.d_pos hv.d₁_pos hv.D_pos
    hv.k₁_pos hv.k₂_pos hv.n₁_pos hv.lcm_eq hv.k₁_dvd hv.k₂_dvd
    hv.k_D hp.1 hp.2.1 hp.2.2 hc' M a h
  simpa only [← hv.N₁_eq, ← hv.N₂_eq] using he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
