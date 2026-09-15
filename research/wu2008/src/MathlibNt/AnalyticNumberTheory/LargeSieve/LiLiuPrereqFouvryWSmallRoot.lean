import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWGCDReindex

/-!
# The small-modulus root of the W phase

Fouvry (1984), p. 237, (8.8), and Fouvry (1987), p. 627, (3.11).
The large CRT residue may be replaced, modulo `D`, by the CRT on the two
small moduli. The resulting root phase is constant on explicit congruence
classes; no equality of chosen integer representatives is asserted.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem WCompatible.of_dvd {q r p s N₁ N₂ : ℕ}
    (hc : WCompatible q r N₁ N₂) (hp : p ∣ q) (hs : s ∣ r) :
    WCompatible p s N₁ N₂ :=
  ⟨hc.1.of_dvd_right hp, hc.2.1.of_dvd_right hs,
    hc.2.2.of_dvd (Nat.dvd_gcd ((Nat.gcd_dvd_left p s).trans hp)
      ((Nat.gcd_dvd_right p s).trans hs))⟩

/-- Restriction of the actual constructed CRT representative. -/
theorem productCRTResidue_restrict {q r p s N₁ N₂ : ℕ}
    (hc : WCompatible q r N₁ N₂) (hp : p ∣ q) (hs : s ∣ r) (a : ℤ) :
    Int.ModEq (p.lcm s) (productCRTResidue q r N₁ N₂ a)
      (productCRTResidue p s N₁ N₂ a) := by
  have hb := productCRTResidue_spec a hc
  apply (productCRTResidue_spec a (hc.of_dvd hp hs)).2.2 _ |>.mp
  exact ⟨hb.1.of_dvd (by exact_mod_cast hp),
    hb.2.1.of_dvd (by exact_mod_cast hs)⟩

/-- Changing the two multipliers within their residue classes only changes
the chosen representative by a multiple of the lcm. -/
theorem productCRTResidue_congr {p s N₁ N₂ N₁' N₂' : ℕ}
    (hc : WCompatible p s N₁ N₂) (hc' : WCompatible p s N₁' N₂')
    (h₁ : Nat.ModEq p N₁ N₁') (h₂ : Nat.ModEq s N₂ N₂') (a : ℤ) :
    Int.ModEq (p.lcm s) (productCRTResidue p s N₁ N₂ a)
      (productCRTResidue p s N₁' N₂' a) := by
  have hb := productCRTResidue_spec a hc
  apply (productCRTResidue_spec a hc').2.2 _ |>.mp
  exact ⟨((Int.natCast_modEq_iff.mpr h₁).symm.mul_left _).trans hb.1,
    ((Int.natCast_modEq_iff.mpr h₂).symm.mul_left _).trans hb.2.1⟩

theorem wPhaseInverse_congr {u v m : ℕ} (hu : u.Coprime m)
    (hv : v.Coprime m) (h : Nat.ModEq m u v) :
    Int.ModEq m (wPhaseInverse u m) (wPhaseInverse v m) := by
  apply (product_modEq_iff_of_coprime hu
    (b := wPhaseInverse v m) (a := 1) ?_).mp
  · simpa only [mul_comm] using wPhaseInverse_spec hu
  · exact ((Int.natCast_modEq_iff.mpr h).mul_left _).trans
      (by simpa only [mul_comm] using wPhaseInverse_spec hv)

def smallWCRTResidue (d d₁ δ δ₁ δ₂ n₁ n₂ : ℕ) (a : ℤ) : ℤ :=
  productCRTResidue (δ * δ₁) (δ * δ₂) (d * d₁ * n₁) (d * n₂) a

theorem WGCDData.Valid.small_lcm {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) : (v.δ * v.δ₁).lcm (v.δ * v.δ₂) = v.D := by
  rw [Nat.lcm_mul_left, hv.δ_coprime.lcm_eq_mul]
  exact (mul_assoc _ _ _).symm

theorem WGCDData.Valid.small_compatible {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) (hc : WCompatible q r N₁ N₂) :
    WCompatible (v.δ * v.δ₁) (v.δ * v.δ₂)
      (v.d * v.d₁ * v.n₁) (v.d * v.n₂) := by
  rw [← hv.N₁_eq, ← hv.N₂_eq]
  apply hc.of_dvd
  · rw [hv.q_eq]; exact dvd_mul_right _ _
  · rw [hv.r_eq]; exact dvd_mul_right _ _

theorem WGCDData.Valid.residue_modEq_small {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) (hc : WCompatible q r N₁ N₂) (a : ℤ) :
    Int.ModEq v.D (productCRTResidue q r N₁ N₂ a)
      (smallWCRTResidue v.d v.d₁ v.δ v.δ₁ v.δ₂ v.n₁ v.n₂ a) := by
  have h := productCRTResidue_restrict hc
    (show v.δ * v.δ₁ ∣ q by rw [hv.q_eq]; exact dvd_mul_right _ _)
    (show v.δ * v.δ₂ ∣ r by rw [hv.r_eq]; exact dvd_mul_right _ _) a
  simpa only [smallWCRTResidue, hv.small_lcm, hv.N₁_eq, hv.N₂_eq] using h

/-- The actual small CRT root depends only on the two beta coordinates
modulo `D`, for fixed outer coordinates. -/
theorem smallWCRTResidue_congr
    {d d₁ δ δ₁ δ₂ n₁ n₂ n₁' n₂' : ℕ}
    (hδ : δ₁.Coprime δ₂)
    (hc : WCompatible (δ * δ₁) (δ * δ₂) (d * d₁ * n₁) (d * n₂))
    (hc' : WCompatible (δ * δ₁) (δ * δ₂) (d * d₁ * n₁') (d * n₂'))
    (h₁ : Nat.ModEq (δ * δ₁ * δ₂) n₁ n₁')
    (h₂ : Nat.ModEq (δ * δ₁ * δ₂) n₂ n₂') (a : ℤ) :
    Int.ModEq (δ * δ₁ * δ₂)
      (smallWCRTResidue d d₁ δ δ₁ δ₂ n₁ n₂ a)
      (smallWCRTResidue d d₁ δ δ₁ δ₂ n₁' n₂' a) := by
  have hp : δ * δ₁ ∣ δ * δ₁ * δ₂ := dvd_mul_right _ _
  have hs : δ * δ₂ ∣ δ * δ₁ * δ₂ := ⟨δ₁, by ring⟩
  have he := productCRTResidue_congr hc hc'
    ((h₁.of_dvd hp).mul_left (d * d₁)) ((h₂.of_dvd hs).mul_left d) a
  simpa only [smallWCRTResidue, Nat.lcm_mul_left, hδ.lcm_eq_mul, Nat.cast_mul,
    mul_assoc] using he

def wSmallRootPhase (d d₁ δ δ₁ δ₂ k₁ k₂ n₁ n₂ : ℕ) (a : ℤ) : UnitAddCircle :=
  let D := δ * δ₁ * δ₂
  let D' := d * d₁ * D
  (((smallWCRTResidue d d₁ δ δ₁ δ₂ n₁ n₂ a : ℝ) *
    wPhaseInverse (k₁ * k₂) D / D -
    (a : ℝ) * wPhaseInverse (n₁ * k₁ * k₂) D' / D' : ℝ) : UnitAddCircle)

/-- Replacement of the complementary root in the actual W phase. -/
theorem WGCDData.Valid.rootPhase_eq {v : WGCDData} {q r N₁ N₂ : ℕ}
    (hv : v.Valid q r N₁ N₂) (hc : WCompatible q r N₁ N₂) (a : ℤ) :
    (((productCRTResidue q r N₁ N₂ a : ℝ) * wPhaseInverse (v.k₁ * v.k₂) v.D / v.D -
      (a : ℝ) * wPhaseInverse (v.n₁ * v.k₁ * v.k₂) v.D' / v.D' : ℝ) : UnitAddCircle) =
      wSmallRootPhase v.d v.d₁ v.δ v.δ₁ v.δ₂ v.k₁ v.k₂ v.n₁ v.n₂ a := by
  have he := wPhase_circle_eq_of_modEq hv.D_pos
    ((hv.residue_modEq_small hc a).mul_right (wPhaseInverse (v.k₁ * v.k₂) v.D))
  push_cast at he
  simpa only [wSmallRootPhase, WGCDData.D, WGCDData.D', AddCircle.coe_sub] using
    congrArg (fun z : UnitAddCircle ↦ z -
      (((a : ℝ) * wPhaseInverse (v.n₁ * v.k₁ * v.k₂) v.D' / v.D' : ℝ) :
        UnitAddCircle)) he

/-- The entire original phase with its root replaced by a genuinely
small-modulus CRT, ready for freezing before partial summation. -/
theorem productCRTResidue_phase_smallRoot
    {v : WGCDData} {q r N₁ N₂ : ℕ} (hv : v.Valid q r N₁ N₂)
    (hc : WCompatible q r N₁ N₂) (a : ℤ) :
    (((productCRTResidue q r N₁ N₂ a : ℝ) / (q.lcm r) : ℝ) : UnitAddCircle) =
      wSmallRootPhase v.d v.d₁ v.δ v.δ₁ v.δ₂ v.k₁ v.k₂ v.n₁ v.n₂ a +
      (((a : ℝ) / ((v.n₁ : ℝ) * v.k₁ * v.k₂ * v.D') : ℝ) : UnitAddCircle) +
      (((a : ℝ) * ((v.d₁ : ℝ) * v.n₁ - v.n₂) *
        wPhaseInverse (v.D' * v.n₂ * v.k₁) (v.n₁ * v.k₂) /
        ((v.n₁ : ℝ) * v.k₂) : ℝ) : UnitAddCircle) := by
  have hp := hv.phase_coprime hc
  have hc' : WCompatible q r (v.d * v.d₁ * v.n₁) (v.d * v.n₂) := by
    simpa only [← hv.N₁_eq, ← hv.N₂_eq] using hc
  have he := productCRTResidue_phase_threeFactor hv.d_pos hv.d₁_pos hv.D_pos
    hv.k₁_pos hv.k₂_pos hv.n₁_pos hv.lcm_eq hv.k₁_dvd hv.k₂_dvd
    hv.k_D hp.1 hp.2.1 hp.2.2 hc' a
  dsimp only at he
  rw [← hv.N₁_eq, ← hv.N₂_eq] at he
  have hroot := hv.rootPhase_eq hc a
  unfold WGCDData.D' at hroot
  rw [hroot] at he
  exact he

/-- Freeze the small root by fixing residue classes. The first inverse
uses the modulus `D`; the second uses `D'=d*d₁*D`. -/
theorem wSmallRootPhase_congr
    {d d₁ δ δ₁ δ₂ k₁ k₂ k₁' k₂' n₁ n₂ n₁' n₂' : ℕ}
    (hd : 0 < d) (hd₁ : 0 < d₁) (hD : 0 < δ * δ₁ * δ₂)
    (hδ : δ₁.Coprime δ₂)
    (hc : WCompatible (δ * δ₁) (δ * δ₂) (d * d₁ * n₁) (d * n₂))
    (hc' : WCompatible (δ * δ₁) (δ * δ₂) (d * d₁ * n₁') (d * n₂'))
    (hk : (k₁ * k₂).Coprime (δ * δ₁ * δ₂))
    (hk' : (k₁' * k₂').Coprime (δ * δ₁ * δ₂))
    (hnk : (n₁ * k₁ * k₂).Coprime (d * d₁ * (δ * δ₁ * δ₂)))
    (hnk' : (n₁' * k₁' * k₂').Coprime (d * d₁ * (δ * δ₁ * δ₂)))
    (hn₁ : Nat.ModEq (d * d₁ * (δ * δ₁ * δ₂)) n₁ n₁')
    (hn₂ : Nat.ModEq (δ * δ₁ * δ₂) n₂ n₂')
    (hkk : Nat.ModEq (d * d₁ * (δ * δ₁ * δ₂)) (k₁ * k₂) (k₁' * k₂'))
    (a : ℤ) :
    wSmallRootPhase d d₁ δ δ₁ δ₂ k₁ k₂ n₁ n₂ a =
      wSmallRootPhase d d₁ δ δ₁ δ₂ k₁' k₂' n₁' n₂' a := by
  let D := δ * δ₁ * δ₂
  have hdiv : D ∣ d * d₁ * D := dvd_mul_left _ _
  have hu := smallWCRTResidue_congr hδ hc hc' (hn₁.of_dvd hdiv) hn₂ a
  have hi := wPhaseInverse_congr hk hk' (hkk.of_dvd hdiv)
  have hj := wPhaseInverse_congr hnk hnk'
    (by simpa only [mul_assoc] using hn₁.mul hkk)
  have he₁ := wPhase_circle_eq_of_modEq hD (hu.mul hi)
  have he₂ := wPhase_circle_eq_of_modEq (Nat.mul_pos (Nat.mul_pos hd hd₁) hD)
    (hj.mul_left a)
  push_cast at he₁ he₂
  simpa only [wSmallRootPhase, Nat.cast_mul, AddCircle.coe_sub] using
    congrArg₂ (fun x y : UnitAddCircle ↦ x - y) he₁ he₂

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
