import MathlibNt.SieveTheory.LiLiuGoldbachG12ActiveProduct
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindow

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG12ActiveProductSupport_mem_full {N m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) := by
  obtain ⟨u,hu,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact mem_goldbachG11ProductSupport_iff.mpr
    ⟨u,goldbachG12GoodCrossBodies_subset _ _ _ _ hu,he⟩

theorem goldbachG12PiLiEndpoints_bounds {N m : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (N : ℝ)^(4/53 : ℝ) ≤ goldbachG11PiLiLo N ε m ∧
      goldbachG11PiLiLo N ε m ≤ goldbachG11PiLiHi N m ∧
      goldbachG11PiLiHi N m ≤ (N : ℝ)/m := by
  obtain ⟨hm0,_,_,_,hu,hfac,_⟩ := goldbachG12ActiveProductSupport_data hm
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm0
  have hquot : (N : ℝ)^(4/53 : ℝ) ≤ (N : ℝ)/m := by
    apply (le_div_iff₀ hmp).mpr
    calc
      _ ≤ (N : ℝ)^(4/53 : ℝ)*(N : ℝ)^(49/53 : ℝ) :=
        mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hNp.le _)
      _ = N := by rw [← Real.rpow_add hNp]; norm_num
  have hhi : (N : ℝ)^(4/53 : ℝ) ≤ goldbachG11PiLiHi N m := le_min hfac hquot
  exact ⟨le_min hhi (le_max_left _ _),min_le_left _ _,min_le_right _ _⟩

/-- The original fibre, with exactly the two common real endpoints.
The output-prime and coprimality filters have not entered the coefficient. -/
theorem goldbachG12ProductFirstPrimeFiber_linked_iff {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m ↔
      r.Prime ∧ ¬r ∣ N ∧ goldbachG11PiLiLo N ε m < (r : ℝ) ∧
        (r : ℝ) ≤ goldbachG11PiLiHi N m ∧ (N-r*m).Prime := by
  have hs := goldbachG12ActiveProductSupport_mem_full hm
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (goldbachG11ProductSupport_data hs).1
  rw [goldbachG11ProductFirstPrimeFiber_endpoint_iff hs]
  constructor
  · rintro ⟨hp, hNd, hz, hq, he, hn, hout⟩
    have hqR : (r : ℝ) ≤ m.minFac := by exact_mod_cast hq
    have hnR : (r : ℝ)*(m : ℝ) ≤ N := by exact_mod_cast hn
    have heR : ε * N < (r : ℝ)*(m : ℝ) := by exact_mod_cast he
    have hhi : (r : ℝ) ≤ goldbachG11PiLiHi N m :=
      le_min hqR ((le_div_iff₀ hm0).mpr hnR)
    have hlo : max ((N : ℝ)^(4/53 : ℝ)) (ε*N/m) < (r : ℝ) :=
      max_lt hz ((div_lt_iff₀ hm0).mpr heR)
    exact ⟨hp, hNd, (min_le_right _ _).trans_lt hlo, hhi, hout⟩
  · rintro ⟨hp, hNd, hlo, hhi, hout⟩
    have hlower : max ((N : ℝ)^(4/53 : ℝ)) (ε*N/m) < (r : ℝ) := by
      rcases min_lt_iff.mp hlo with hbad | hgood
      · exact False.elim ((not_lt_of_ge hhi) hbad)
      · exact hgood
    have hparts := le_min_iff.mp hhi
    have hz := (le_max_left _ _).trans_lt hlower
    have he := (div_lt_iff₀ hm0).mp ((le_max_right _ _).trans_lt hlower)
    have hn := (le_div_iff₀ hm0).mp hparts.2
    refine ⟨hp, hNd, hz, ?_, ?_, ?_, hout⟩
    · exact_mod_cast hparts.1
    · exact_mod_cast he
    · exact_mod_cast hn

/-- Exact original carrier; no prime, repeated factor or endpoint was discarded. -/
theorem goldbachG12ProductFirstPrimeFiber_eq_linkedWindow {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4/53 : ℝ)) m =
      (goldbachG11LinkedPrimeWindow N ε m).filter
        (fun r => ¬r ∣ N ∧ (N-r*m).Prime) := by
  classical
  ext r
  rw [goldbachG12ProductFirstPrimeFiber_linked_iff hm]
  simp only [goldbachG11LinkedPrimeWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hNd, hlo, hhi, hout⟩
    have hs := goldbachG12ActiveProductSupport_mem_full hm
    have hm0 := (goldbachG11ProductSupport_data hs).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hnR := (le_div_iff₀ hmR).mp ((min_le_right _ _).trans' hhi)
    have hn : r*m ≤ N := by exact_mod_cast hnR
    have hrN : r ≤ N := by
      nlinarith [Nat.mul_le_mul_left r (show 1 ≤ m by omega)]
    exact ⟨⟨Nat.lt_succ_of_le hrN, hp, hlo, hhi⟩, hNd, hout⟩
  · rintro ⟨⟨_, hp, hlo, hhi⟩, hNd, hout⟩
    exact ⟨hp, hNd, hlo, hhi, hout⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig