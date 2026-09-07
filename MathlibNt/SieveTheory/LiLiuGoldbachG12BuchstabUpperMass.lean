import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabEndpointMass

open scoped BigOperators
open Finset Filter LiLiuPrereqBuchstab
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The cross has three lower prime labels and one upper label. -/
theorem goldbachG12_canonical_cofactor_lower_bound {N : ℕ} {v : GoldbachG11Label}
    (hN : 2 ≤ N)
    (hv : v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) :
    (N : ℝ)^(4/11 : ℝ) ≤ (N : ℝ)/goldbachG11LabelProd v := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : (0 : ℝ) < goldbachG11LabelProd v := by
    exact_mod_cast goldbachG11LabelProd_pos
      (goldbachG12Labels_subset_goldbachG11Labels _ _ _ _ hv)
  rcases v with ⟨t,s,r,q⟩
  obtain ⟨hr,hq,hs,ht,_,_,hrq,hqs,hsb,_,htc⟩ := mem_goldbachG12Labels_iff.mp hv
  have hrb : (r : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) :=
    (show (r : ℝ) ≤ s by exact_mod_cast hrq.trans hqs).trans hsb
  have hqb : (q : ℝ) ≤ (N : ℝ)^(4/33 : ℝ) :=
    (show (q : ℝ) ≤ s by exact_mod_cast hqs).trans hsb
  have hp : (goldbachG11LabelProd ⟨t,s,r,q⟩ : ℝ) ≤ (N : ℝ)^(7/11 : ℝ) := by
    calc
      _ = (r : ℝ)*q*s*t := by simp [goldbachG11LabelProd]
      _ ≤ (N : ℝ)^(4/33 : ℝ)*(N : ℝ)^(4/33 : ℝ)*
          (N : ℝ)^(4/33 : ℝ)*(N : ℝ)^(3/11 : ℝ) := by gcongr
      _ = (N : ℝ)^(7/11 : ℝ) := by
        rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
        norm_num
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (N : ℝ)^(4/11 : ℝ)*(N : ℝ)^(7/11 : ℝ) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hNp.le _)
    _ = N := by rw [← Real.rpow_add hNp]; norm_num

/-- Buchstab on the unconditioned rough cofactor mother, on the ORIGINAL cross.
This is not the output-prime sieve and does not itself supply the second logarithm. -/
theorem goldbachG12_rough_upper_buchstab (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
        (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ) ≤
          goldbachG11BuchstabMass ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 +
            η*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by
  obtain ⟨X,hX,hsource⟩ := roughCount_uniform_buchstab (u₀ := 3) (by norm_num) hη
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/11)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  obtain ⟨K,hK⟩ := eventually_atTop.mp hg
  refine ⟨max 4 K, le_max_left _ _, ?_⟩
  intro N hN v hv
  have hN2 : 2 ≤ N := by omega
  have hyX := (hK N (by omega)).trans (goldbachG12_canonical_cofactor_lower_bound hN2 hv)
  have hy1 : 1 < (N : ℝ)/goldbachG11LabelProd v := hX.trans_le hyX
  rcases v with ⟨t,s,r,q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG12Labels, Finset.mem_sigma] using hv
  have hq1 : (1 : ℝ) < q := by
    exact_mod_cast (mem_goldbachClosedPrimes_iff.mp hm.2.2.2).1.one_lt
  have hU := goldbachG12_canonical_logQuotient_bounds hN2 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  change Real.log ((N : ℝ)/goldbachG11LabelProd ⟨t,s,r,q⟩)/Real.log (q : ℝ) ∈
    Set.Icc (3 : ℝ) (1141/132) at hU
  have hdata := hsource _ hyX _ ⟨hU.1, hU.2.trans (by norm_num)⟩
  rw [← goldbachG11_buchstab_cutoff_identity hy1 hq1,
    goldbachG11_buchstab_source_mass_identity hy1 hq1] at hdata
  have herr := goldbachG11_buchstab_relative_to_absolute hy1 hq1
    ((by norm_num : (1 : ℝ) ≤ 3).trans hU.1) hη hdata.2
  exact sub_le_iff_le_add'.mp ((le_abs_self _).trans herr)

noncomputable def goldbachG12FullRoughMass (N : ℕ) : ℝ :=
  ∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
    (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ)

noncomputable def goldbachG12BuchstabUpperMass (N : ℕ) (η : ℝ) : ℝ :=
  ∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
    (goldbachG11BuchstabMass ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 +
      η*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ))

theorem goldbachG12FullRoughMass_le_buchstabUpper (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12FullRoughMass N ≤ goldbachG12BuchstabUpperMass N η := by
  obtain ⟨N₀,hN₀,hn⟩ := goldbachG12_rough_upper_buchstab η hη
  exact ⟨N₀,hN₀,fun N hN => Finset.sum_le_sum (hn N hN)⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
