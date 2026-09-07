import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabUpperMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant

open Set Filter LiLiuPrereqBuchstab
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Compact continuity gives one modulus for every endpoint, not a derivative estimate. -/
theorem goldbachG12Thin_buchstab_modulus (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ u ∈ Icc (2 : ℝ) 10, ∀ v ∈ Icc (2 : ℝ) 10,
      |u-v| < δ → |buchstab u-buchstab v| < η := by
  have hc : UniformContinuousOn buchstab (Icc (2 : ℝ) 10) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_buchstab.continuousOn
  obtain ⟨d,hd,hm⟩ := (Metric.uniformContinuousOn_iff.mp hc) η hη
  refine ⟨min d 1, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro u hu v hv huv
  exact hm u hu v hv (by simpa only [Real.dist_eq] using huv.trans_le (min_le_left d 1))

/-- Real endpoints retain the literal integer rough counts, including both floors.
The threshold is chosen before the scaling parameter. -/
theorem goldbachG12Thin_uniform_endpoint
    (e₀ : ℝ) (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ X L : ℝ, 1 < X ∧ 0 < L ∧ ∀ y q : ℝ,
      X ≤ e₀*y → L ≤ Real.log q → 1 < q →
      Real.log y / Real.log q ∈ Icc (3 : ℝ) (1141/132) →
      ∀ l ∈ Icc e₀ 1,
        |(roughCount (l*y) q : ℝ) - l*goldbachG11BuchstabMass y q| ≤
          η*y/Real.log q := by
  have hh : 0 < η/2 := half_pos hη
  obtain ⟨X,hX,hs⟩ := roughCount_uniform_buchstab (u₀ := 2) (by norm_num) hh
  obtain ⟨δ,hδ,hδ1,hm⟩ := goldbachG12Thin_buchstab_modulus (η/2) hh
  refine ⟨X, |Real.log e₀|/δ+1, hX, by positivity, ?_⟩
  intro y q hy hL hq hu l hl
  have hlq := Real.log_pos hq
  have hy0 : 0 < y := by
    have : 0 < e₀*y := (by linarith : 0 < X).trans_le hy
    exact (mul_pos_iff.mp this).resolve_right (by intro h; linarith [h.1]) |>.2
  have hl0 : 0 < l := he₀.trans_le hl.1
  have hxy : X ≤ l*y := hy.trans (mul_le_mul_of_nonneg_right hl.1 hy0.le)
  have hxy1 : 1 < l*y := hX.trans_le hxy
  have hly : l*y ≤ y := mul_le_of_le_one_left hy0.le hl.2
  have hlogl : |Real.log l| ≤ |Real.log e₀| := by
    have hlo := Real.log_le_log he₀ hl.1
    have hhi := Real.log_le_log hl0 hl.2
    have hehi := Real.log_le_log he₀ he₁
    simp only [Real.log_one] at hhi hehi
    rw [abs_of_nonpos hhi, abs_of_nonpos hehi]
    linarith
  have hsmall : |Real.log l / Real.log q| < δ := by
    rw [abs_div, abs_of_pos hlq]
    apply (div_lt_iff₀ hlq).mpr
    have hbound : |Real.log e₀| + δ ≤ δ * Real.log q := by
      have := mul_le_mul_of_nonneg_left hL hδ.le
      field_simp at this
      nlinarith
    linarith
  have hid : Real.log (l*y)/Real.log q =
      Real.log y/Real.log q + Real.log l/Real.log q := by
    rw [Real.log_mul hl0.ne' hy0.ne']
    ring
  have hp : Real.log (l*y)/Real.log q ∈ Icc (2 : ℝ) 10 := by
    rw [hid]
    have ha := abs_lt.mp hsmall
    constructor <;> linarith [hu.1,hu.2]
  have hw : |buchstab (Real.log (l*y)/Real.log q) -
      buchstab (Real.log y/Real.log q)| ≤ η/2 := by
    apply le_of_lt
    apply hm _ hp _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simpa only [hid, add_sub_cancel_left] using hsmall
  have hsource := hs (l*y) hxy _ ⟨hp.1,hp.2.trans (by norm_num)⟩
  rw [← goldbachG11_buchstab_cutoff_identity hxy1 hq,
    goldbachG11_buchstab_source_mass_identity hxy1 hq] at hsource
  have herr := goldbachG11_buchstab_relative_to_absolute hxy1 hq
    (by linarith [hp.1]) hh hsource.2
  have hmass : |goldbachG11BuchstabMass (l*y) q - l*goldbachG11BuchstabMass y q| ≤
      (η/2)*y/Real.log q := by
    have hid' : goldbachG11BuchstabMass (l*y) q - l*goldbachG11BuchstabMass y q =
        (l*y)/Real.log q * (buchstab (Real.log (l*y)/Real.log q) -
          buchstab (Real.log y/Real.log q)) := by
      unfold goldbachG11BuchstabMass
      ring
    rw [hid', abs_mul, abs_of_nonneg (by positivity : 0 ≤ (l*y)/Real.log q)]
    calc
      _ ≤ (l*y)/Real.log q * (η/2) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ y/Real.log q * (η/2) := by gcongr
      _ = _ := by ring
  have herr' : |(roughCount (l*y) q : ℝ) - goldbachG11BuchstabMass (l*y) q| ≤
      (η/2)*y/Real.log q := herr.trans (by gcongr)
  calc
    _ ≤ |(roughCount (l*y) q : ℝ) - goldbachG11BuchstabMass (l*y) q| +
        |goldbachG11BuchstabMass (l*y) q - l*goldbachG11BuchstabMass y q| :=
      abs_sub_le _ _ _
    _ ≤ (η/2)*y/Real.log q + (η/2)*y/Real.log q := add_le_add herr' hmass
    _ = _ := by ring

/-- Uniform raw-mother endpoint approximation on the original closed cross. -/
theorem goldbachG12Thin_canonical_endpoints
    (e₀ : ℝ) (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
      ∀ l ∈ Icc e₀ 1,
        |(roughCount (l*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) -
          l*goldbachG11BuchstabMass ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2| ≤
          η*((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by
  obtain ⟨X,L,_,_,hend⟩ := goldbachG12Thin_uniform_endpoint e₀ he₀ he₁ η hη
  have hg := (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/11)).comp
    tendsto_natCast_atTop_atTop).const_mul_atTop he₀).eventually (eventually_ge_atTop X)
  have hl := (((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 4/53))).eventually (eventually_ge_atTop L)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hg.and hl)
  refine ⟨max 4 K,le_max_left _ _,?_⟩
  intro N hN v hv l hscale
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound := goldbachG12_canonical_cofactor_lower_bound hN2 hv
  obtain ⟨hy,hl⟩ := hK N (by omega)
  rcases v with ⟨t,s,r,q⟩
  obtain ⟨_,hq,_,_,_,hz,hrq,_,_,_,_⟩ := mem_goldbachG12Labels_iff.mp hv
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hzq : (N : ℝ)^(4/53 : ℝ) ≤ q := hz.trans (by exact_mod_cast hrq)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hNp _) hzq
  rw [Real.log_rpow hNp] at hlog
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG12Labels, Finset.mem_sigma] using hv
  have hu := goldbachG12_canonical_logQuotient_bounds hN2 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  exact hend _ _ (hy.trans (mul_le_mul_of_nonneg_left hbound he₀.le))
    (hl.trans hlog) hq1 hu l hscale

/-- The coefficient is the certified broad Buchstab majorant. This does not
assert an output-prime sieve, a second logarithm, or a full boundary payment. -/
theorem goldbachG12Thin_cofactor_budget
    (e₀ : ℝ) (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
      ∀ l₁ l₂ : ℝ, e₀ ≤ l₁ → l₁ ≤ l₂ → l₂ ≤ 1 →
        (roughCount (l₂*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) -
          (roughCount (l₁*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) ≤
          ((564383/1000000 : ℝ)*(l₂-l₁)+η)*
            ((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) := by
  obtain ⟨K,hK,hend⟩ := goldbachG12Thin_canonical_endpoints e₀ he₀ he₁ (η/2) (half_pos hη)
  refine ⟨K,hK,?_⟩
  intro N hN v hv l₁ l₂ hl h12 hh
  have h1 := abs_le.mp (hend N hN v hv l₁ ⟨hl,h12.trans hh⟩)
  have h2 := abs_le.mp (hend N hN v hv l₂ ⟨hl.trans h12,hh⟩)
  have hN2 : 2 ≤ N := by omega
  rcases v with ⟨t,s,r,q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG12Labels, Finset.mem_sigma] using hv
  have hu := goldbachG12_canonical_logQuotient_bounds hN2 hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hw := LiLiuGoldbachG12BuchstabMajorant.buchstab_le_564383 hu.1
  have hq1 : (1 : ℝ) < q := by
    exact_mod_cast (mem_goldbachClosedPrimes_iff.mp hm.2.2.2).1.one_lt
  have hlq := Real.log_pos hq1
  let y : ℝ := (N : ℝ)/goldbachG11LabelProd ⟨t,s,r,q⟩
  have hy : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmass : (l₂-l₁)*goldbachG11BuchstabMass y q ≤
      (564383/1000000 : ℝ)*(l₂-l₁)*y/Real.log (q : ℝ) := by
    have hw' : buchstab (Real.log y/Real.log (q : ℝ)) ≤ (564383/1000000 : ℝ) := hw
    unfold goldbachG11BuchstabMass
    calc
      _ = (l₂-l₁)*y*buchstab (Real.log y/Real.log (q : ℝ))/Real.log (q : ℝ) := by ring
      _ ≤ (l₂-l₁)*y*(564383/1000000 : ℝ)/Real.log (q : ℝ) := by gcongr
      _ = _ := by ring
  change (roughCount (l₂*y) q : ℝ) - (roughCount (l₁*y) q : ℝ) ≤ _
  have hlower := h1.1
  change -(η/2*y/Real.log (q : ℝ)) ≤ (roughCount (l₁*y) q : ℝ) - l₁*goldbachG11BuchstabMass y q at hlower
    -- Keep the lower endpoint error and the upper endpoint error separately.
  have hupper := h2.2
  change (roughCount (l₂*y) q : ℝ) - l₂*goldbachG11BuchstabMass y q ≤ η/2*y/Real.log (q : ℝ) at hupper
  calc
    _ ≤ (l₂-l₁)*goldbachG11BuchstabMass y q + η*y/Real.log (q : ℝ) := by
      have he : η*y/Real.log (q : ℝ) = 2*(η/2*y/Real.log (q : ℝ)) := by ring
      rw [he]
      nlinarith only [hlower, hupper]
    _ ≤ (564383/1000000 : ℝ)*(l₂-l₁)*y/Real.log (q : ℝ) + η*y/Real.log (q : ℝ) := add_le_add hmass le_rfl
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
