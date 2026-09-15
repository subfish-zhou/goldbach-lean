import MathlibNt.Wu2008DoubleSieve.NinthMainMassIntegral

/-!
# Triangular reciprocal-prime quadrature for the ninth main mass

Two applications of the existing uniform weighted theorem suffice.
Closed windows enlarge the exact source endpoints without a boundary
loss; their possible endpoint atoms are already paid by that theorem.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def ninthMainCoordinate (N p : ℕ) : ℝ := log p / log N

noncomputable def ninthMainPairSum (N : ℕ) : ℝ :=
  ∑ t ∈ ninthPairs N (ninthProfileW N) (ninthProfileU N),
    ninthMainKernel (ninthMainCoordinate N t.1) (ninthMainCoordinate N t.2) /
      ((t.1 : ℝ) * t.2)

noncomputable def ninthMainNestedSum (N : ℕ) : ℝ :=
  primeOrderedClosedSum N ninthProfileK2 ninthProfileSigma (fun t =>
    primeOrderedClosedSum N ninthProfileSigma (ninthMainTop t) (ninthMainKernel t))

theorem ninthMain_coordinate_mem {N p : ℕ} {A B : ℝ} (hN : 1 < N)
    (hp : p ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ B)) :
    ninthMainCoordinate N p ∈ Set.Icc A B := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) B)).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hl := log_le_log (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) A) hlo
  have hu := log_le_log hp0 hhi
  rw [log_rpow (by linarith : (0 : ℝ) < N)] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hNR)).mpr hl, (div_le_iff₀ (log_pos hNR)).mpr hu⟩

theorem ninthMain_pair_mem {N : ℕ} (hN : 1 < N) {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N (ninthProfileW N) (ninthProfileU N)) :
    t.1 ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma) ∧
      t.2 ∈ primesIcc ((N : ℝ) ^ ninthProfileSigma)
        ((N : ℝ) ^ ninthMainTop (ninthMainCoordinate N t.1)) := by
  obtain ⟨hpair, hau⟩ := mem_filter.mp ht
  obtain ⟨ha, hb, _, hwa, hub, _, hsize⟩ := mem_lowerPairs_source.mp hpair
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have ha0 : (0 : ℝ) < t.1 := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < t.2 := by exact_mod_cast hb.pos
  have hpa : t.1 ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma) :=
    (mem_primesIcc (rpow_nonneg hN0.le _)).mpr ⟨ha, hwa, hau.le⟩
  have hcoord := ninthMain_coordinate_mem hN hpa
  refine ⟨hpa, (mem_primesIcc (rpow_nonneg hN0.le _)).mpr ⟨hb, hub, ?_⟩⟩
  have hsq : (t.1 : ℝ) * t.2 ^ 2 < N := by
    exact_mod_cast (lower_pair_size_iff ha.pos).mpr hsize
  have hlog := log_lt_log (mul_pos ha0 (sq_pos_of_pos hb0)) hsq
  rw [log_mul ha0.ne' (sq_pos_of_pos hb0).ne', log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  apply (log_le_log_iff hb0 (rpow_pos_of_pos hN0 _)).mp
  rw [log_rpow hN0, ninthMainTop, ninthMainClip, min_eq_left hcoord.2]
  unfold ninthMainCoordinate
  have hL : log (N : ℝ) ≠ 0 := (log_pos hNR).ne'
  field_simp
  linarith

theorem ninthMainPairSum_le_nested {N : ℕ} (hN : 1 < N) :
    ninthMainPairSum N ≤ ninthMainNestedSum N := by
  let A := primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma)
  let B := fun a => primesIcc ((N : ℝ) ^ ninthProfileSigma)
    ((N : ℝ) ^ ninthMainTop (ninthMainCoordinate N a))
  let S := ninthPairs N (ninthProfileW N) (ninthProfileU N)
  let i := fun t : ℕ × ℕ => (⟨t.1, t.2⟩ : Sigma (fun _ : ℕ => ℕ))
  let f := fun x : Sigma (fun _ : ℕ => ℕ) =>
    ninthMainKernel (ninthMainCoordinate N x.1) (ninthMainCoordinate N x.2) /
      ((x.1 : ℝ) * x.2)
  have hinj : Set.InjOn i S := by
    intro x _ y _ h
    exact Prod.ext (congrArg Sigma.fst h) (congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) h)
  have hsub : S.image i ⊆ A.sigma B := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
    exact mem_sigma.mpr (ninthMain_pair_mem hN ht)
  have hpos : ∀ x ∈ A.sigma B, 0 ≤ f x := by
    intro x hx
    obtain ⟨ha, hb⟩ := mem_sigma.mp hx
    have hca := ninthMain_coordinate_mem hN ha
    have hp := ninthMain_parameters
    have hca' : ninthMainCoordinate N x.1 ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
      constructor <;> linarith [hca.1, hca.2]
    have hcb := ninthMain_coordinate_mem hN hb
    have htop := ninthMainTop_bounds hca'
    have hcb' : ninthMainCoordinate N x.2 ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
      constructor <;> linarith [hcb.1, hcb.2, htop.2.2]
    exact div_nonneg (ninthMainKernel_bound hca' hcb').1 (by positivity)
  calc
    ninthMainPairSum N = ∑ x ∈ S.image i, f x := by rw [sum_image hinj]; rfl
    _ ≤ ∑ x ∈ A.sigma B, f x :=
      sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hpos x hx)
    _ = ninthMainNestedSum N := by
      rw [sum_sigma]
      unfold ninthMainNestedSum primeOrderedClosedSum
      apply sum_congr rfl
      intro a _
      rw [sum_div]
      apply sum_congr rfl
      intro b _
      dsimp only [f, ninthMainCoordinate]
      rw [div_div, mul_comm (b : ℝ) (a : ℝ)]

/-- Uniformity in the inner function and endpoint comes from the existing
one-dimensional theorem; the outer reciprocal mass stays bounded by five. -/
theorem ninthMainNestedSum_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ninthMainNestedSum N ≤ J9 + ε := by
  let η := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  have hp := ninthMain_parameters
  have hA : 1 / 10 ≤ ninthProfileK2 := hp.1.le
  have hAB : ninthProfileK2 ≤ ninthProfileSigma := hp.2.1.le
  have hB : ninthProfileSigma ≤ 1 / 2 := by linarith
  have hs : ninthProfileSigma ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := ⟨hp.2.2.1.le, hB⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_natCast_atTop_atTop.eventually
      (primeOrdered_weighted_uniform 5 25 η (by norm_num) (by norm_num) hη),
    tendsto_natCast_atTop_atTop.eventually
      (primeOrdered_weighted_uniform 20 125 η (by norm_num) (by norm_num) hη),
    tendsto_natCast_atTop_atTop.eventually (primeOrdered_reciprocal_uniform 1 (by norm_num))]
    with N hN hinner houter hrec
  have hmass : (∑ a ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma),
      1 / (a : ℝ)) ≤ 5 := by
    have h := (abs_lt.mp (hrec _ _ hA hAB hB)).2
    have hi := (primeOrdered_exponent_density_bounds hA hAB hB).2
    linarith
  have hreplace :
      ninthMainNestedSum N ≤
        primeOrderedClosedSum N ninthProfileK2 ninthProfileSigma ninthMainInner + 5 * η := by
    have hsum :
        ninthMainNestedSum N ≤
          ∑ a ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma),
            (ninthMainInner (ninthMainCoordinate N a) + η) / a := by
      unfold ninthMainNestedSum
      rw [primeOrderedClosedSum]
      apply sum_le_sum
      intro a ha
      have hc := ninthMain_coordinate_mem (by omega) ha
      have hc' : ninthMainCoordinate N a ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
        constructor <;> linarith [hc.1, hc.2]
      have ht := ninthMainTop_bounds hc'
      have hq := hinner (ninthMainKernel (ninthMainCoordinate N a))
        ninthProfileSigma (ninthMainTop (ninthMainCoordinate N a))
        (ninthMainKernel_continuous hc')
        (fun v hv => (ninthMainKernel_bound hc' hv).2)
        (fun x hx y hy => ninthMainKernel_lipschitz_second hc' hx hy)
        hs.1 ht.1 ht.2.2
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
      have hh := (abs_lt.mp hq).2
      change _ - ninthMainInner (ninthMainCoordinate N a) < η at hh
      dsimp only [ninthMainCoordinate] at hh ⊢
      linarith
    have he :
        (∑ a ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma),
          (ninthMainInner (ninthMainCoordinate N a) + η) / a) =
          primeOrderedClosedSum N ninthProfileK2 ninthProfileSigma ninthMainInner +
            η * ∑ a ∈ primesIcc ((N : ℝ) ^ ninthProfileK2) ((N : ℝ) ^ ninthProfileSigma),
              1 / (a : ℝ) := by
      simp only [add_div, sum_add_distrib, mul_sum, mul_one_div, primeOrderedClosedSum,
        ninthMainCoordinate]
    rw [he] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hmass hη.le]
  have ho := houter ninthMainInner ninthProfileK2 ninthProfileSigma
    ninthMainInner_continuous ninthMainInner_regular.1 ninthMainInner_regular.2 hA hAB hB
  rw [← J9_eq_iterated] at ho
  have ho' := (abs_lt.mp ho).2
  dsimp only [η] at *
  linarith

theorem ninthMainPairSum_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ninthMainPairSum N ≤ J9 + ε := by
  filter_upwards [ninthMainNestedSum_eventually_le hε, eventually_ge_atTop (2 : ℕ)]
    with N h hN
  exact (ninthMainPairSum_le_nested (by omega)).trans h

end Wu2008DoubleSieve
