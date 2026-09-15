import MathlibNt.Wu2008DoubleSieve.SeventhEighthPairKernel

namespace Wu2008DoubleSieve.SeventhEighth
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def pairNested (N : ℕ) (A : ℝ) (l : ℝ → ℝ) : ℝ :=
  primeOrderedClosedSum N A (1 / 3) (fun t =>
    primeOrderedClosedSum N (l t) (pairTop t) (pairKernel t))

theorem pair_low_density_bound {A : ℝ} (hA : 1 / 15 ≤ A) (hAB : A ≤ 1 / 3) :
    (∫ t in A..(1 / 3 : ℝ), 1 / t) ≤ 4 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := A) (b := (1 / 3 : ℝ)) (C := 15) (f := fun t : ℝ => 1 / t) (by
      intro t ht
      rw [uIoc_of_le hAB] at ht
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr ht0.le)]
      exact (div_le_iff₀ ht0).mpr (by linarith [ht.1]))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hAB)] at h
  have hh := (le_abs_self _).trans h
  linarith

/-- Two genuinely uniform quadratures. The whole outer prime mass is paid,
not an error relative to the width of a possibly collapsed slice. -/
theorem pairNested_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : ℝ) (l : ℝ → ℝ),
      1 / 15 ≤ A → A ≤ 1 / 3 →
      (∀ t ∈ Icc (1 / 15 : ℝ) (1 / 3),
        l t ∈ Icc (1 / 10 : ℝ) (1 / 2) ∧ l t ≤ pairTop t) →
      (∀ x ∈ Icc (1 / 15 : ℝ) (1 / 3), ∀ y ∈ Icc (1 / 15 : ℝ) (1 / 3),
        |l x - l y| ≤ |x - y|) →
      pairNested N A l ≤ (∫ t in A..(1 / 3), pairInner l t / t) + ε := by
  let η := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨To, _, hTo⟩ := classical_low_weighted_uniform 20 300 η (by norm_num) (by norm_num) hη
  obtain ⟨Tm, _, hTm⟩ := classical_low_weighted_uniform 1 0 1 (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop To, eventually_ge_atTop Tm,
    eventually_ge_atTop (2 : ℕ), tendsto_natCast_atTop_atTop.eventually
      (primeOrdered_weighted_uniform 5 25 η (by norm_num) (by norm_num) hη)]
    with N hNo hNm hN hinner
  intro A l hA hAB hb hl
  have hlb := fun t ht => (hb t ht).1
  have hmass : (∑ a ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ)),
      1 / (a : ℝ)) ≤ 5 := by
    have h := hTm N hNm (fun _ => 1) A (1 / 3) continuousOn_const
      (by intro t _; norm_num) (by intro x _ y _; simp) hA hAB le_rfl
    have hh := (abs_lt.mp h).2
    change (∑ a ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ)),
      1 / (a : ℝ)) - (∫ t in A..(1 / 3), 1 / t) < 1 at hh
    linarith [pair_low_density_bound hA hAB]
  have hreplace : pairNested N A l ≤
      primeOrderedClosedSum N A (1 / 3) (pairInner l) + 5 * η := by
    have hsum : pairNested N A l ≤
        ∑ a ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ)),
          (pairInner l (ninthMainCoordinate N a) + η) / a := by
      unfold pairNested
      rw [primeOrderedClosedSum]
      apply sum_le_sum
      intro a ha
      have hc := ninthMain_coordinate_mem (by omega) ha
      have hc' : ninthMainCoordinate N a ∈ Icc (1 / 15 : ℝ) (1 / 3) :=
        ⟨hA.trans hc.1, hc.2⟩
      have hq := hinner (pairKernel (ninthMainCoordinate N a))
        (l (ninthMainCoordinate N a)) (pairTop (ninthMainCoordinate N a))
        (pairKernel_continuous hc') (fun v _ => (pairKernel_bound hc' v).2)
        (fun x _ y _ => pairKernel_lipschitz_second hc' x y)
        (hb _ hc').1.1 (hb _ hc').2 (pairTop_bounds hc').2
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
      have hh := (abs_lt.mp hq).2
      change _ - pairInner l (ninthMainCoordinate N a) < η at hh
      dsimp only [ninthMainCoordinate] at hh ⊢
      linarith
    have he : (∑ a ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ)),
        (pairInner l (ninthMainCoordinate N a) + η) / a) =
        primeOrderedClosedSum N A (1 / 3) (pairInner l) +
        η * ∑ a ∈ primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ)), 1 / (a : ℝ) := by
      simp only [add_div, sum_add_distrib, mul_sum, mul_one_div, primeOrderedClosedSum,
        ninthMainCoordinate]
    rw [he] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hmass hη.le]
  have ho := hTo N hNo (pairInner l) A (1 / 3) (pairInner_continuous l hlb hl)
    (pairInner_regular l hlb hl).1 (pairInner_regular l hlb hl).2 hA hAB le_rfl
  have ho' := (abs_lt.mp ho).2
  dsimp only [η] at *
  linarith

/-- Converse log-coordinate membership, with closed endpoints retained. -/
theorem pair_prime_mem {N p : ℕ} {a b : ℝ} (hN : 1 < N) (hp : p.Prime)
    (hc : ninthMainCoordinate N p ∈ Icc a b) :
    p ∈ primesIcc ((N : ℝ) ^ a) ((N : ℝ) ^ b) := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine (mem_primesIcc (rpow_nonneg hN0.le b)).mpr ⟨hp, ?_, ?_⟩
  · apply (log_le_log_iff (rpow_pos_of_pos hN0 a) hp0).mp
    rw [log_rpow hN0]
    exact (le_div_iff₀ (log_pos hNR)).mp hc.1
  · apply (log_le_log_iff hp0 (rpow_pos_of_pos hN0 b)).mp
    rw [log_rpow hN0]
    exact (div_le_iff₀ (log_pos hNR)).mp hc.2

/-- Literal pair injection into a dependent closed rectangle sum.
The added terms are nonnegative and no strict-face atom is discarded. -/
theorem classicalPairSum_le_pairNested {N : ℕ} (hN : 1 < N)
    (S : Finset (ℕ × ℕ)) (A : ℝ) (l : ℝ → ℝ) (hA : 1 / 15 ≤ A)
    (hS : ∀ p ∈ S, p.1.Prime ∧ p.2.Prime ∧
      ninthMainCoordinate N p.1 ∈ Icc A (1 / 3) ∧
      ninthMainCoordinate N p.2 ∈ Icc (l (ninthMainCoordinate N p.1))
        (pairTop (ninthMainCoordinate N p.1))) :
    classicalPairSum N S ≤ pairNested N A l := by
  let Aset := primesIcc ((N : ℝ) ^ A) ((N : ℝ) ^ (1 / 3 : ℝ))
  let B := fun a => primesIcc ((N : ℝ) ^ (l (ninthMainCoordinate N a)))
    ((N : ℝ) ^ pairTop (ninthMainCoordinate N a))
  let i := fun p : ℕ × ℕ => (⟨p.1, p.2⟩ : Sigma (fun _ : ℕ => ℕ))
  let f := fun x : Sigma (fun _ : ℕ => ℕ) =>
    pairKernel (ninthMainCoordinate N x.1) (ninthMainCoordinate N x.2) / ((x.1 : ℝ) * x.2)
  have hinj : Set.InjOn i S := by
    intro x _ y _ h
    exact Prod.ext (congrArg Sigma.fst h) (congrArg (fun z : Sigma (fun _ : ℕ => ℕ) => z.2) h)
  have hsub : S.image i ⊆ Aset.sigma B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨ha, hb, hca, hcb⟩ := hS p hp
    exact mem_sigma.mpr ⟨pair_prime_mem hN ha hca, pair_prime_mem hN hb hcb⟩
  have hpos : ∀ x ∈ Aset.sigma B, 0 ≤ f x := by
    intro x hx
    obtain ⟨ha, _⟩ := mem_sigma.mp hx
    have hc := ninthMain_coordinate_mem hN ha
    exact div_nonneg (pairKernel_bound ⟨hA.trans hc.1, hc.2⟩ _).1 (by positivity)
  calc
    classicalPairSum N S = ∑ x ∈ S.image i, f x := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro p hp
      obtain ⟨_, _, _, hcb⟩ := hS p hp
      dsimp only [f, i, pairKernel]
      rw [min_eq_left hcb.2]
    _ ≤ ∑ x ∈ Aset.sigma B, f x :=
      sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hpos x hx)
    _ = pairNested N A l := by
      rw [sum_sigma]
      unfold pairNested primeOrderedClosedSum
      apply sum_congr rfl
      intro a _
      rw [sum_div]
      apply sum_congr rfl
      intro b _
      dsimp only [f, ninthMainCoordinate]
      rw [div_div, mul_comm (b : ℝ) (a : ℝ)]

theorem seventhPairSum_le_nested {N : ℕ} (hN : 512 ≤ N) :
    classicalPairSum N (seventhPairs N) ≤ pairNested N sigma pairLower7 := by
  apply classicalPairSum_le_pairNested (by omega) _ _ _ (by norm_num [sigma, alpha])
  intro p hp
  obtain ⟨ha, hb, _⟩ := seventh_classicalPairGeometry hN p hp
  obtain ⟨hl, hu, hab, hv⟩ := seventh_pair_log_domain (by omega) hp
  refine ⟨ha, hb, ⟨hl, hu.le⟩, ?_, hv.le⟩
  change max (ninthMainCoordinate N p.1) (1 / 10) ≤ ninthMainCoordinate N p.2
  apply max_le hab.le
  have hs : (1 / 10 : ℝ) ≤ sigma := by norm_num [sigma, alpha]
  exact hs.trans (hl.trans hab.le)

theorem eighthPairSum_le_nested {N : ℕ} (hN : 512 ≤ N) :
    classicalPairSum N (eighthPairs N) ≤ pairNested N alpha pairLower8 := by
  apply classicalPairSum_le_pairNested (by omega) _ _ _ (by norm_num [alpha])
  intro p hp
  obtain ⟨ha, hb, _⟩ := eighth_classicalPairGeometry hN p hp
  obtain ⟨hl, hu, hv, htop⟩ := eighth_pair_log_domain (by omega) hp
  exact ⟨ha, hb, ⟨hl, hu.le⟩, hv, htop.le⟩

/-- The actual two families, a single threshold before N, no target hypotheses. -/
theorem seventh_eighth_pairSum_le_J_add_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      classicalPairSum N (seventhPairs N) ≤ J7 + ε ∧
      classicalPairSum N (eighthPairs N) ≤ J8 + ε := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (pairNested_eventually_le hε)
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN
  have h512 : 512 ≤ N := (le_max_right _ _).trans hN
  have h := hT N ((le_max_left _ _).trans hN)
  have h7 := h sigma pairLower7 (by norm_num [sigma, alpha]) classical_parameters.2.2.le
    (fun t ht => pairLower7_bounds ht) (fun x _ y _ => pairLower7_lipschitz x y)
  have h8 := h alpha pairLower8 (by norm_num [alpha])
    (classical_parameters.2.1.le.trans classical_parameters.2.2.le)
    (fun t ht => pairLower8_bounds ht) (fun x _ y _ => pairLower8_lipschitz x y)
  rw [← J7_eq_pairInner] at h7
  rw [← J8_eq_pairInner] at h8
  exact ⟨(seventhPairSum_le_nested h512).trans h7, (eighthPairSum_le_nested h512).trans h8⟩

end Wu2008DoubleSieve.SeventhEighth
