import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGrouped

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset
open scoped Classical

/-- Independent six-band dictionary: the entries are pLo,pHi,qLo,qHi,rLo,rHi. -/
noncomputable def bands (a b c e f : ℝ) (j : Fin 6) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  ![(b,c,b,c,c,f), (b,c,c,e,c,e), (a,b,a,b,e,f),
    (a,b,b,c,c,f), (a,b,c,f,c,f), (b,c,c,e,e,f)] j

noncomputable def actualBands (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  bands (wuLocalCutoff N δ d P.S) (wuLocalCutoff N δ d P.kappa1)
    (wuLocalCutoff N δ d P.kappa2) (wuLocalCutoff N δ d P.kappa3)
    (wuLocalCutoff N δ d P.s) j

noncomputable def actualPre (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d p q : ℕ) : Prop :=
  (actualBands N δ P j d).1 ≤ (p : ℝ) ∧ (p : ℝ) < (actualBands N δ P j d).2.1 ∧
  (actualBands N δ P j d).2.2.1 ≤ (q : ℝ) ∧ (q : ℝ) < (actualBands N δ P j d).2.2.2.1

noncomputable def sourceFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : LabelledPhysical.Family Label N :=
  family N (convolutionWuWindows N Δ V) (fun d => wuLocalCutoff N δ d P.S)
    (fun d => wuLocalCutoff N δ d P.s) (fun d => (actualBands N δ P j d).2.2.2.2.1)
    (fun d => (actualBands N δ P j d).2.2.2.2.2) (actualPre N δ P j)
    (fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd)

noncomputable def actualSourceMass {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  sourceMass N (convolutionWuWindows N Δ V) (fun d => wuLocalCutoff N δ d P.S)
    (fun d => wuLocalCutoff N δ d P.s) (fun d => (actualBands N δ P j d).2.2.2.2.1)
    (fun d => (actualBands N δ P j d).2.2.2.2.2) (actualPre N δ P j)

structure PhysicalGeometry (N : ℕ) (η : ℝ) (L : LabelledPhysical.Family Label N)
    (x : Label) : Prop where
  positive : 0 < L.cofactor x
  le_N : L.cofactor x ≤ N
  power_lower : (N : ℝ)^η ≤ L.cofactor x
  power_upper : (L.cofactor x : ℝ) ≤ (N : ℝ)^(1-η)
  lower_two : 2 ≤ L.lower x
  lower_large : (N : ℝ)^η ≤ L.lower x
  feasible : L.lower x ≤ L.upper x
  physical : (L.cofactor x : ℝ) * L.upper x ≤ N

/-- Geometry of every raw label, not inferred from existence of a prime output. -/
theorem source_geometry {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) (j : Fin 6) {x : Label}
    (hx : x ∈ (sourceFamily N δ Δ V P j).labels) :
    PhysicalGeometry N (wuLocalExponent k δ / 10) (sourceFamily N δ Δ V P j) x := by
  obtain ⟨hd,_,hq,_⟩ := (mem_labels x).mp hx
  have hlarge := HighNonunit.mother_window_lower hN hδ hδhi hb P hP hd hq
  have hg := (sourceFamily N δ Δ V P j).geometry x hx
  have hpos : 0 < cofactor x := hg.1
  have hqu : (x.2.2.1 : ℝ) ≤ (sourceFamily N δ Δ V P j).upper x :=
    (le_max_left _ _).trans hg.2.2.1
  have hcap : cofactor x * x.2.2.1 ≤ N := by
    exact_mod_cast (mul_le_mul_of_nonneg_left hqu (Nat.cast_nonneg (cofactor x))).trans hg.2.2.2
  have hle : cofactor x ≤ N :=
    (Nat.le_mul_of_pos_right _ hlarge.1.pos).trans hcap
  have hpow : (N : ℝ)^(wuLocalExponent k δ / 10) ≤ cofactor x :=
    hlarge.2.trans (by exact_mod_cast Nat.le_of_dvd hpos (cofactor_divisors x).2.2)
  exact ⟨hpos,hle,hpow,omega3_cofactor_power_gap (by omega) hlarge.2 hcap,
    hg.2.1,hlarge.2.trans (le_max_left _ _),hg.2.2.1,hg.2.2.2⟩

/-- All source-family labels retain n≥1 and the full residual E-mask. -/
theorem source_mask {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (P : SecondFunctionalParameters) (j : Fin 6) {x : Label}
    (hx : x ∈ (sourceFamily N δ Δ V P j).labels) :
    0 < x.2.2.2 ∧ Sifted (x.1*x.2.1*N) (cofactor x) x.2.2.1 := by
  obtain ⟨_,_,_,_,_,_,hn,hs,_⟩ := (mem_labels x).mp hx
  exact ⟨hn,hs⟩

theorem source_fixedE {i N E : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (P : SecondFunctionalParameters) (j : Fin 6) {x : Label}
    (hx : x ∈ (sourceFamily N δ Δ V P j).labels) (hE : cofactor x = E) :
    0 < E ∧ x.1 ∣ E ∧ x.2.1 ∣ E ∧ x.2.2.1 ∣ E ∧
      E/(x.1*x.2.1*x.2.2.1) = x.2.2.2 := by
  have hp : 0 < cofactor x := ((sourceFamily N δ Δ V P j).geometry x hx).1
  have hd := cofactor_divisors x
  have hn := recover_n hp
  rw [hE] at hp hd hn
  exact ⟨hp,hd.1,hd.2.1,hd.2.2,hn⟩

theorem gamma10_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 10 =
      actualSourceMass N δ Δ V P 0 := by
  rw [secondFunctionalMother_gamma10_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

theorem gamma11_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 11 =
      actualSourceMass N δ Δ V P 1 := by
  rw [secondFunctionalMother_gamma11_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

theorem gamma12_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 12 =
      actualSourceMass N δ Δ V P 2 := by
  rw [secondFunctionalMother_gamma12_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

theorem gamma13_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 13 =
      actualSourceMass N δ Δ V P 3 := by
  rw [secondFunctionalMother_gamma13_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

theorem gamma14_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 14 =
      actualSourceMass N δ Δ V P 4 := by
  rw [secondFunctionalMother_gamma14_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

theorem gamma15_dictionary {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 15 =
      actualSourceMass N δ Δ V P 5 := by
  rw [secondFunctionalMother_gamma15_weighted_ordered_source P hP hN hδ hδhi hb]
  simp [actualSourceMass, sourceMass, actualPre, actualBands, bands, and_assoc]

/-- Each independent source is bounded by its own wide physical family; not an exact envelope identity. -/
theorem actual_source_upper {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (P : SecondFunctionalParameters) (j : Fin 6) :
    actualSourceMass N δ Δ V P j ≤ (sourceFamily N δ Δ V P j).primeMass :=
  source_upper _ hN he

theorem gamma10_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 10 ≤
      (sourceFamily N δ Δ V P 0).primeMass := by
  rw [gamma10_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 0

theorem gamma11_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 11 ≤
      (sourceFamily N δ Δ V P 1).primeMass := by
  rw [gamma11_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 1

theorem gamma12_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 12 ≤
      (sourceFamily N δ Δ V P 2).primeMass := by
  rw [gamma12_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 2

theorem gamma13_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 13 ≤
      (sourceFamily N δ Δ V P 3).primeMass := by
  rw [gamma13_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 3

theorem gamma14_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 14 ≤
      (sourceFamily N δ Δ V P 4).primeMass := by
  rw [gamma14_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 4

theorem gamma15_source_upper {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (he : Even N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) :
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) 15 ≤
      (sourceFamily N δ Δ V P 5).primeMass := by
  rw [gamma15_dictionary (by omega) hδ hδhi hb P hP]
  exact actual_source_upper hN he P 5

end Wu2008DoubleSieve.LowerTripleGrouped
