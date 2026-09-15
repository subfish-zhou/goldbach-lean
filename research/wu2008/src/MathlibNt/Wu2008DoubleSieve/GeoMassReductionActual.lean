import MathlibNt.Wu2008DoubleSieve.GeoMassReductionRectangle

/-! Original lower rows 3 and 5, and an unchanged-total-M consumer. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass
open Set MeasureTheory
open scoped BigOperators
open SecondFunctionalJointTail

theorem triple_rectangle_mass {a b c d e f : ℝ}
    (ha : 0 < a) (hc : 0 < c) (he : 0 < e)
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) :
    geometricMass 1 (continuousRectangle ![a,c,e] ![b,d,f]) =
      Real.log (b/a) * (1/c - 1/d) * Real.log (f/e) := by
  have hA : ∀ i : Fin 3, 0 < (![a,c,e] : Fin 3 → ℝ) i := by
    simpa only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ] using And.intro ha (And.intro hc he)
  have hAB : ∀ i : Fin 3, (![a,c,e] : Fin 3 → ℝ) i ≤ (![b,d,f] : Fin 3 → ℝ) i := by
    simpa only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      Matrix.cons_val_zero, Matrix.cons_val_succ] using And.intro hab (And.intro hcd hef)
  rw [rectangle_mass 1 _ _ hA hAB]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (if (0 : Fin 3) = 1 then 1/a - 1/b else Real.log (b/a)) *
    ((if (1 : Fin 3) = 1 then 1/c - 1/d else Real.log (d/c)) *
    (if (2 : Fin 3) = 1 then 1/e - 1/f else Real.log (f/e))) = _
  rw [if_neg (by decide), if_pos rfl, if_neg (by decide)]
  ring

/-- The weak order is already forced by these closed colour windows. -/
theorem lower_domain_three (a b c e f : ℝ) :
    LowerTripleContinuous.D a b c e f 3 = continuousRectangle ![a,b,c] ![b,c,f] := by
  ext t
  rw [(LowerTripleContinuous.D_six_literal a b c e f).2.2.2.1]
  simp only [mem_ofPred_eq, continuousRectangle, mem_pi, mem_univ, forall_const,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,_,_⟩
    exact ⟨⟨h0,h1⟩,⟨h2,h3⟩,⟨h4,h5⟩⟩
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩,⟨h4,h5⟩⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h1.trans h2,h3.trans h4⟩

theorem lower_domain_five (a b c e f : ℝ) :
    LowerTripleContinuous.D a b c e f 5 = continuousRectangle ![b,c,e] ![c,e,f] := by
  ext t
  rw [(LowerTripleContinuous.D_six_literal a b c e f).2.2.2.2.2]
  simp only [mem_ofPred_eq, continuousRectangle, mem_pi, mem_univ, forall_const,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,_,_⟩
    exact ⟨⟨h0,h1⟩,⟨h2,h3⟩,⟨h4,h5⟩⟩
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩,⟨h4,h5⟩⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h1.trans h2,h3.trans h4⟩

/-- A literal original three-dimensional geometric mass, not a supplied formula. -/
theorem lower_three_exact {a b c e f : ℝ}
    (hp : LowerTripleContinuous.CompactParameters a b c e f) :
    geometricMass 1 (LowerTripleContinuous.D a b c e f 3) =
      Real.log (b/a) * (1/b - 1/c) * Real.log (f/c) := by
  rcases hp with ⟨ha,hab,hbc,hce,hef,_hf⟩
  have ha0 : 0 < a := by linarith
  rw [lower_domain_three]
  exact triple_rectangle_mass ha0 (ha0.trans_le hab) (ha0.trans_le (hab.trans hbc))
    hab hbc (hce.trans hef)

theorem lower_five_exact {a b c e f : ℝ}
    (hp : LowerTripleContinuous.CompactParameters a b c e f) :
    geometricMass 1 (LowerTripleContinuous.D a b c e f 5) =
      Real.log (c/b) * (1/c - 1/e) * Real.log (f/e) := by
  rcases hp with ⟨ha,hab,hbc,hce,hef,_hf⟩
  have hb0 : 0 < b := by linarith
  rw [lower_domain_five]
  exact triple_rectangle_mass hb0 (hb0.trans_le hbc) (hb0.trans_le (hbc.trans hce))
    hbc hce hef

noncomputable def lowerThreeLog (p : SecondFunctionalParameters) : ℝ :=
  Real.log ((1/p.kappa1)/(1/p.S)) * (1/(1/p.kappa1) - 1/(1/p.kappa2)) *
    Real.log ((1/p.s)/(1/p.kappa2))

noncomputable def lowerFiveLog (p : SecondFunctionalParameters) : ℝ :=
  Real.log ((1/p.kappa2)/(1/p.kappa1)) * (1/(1/p.kappa2) - 1/(1/p.kappa3)) *
    Real.log ((1/p.s)/(1/p.kappa3))

theorem lowerMass_three (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : lowerMass p 3 = lowerThreeLog p :=
  lower_three_exact (LowerTripleContinuous.mother_compact_parameters p hp hs)

theorem lowerMass_five (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : lowerMass p 5 = lowerFiveLog p :=
  lower_five_exact (LowerTripleContinuous.mother_compact_parameters p hp hs)

/-- The original M with precisely two rows evaluated; all other masses remain literal. -/
theorem M_two_rows_exact (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    SecondFunctionalJointTail.M p = (lowerMass p 0 + lowerMass p 1 + lowerMass p 2 + lowerThreeLog p +
      lowerMass p 4 + lowerFiveLog p) +
      ((highMass20 p + highMass21 p) + ∑ j : Fin 4, fourMass p j) := by
  unfold SecondFunctionalJointTail.M
  congr 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change lowerMass p 0 + (lowerMass p 1 + (lowerMass p 2 + (lowerMass p 3 +
    (lowerMass p 4 + lowerMass p 5)))) = _
  rw [lowerMass_three p hp hs, lowerMass_five p hp hs]
  ring

/-- Actual weighted integrability accompanies both identities. -/
theorem two_rows_integrable (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    IntegrableOn (geometricWeight 1) (LowerTripleContinuous.D (1/p.S) (1/p.kappa1)
      (1/p.kappa2) (1/p.kappa3) (1/p.s) 3) ∧
    IntegrableOn (geometricWeight 1) (LowerTripleContinuous.D (1/p.S) (1/p.kappa1)
      (1/p.kappa2) (1/p.kappa3) (1/p.s) 5) :=
  ⟨(mother_mass_integrable p hp hs).1 3, (mother_mass_integrable p hp hs).1 5⟩

end Wu2008DoubleSieve.SecondFunctionalGeometricMass
