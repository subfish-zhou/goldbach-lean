import MathlibNt.Wu2008DoubleSieve.GeoMassOriginalBlocksCore

namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
open Set MeasureTheory
open SecondFunctionalJointTail

/-- Endpoints and adjacent weak order determine a closed ordered block. -/
theorem ordered_endpoints {n : ℕ} (a b : ℝ) (t : Fin (n+1) → ℝ) :
    t ∈ orderedDomain (n+1) a b ↔ a ≤ t 0 ∧ Monotone t ∧ t (Fin.last n) ≤ b := by
  constructor
  · rintro ⟨hb, hm⟩
    exact ⟨(hb 0).1, hm, (hb (Fin.last n)).2⟩
  · rintro ⟨ha, hm, hb⟩
    exact ⟨fun i => ⟨ha.trans (hm (Fin.zero_le i)), (hm (Fin.le_last i)).trans hb⟩, hm⟩

theorem lower_zero_domain (a b c e f : ℝ) :
    join 2 1 ⁻¹' LowerTripleContinuous.D a b c e f 0 =
      orderedDomain 2 b c ×ˢ orderedDomain 1 c f := by
  ext z
  rw [(LowerTripleContinuous.D_six_literal a b c e f).1]
  simp only [mem_preimage, mem_ofPred_eq, join_apply, mem_prod, ordered_endpoints,
    Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0,h6,h3⟩,h4,h5⟩
  · rintro ⟨⟨h0,h1,h2⟩,h3,h4⟩
    exact ⟨h0,h1.trans h2,h0.trans h1,h2,h3,h4,h1,h2.trans h3⟩

theorem lower_one_domain (a b c e f : ℝ) :
    join 1 2 ⁻¹' LowerTripleContinuous.D a b c e f 1 =
      orderedDomain 1 b c ×ˢ orderedDomain 2 c e := by
  ext z
  rw [(LowerTripleContinuous.D_six_literal a b c e f).2.1]
  simp only [mem_preimage, mem_ofPred_eq, join_apply, mem_prod, ordered_endpoints,
    Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0,h1⟩,h2,h7,h5⟩
  · rintro ⟨⟨h0,h1⟩,h2,h3,h4⟩
    exact ⟨h0,h1,h2,h3.trans h4,h2.trans h3,h4,h1.trans h2,h3⟩

theorem lower_two_domain (a b c e f : ℝ) (hbe : b ≤ e) :
    join 2 1 ⁻¹' LowerTripleContinuous.D a b c e f 2 =
      orderedDomain 2 a b ×ˢ orderedDomain 1 e f := by
  ext z
  rw [(LowerTripleContinuous.D_six_literal a b c e f).2.2.1]
  simp only [mem_preimage, mem_ofPred_eq, join_apply, mem_prod, ordered_endpoints,
    Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0,h6,h3⟩,h4,h5⟩
  · rintro ⟨⟨h0,h1,h2⟩,h3,h4⟩
    exact ⟨h0,h1.trans h2,h0.trans h1,h2,h3,h4,h1,h2.trans (hbe.trans h3)⟩

theorem lower_four_domain (a b c e f : ℝ) (hbc : b ≤ c) :
    join 1 2 ⁻¹' LowerTripleContinuous.D a b c e f 4 =
      orderedDomain 1 a b ×ˢ orderedDomain 2 c f := by
  ext z
  rw [(LowerTripleContinuous.D_six_literal a b c e f).2.2.2.2.1]
  simp only [mem_preimage, mem_ofPred_eq, join_apply, mem_prod, ordered_endpoints,
    Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨⟨h0,h1⟩,h2,h7,h5⟩
  · rintro ⟨⟨h0,h1⟩,h2,h3,h4⟩
    exact ⟨h0,h1,h2,h3.trans h4,h2.trans h3,h4,h1.trans (hbc.trans h2),h3⟩

theorem high_twenty_domain (c e f : ℝ) :
    join 1 4 ⁻¹' massDomain20 c e f = orderedDomain 1 c e ×ˢ orderedDomain 4 e f := by
  ext z
  simp only [mem_preimage, massDomain20, mem_ofPred_eq, join_apply, mem_prod,
    ordered_endpoints, Fin.monotone_iff_le_succ, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  constructor
  · rintro ⟨h0,h1,h2,⟨h3,h4,h5,h6⟩,h7⟩
    exact ⟨⟨h0,h1⟩,h2,⟨h4,h5,h6⟩,h7⟩
  · rintro ⟨⟨h0,h1⟩,h2,⟨h3,h4,h5⟩,h6⟩
    exact ⟨h0,h1,h2,⟨h1.trans h2,h3,h4,h5⟩,h6⟩

theorem high_twenty_one_domain (e f : ℝ) : massDomain21 e f = orderedDomain 6 e f := by
  ext t
  exact (ordered_endpoints e f t).symm

theorem four_sixteen_domain (c e : ℝ) : FourPrimeContinuous.D16 c e = orderedDomain 4 c e := by
  ext t
  simp only [FourPrimeContinuous.D16, mem_ofPred_eq, ordered_endpoints,
    Fin.monotone_iff_le_succ, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  dsimp
  simp only [and_assoc]

theorem four_seventeen_domain (c e f : ℝ) :
    join 3 1 ⁻¹' FourPrimeContinuous.D17 c e f =
      orderedDomain 3 c e ×ˢ orderedDomain 1 e f := by
  ext z
  simp only [mem_preimage, FourPrimeContinuous.D17, mem_ofPred_eq, join_apply,
    mem_prod, ordered_endpoints, Fin.monotone_iff_le_succ, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, true_and]
  dsimp [Fin.append, Fin.addCases]
  simp only [and_assoc]
  rfl

theorem four_eighteen_domain (c e f : ℝ) :
    join 2 2 ⁻¹' FourPrimeContinuous.D18 c e f =
      orderedDomain 2 c e ×ˢ orderedDomain 2 e f := by
  ext z
  simp only [mem_preimage, FourPrimeContinuous.D18, mem_ofPred_eq, join_apply,
    mem_prod, ordered_endpoints, Fin.monotone_iff_le_succ, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp [Fin.append, Fin.addCases]
  simp only [and_assoc]

/-- The original D19 includes c ≤ e, which must not be silently dropped. -/
theorem four_nineteen_domain (b c e f : ℝ) (hce : c ≤ e) :
    join 1 3 ⁻¹' FourPrimeContinuous.D19 b c e f =
      orderedDomain 1 b c ×ˢ orderedDomain 3 e f := by
  ext z
  simp only [mem_preimage, FourPrimeContinuous.D19, mem_ofPred_eq, join_apply,
    mem_prod, ordered_endpoints, Fin.monotone_iff_le_succ, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, true_and, hce]
  dsimp [Fin.append, Fin.addCases]
  simp only [and_assoc]

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.OriginalBlocks
