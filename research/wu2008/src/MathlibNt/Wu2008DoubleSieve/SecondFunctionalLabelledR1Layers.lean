import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledPhysicalSieve

/-! Modulus-independent complete cofactor layers for arbitrary physical labels. -/
namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset
open scoped Classical
variable {α : Type*} {N : ℕ}

def layerFibre (L : Family α N) (e : ℕ) :
    Finset α :=
  L.labels.filter fun c => L.cofactor c = e

noncomputable def layerRank (L : Family α N) (e B : ℕ)
    (hB : (layerFibre L e).card ≤ B) :
    ↥(layerFibre L e) → Fin B :=
  fun c => Fin.castLE (by simpa only [Fintype.card_coe] using hB)
    (Fintype.equivFin ↥(layerFibre L e) c)

theorem layerRank_injective (L : Family α N) (e B : ℕ)
    (hB : (layerFibre L e).card ≤ B) :
    Function.Injective (layerRank L e B hB) := by
  intro a b hab
  apply (Fintype.equivFin ↥(layerFibre L e)).injective
  apply Fin.ext
  exact congrArg (fun x : Fin B => x.val) hab

noncomputable def layerSupport (L : Family α N) (j : ℕ) :
    Finset ℕ :=
  (L.labels.image L.cofactor).filter fun e => j < (layerFibre L e).card

noncomputable def layerLabel (L : Family α N) (c₀ : α) (j e : ℕ) :
    α :=
  if hj : j < (layerFibre L e).card then
    ((Fintype.equivFin ↥(layerFibre L e)).symm
      ⟨j, by simpa only [Fintype.card_coe] using hj⟩).val
  else c₀

theorem layerLabel_mem_fibre {L : Family α N} (c₀ : α) {j e : ℕ}
    (hj : j < (layerFibre L e).card) :
    layerLabel L c₀ j e ∈ layerFibre L e := by
  simp only [layerLabel, dif_pos hj]
  exact Subtype.property _

theorem layerLabel_mem {L : Family α N} (c₀ : α) {j e : ℕ}
    (he : e ∈ layerSupport L j) :
    layerLabel L c₀ j e ∈ L.labels ∧ L.cofactor (layerLabel L c₀ j e) = e :=
  mem_filter.mp (layerLabel_mem_fibre c₀ (mem_filter.mp he).2)

theorem layerLabel_rank {L : Family α N} (c₀ : α) {e B : ℕ}
    (hB : (layerFibre L e).card ≤ B) (c : ↥(layerFibre L e)) :
    layerLabel L c₀ (layerRank L e B hB c).val e = c.val := by
  have hc : (layerRank L e B hB c).val < (layerFibre L e).card := by
    simpa only [layerRank, Fin.val_castLE, Fintype.card_coe] using
      (Fintype.equivFin ↥(layerFibre L e) c).isLt
  rw [layerLabel, dif_pos hc]
  change ((Fintype.equivFin ↥(layerFibre L e)).symm
    (Fintype.equivFin ↥(layerFibre L e) c)).val = c.val
  exact congrArg Subtype.val
    ((Fintype.equivFin ↥(layerFibre L e)).symm_apply_apply c)

/-- Exact fibre enumeration, padded by zero up to the common layer bound. -/
theorem layer_fibre_sum (L : Family α N) (c₀ : α) (e B : ℕ)
    (hB : (layerFibre L e).card ≤ B) (F : α → ℝ) :
    (∑ c ∈ layerFibre L e, F c) =
      ∑ j ∈ range B, if j < (layerFibre L e).card
        then F (layerLabel L c₀ j e) else 0 := by
  rw [← sum_filter]
  rw [← sum_attach]
  apply sum_bij (fun c _ => (layerRank L e B hB c).val)
  · intro c _
    exact mem_filter.mpr ⟨mem_range.mpr (layerRank L e B hB c).isLt, by
      simpa only [layerRank, Fin.val_castLE, Fintype.card_coe] using
        (Fintype.equivFin ↥(layerFibre L e) c).isLt⟩
  · intro a _ b _ hab
    exact layerRank_injective L e B hB (Fin.ext hab)
  · intro j hj
    obtain ⟨_, hj⟩ := mem_filter.mp hj
    refine ⟨(Fintype.equivFin ↥(layerFibre L e)).symm
      ⟨j, by simpa only [Fintype.card_coe] using hj⟩, mem_attach _ _, ?_⟩
    simp only [layerRank, Equiv.apply_symm_apply, Fin.val_castLE]
  · intro c _
    rw [layerLabel_rank]

/-- One common finite partition gives equality for every test simultaneously.
In particular an AP modulus may occur in F, but not in any layer choice. -/
theorem layer_sum (L : Family α N) (c₀ : α) (B : ℕ)
    (hB : ∀ e, (layerFibre L e).card ≤ B) (F : α → ℝ) :
    (∑ c ∈ L.labels, F c) =
      ∑ j ∈ range B, ∑ e ∈ layerSupport L j, F (layerLabel L c₀ j e) := by
  calc
    (∑ c ∈ L.labels, F c) =
        ∑ e ∈ L.labels.image L.cofactor, ∑ c ∈ layerFibre L e, F c :=
      (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) F).symm
    _ = ∑ e ∈ L.labels.image L.cofactor, ∑ j ∈ range B,
        if j < (layerFibre L e).card then F (layerLabel L c₀ j e) else 0 := by
      apply sum_congr rfl
      intro e _
      exact layer_fibre_sum L c₀ e B (hB e) F
    _ = _ := by
      rw [sum_comm]
      simp only [layerSupport, sum_filter]


/-- Exact original-weight reconstruction for every profile-dependent test. -/
theorem layer_weighted_sum (L : Family α N) (c₀ : α) (B : ℕ)
    (hB : ∀ e, (L.layerFibre e).card ≤ B) (F : α → ℝ) :
    (∑ c ∈ L.labels, L.weight c * F c) =
      ∑ j ∈ range B, ∑ e ∈ L.layerSupport j,
        L.weight (L.layerLabel c₀ j e) * F (L.layerLabel c₀ j e) :=
  L.layer_sum c₀ B hB (fun c => L.weight c * F c)

/-- Coprimality is only a restriction on the test, never on the enumeration. -/
theorem layer_coprime_sum (L : Family α N) (c₀ : α) (B : ℕ)
    (hB : ∀ e, (L.layerFibre e).card ≤ B) (q : ℕ) (F : α → ℝ) :
    (∑ c ∈ L.labels.filter (fun c => (L.cofactor c).Coprime q), L.weight c * F c) =
      ∑ j ∈ range B, ∑ e ∈ (L.layerSupport j).filter (fun e => e.Coprime q),
        L.weight (L.layerLabel c₀ j e) * F (L.layerLabel c₀ j e) := by
  have h := L.layer_weighted_sum c₀ B hB
    (fun c => if (L.cofactor c).Coprime q then F c else 0)
  simp only [mul_ite, mul_zero] at h
  rw [sum_filter, h]
  apply sum_congr rfl
  intro j _
  rw [sum_filter]
  apply sum_congr rfl
  intro e he
  rw [(layerLabel_mem c₀ he).2]

noncomputable def layerReduced (L : Family α N) (c₀ : α) (j q : ℕ) : ℝ :=
  ∑ e ∈ (L.layerSupport j).filter (fun e => e.Coprime q),
    L.weight (L.layerLabel c₀ j e) * omega3ProfileError N q e
      (L.lower (L.layerLabel c₀ j e)) (L.upper (L.layerLabel c₀ j e))

noncomputable def layerR1 (L : Family α N) (c₀ : α) (j D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card * |L.layerReduced c₀ j q|

/-- Both endpoints and the actual prime-count center survive exact signed regrouping. -/
theorem reduced_eq_layers (L : Family α N) (c₀ : α) (B : ℕ)
    (hB : ∀ e, (L.layerFibre e).card ≤ B) (q : ℕ) :
    L.reduced q = ∑ j ∈ range B, L.layerReduced c₀ j q := by
  rw [reduced, L.layer_coprime_sum c₀ B hB]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro e he
  rw [(layerLabel_mem c₀ (mem_filter.mp he).1).2]

/-- The only triangle inequality is between the fixed B complete layers. -/
theorem R1_le_layers (L : Family α N) (c₀ : α) (B : ℕ)
    (hB : ∀ e, (L.layerFibre e).card ≤ B) (D : ℕ) (Z : ℝ) :
    L.R1 D Z ≤ ∑ j ∈ range B, L.layerR1 c₀ j D Z := by
  unfold R1 layerR1
  rw [sum_comm]
  apply sum_le_sum
  intro q _
  rw [L.reduced_eq_layers c₀ B hB, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)

/-- Uniform analytic payment, including empty label types, with fixed cardinality bound. -/
theorem R1_log_saving_of_card (A η F : ℝ) (B : ℕ) {δ : ℝ}
    (hA : 0 < A) (hη : 0 < η) (hF : 0 ≤ F) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (α : Type*) (L : Family α N),
      (∀ e, (L.layerFibre e).card ≤ B) →
      (∀ c ∈ L.labels, (N : ℝ) ^ η ≤ L.cofactor c ∧
        (L.cofactor c : ℝ) ≤ (N : ℝ) ^ (1-η)) →
      (∀ c ∈ L.labels, L.weight c ≤ F) → ∀ Z : ℝ,
      L.R1 (⌊(N : ℝ) ^ (1/2-δ)⌋₊ + 1) Z ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, T, hT, hd⟩ := omega3_balanced_interval_distribution A η F hA hη hF hδ
  refine ⟨((B : ℝ)+1)*C, by positivity, T, hT, ?_⟩
  intro N hN α L hB hp hw Z
  by_cases hn : L.labels.Nonempty
  · obtain ⟨c₀, _⟩ := hn
    have hj (j : ℕ) : L.layerR1 c₀ j (⌊(N : ℝ) ^ (1/2-δ)⌋₊+1) Z ≤
        C*N / Real.log (N : ℝ)^A := by
      apply hd N hN (L.layerSupport j) (fun e => L.weight (L.layerLabel c₀ j e))
        (fun e => L.lower (L.layerLabel c₀ j e)) (fun e => L.upper (L.layerLabel c₀ j e))
      · intro e he
        have hm := layerLabel_mem c₀ he
        simpa only [hm.2] using hp _ hm.1
      · intro e he
        have hm := layerLabel_mem c₀ he
        rw [abs_of_nonneg (L.weight_nonneg _ hm.1)]
        exact hw _ hm.1
      · intro e he
        have hm := layerLabel_mem c₀ he
        simpa only [hm.2] using (L.geometry _ hm.1).2
    have hs := (L.R1_le_layers c₀ B hB _ Z).trans (sum_le_sum (fun j _ => hj j))
    simp only [sum_const, card_range, nsmul_eq_mul] at hs
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact hs.trans (by
      calc
        _ ≤ ((B : ℝ)+1)*(C*N/Real.log (N : ℝ)^A) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring)
  · have hem := not_nonempty_iff_eq_empty.mp hn
    simp only [R1, reduced, hem, filter_empty, sum_empty, abs_zero, mul_zero, sum_const_zero]
    positivity

/-- Positive original weights turn a fixed weighted fibre bound into finite layers.
No inhabitance assumption is imposed, even on empty dependent profile types. -/
theorem R1_log_saving (A η F : ℝ) {δ : ℝ}
    (hA : 0 < A) (hη : 0 < η) (hF : 0 ≤ F) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (α : Type*) (L : Family α N),
      (∀ c ∈ L.labels, (N : ℝ)^η ≤ L.cofactor c ∧
        (L.cofactor c : ℝ) ≤ (N : ℝ)^(1-η)) →
      (∀ c ∈ L.labels, 1 ≤ L.weight c) →
      (∀ e, (∑ c ∈ L.layerFibre e, L.weight c) ≤ F) → ∀ Z : ℝ,
      L.R1 (⌊(N : ℝ) ^ (1/2-δ)⌋₊+1) Z ≤ C*N / Real.log (N : ℝ)^A := by
  obtain ⟨C, hC, T, hT, hd⟩ := R1_log_saving_of_card A η F ⌈F⌉₊ hA hη hF hδ
  refine ⟨C, hC, T, hT, ?_⟩
  intro N hN α L hp hw hf Z
  apply hd N hN α L _ hp _ Z
  · intro e
    have hc : ((L.layerFibre e).card : ℝ) ≤ F := by
      calc
        _ = ∑ _c ∈ L.layerFibre e, (1 : ℝ) := by simp
        _ ≤ ∑ c ∈ L.layerFibre e, L.weight c :=
          sum_le_sum (fun c hc => hw c (mem_filter.mp hc).1)
        _ ≤ F := hf e
    exact_mod_cast hc.trans (Nat.le_ceil F)
  · intro c hc
    exact (single_le_sum (fun d hd => L.weight_nonneg d (mem_filter.mp hd).1)
      (show c ∈ L.layerFibre (L.cofactor c) from mem_filter.mpr ⟨hc, rfl⟩)).trans (hf _)

end Wu2008DoubleSieve.LabelledPhysical.Family
