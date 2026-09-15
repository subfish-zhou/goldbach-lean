import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform
import MathlibNt.Wu2008DoubleSieve.TruncatedFourPayment

/-! Closed prime labels retain every multiplicity and impose no coprimality screen.
The cofactor is an arbitrary nonunit rough integer, not a prime. -/
namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Real LiLiuPrereqBuchstab TruncatedFourPhysical
open scoped Classical
noncomputable section

abbrev alpha : ℝ := truncatedSixthLowerAlpha
abbrev beta : ℝ := truncatedSixthLowerBeta
abbrev lam : ℝ := truncatedSixthLowerLambda

private def flatten : (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ) ↪ Quad where
  toFun s := (s.1, s.2.1, s.2.2.1, s.2.2.2)
  inj' := by rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he; simpa using he

@[simp] private theorem flatten_apply (a b c d : ℕ) :
    flatten ⟨a,b,c,d⟩ = (a,b,c,d) := rfl

noncomputable def labels (N : ℕ) (lower upper : ℕ → ℝ) : Finset Quad :=
  ((primesIcc ((N : ℝ)^alpha) ((N : ℝ)^beta)).sigma fun a =>
    (primesIcc a ((N : ℝ)^beta)).sigma fun b =>
      (primesIcc b ((N : ℝ)^beta)).sigma fun c =>
        primesIcc (lower c) (upper c)).map flatten

noncomputable def labels10 (N : ℕ) : Finset Quad :=
  labels N (fun c => c) (fun _ => (N : ℝ)^beta)
noncomputable def labels11 (N : ℕ) : Finset Quad :=
  labels N (fun _ => (N : ℝ)^beta) (fun c => (N : ℝ)^lam / c)
noncomputable def cofactor (N : ℕ) (q : Quad) : Finset ℕ :=
  (roughNumbers ((N : ℝ) / fourModulusProduct q) q.2.1).erase 1
noncomputable def mass (N : ℕ) (S : Finset Quad) : ℝ :=
  ∑ q ∈ S, ((cofactor N q).card : ℝ)
noncomputable def rawMass10 (N : ℕ) : ℝ := mass N (labels10 N)
noncomputable def rawMass11 (N : ℕ) : ℝ := mass N (labels11 N)

/-- Strict product cutoff, with the original nonunit ordinary rough condition. -/
noncomputable def strictFibre (N : ℕ) (q : Quad) : Finset ℕ :=
  (range (N+1)).filter fun n => 1 < n ∧ Rough (q.2.1 : ℝ) n ∧
    fourModulusProduct q*n < N
noncomputable def strictMass (N : ℕ) (S : Finset Quad) : ℝ :=
  ∑ q ∈ S, ((strictFibre N q).card : ℝ)

theorem mem_labels {N a b c d : ℕ} {l u : ℕ → ℝ} :
    (a,b,c,d) ∈ labels N l u ↔
    a ∈ primesIcc ((N : ℝ)^alpha) ((N : ℝ)^beta) ∧
    b ∈ primesIcc a ((N : ℝ)^beta) ∧
    c ∈ primesIcc b ((N : ℝ)^beta) ∧ d ∈ primesIcc (l c) (u c) := by
  simp [labels, Prod.mk.injEq, and_assoc]

theorem mass_eq_nested (N : ℕ) (l u : ℕ → ℝ) :
    mass N (labels N l u) =
    ∑ a ∈ primesIcc ((N : ℝ)^alpha) ((N : ℝ)^beta),
    ∑ b ∈ primesIcc a ((N : ℝ)^beta),
    ∑ c ∈ primesIcc b ((N : ℝ)^beta),
    ∑ d ∈ primesIcc (l c) (u c),
      (((roughNumbers ((N : ℝ)/(a*b*c*d)) b).erase 1).card : ℝ) := by
  simp only [mass, labels, sum_map, sum_sigma, flatten_apply, cofactor, fourModulusProduct, Nat.cast_mul]

theorem T10_subset (N : ℕ) : T10 N ⊆ labels10 N := by
  rintro ⟨a,b,c,d⟩ ht
  obtain ⟨ha,_,hza,hb,_,hc,_,hd,_,hdw,hab,hbc,hcd⟩ := mem_s3_first_quadruples.mp ht
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd.le
  have hw : 0 ≤ (N : ℝ)^beta := rpow_nonneg (Nat.cast_nonneg N) _
  exact mem_labels.mpr ⟨(mem_primesIcc hw).mpr ⟨ha,hza,hab'.trans (hbc'.trans (hcd'.trans hdw.le))⟩,
    (mem_primesIcc hw).mpr ⟨hb,hab',hbc'.trans (hcd'.trans hdw.le)⟩,
    (mem_primesIcc hw).mpr ⟨hc,hbc',hcd'.trans hdw.le⟩,
    (mem_primesIcc hw).mpr ⟨hd,hcd',hdw.le⟩⟩

theorem T11_subset (N : ℕ) : T11 N ⊆ labels11 N := by
  rintro ⟨a,b,c,d⟩ ht
  obtain ⟨ha,_,hza,hb,_,hc,_,hd,_,hab,hbc,hcw,hwd,hdV⟩ := mem_s3Upsilon11Range.mp ht
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc.le
  have hw : 0 ≤ (N : ℝ)^beta := rpow_nonneg (Nat.cast_nonneg N) _
  have hv : 0 ≤ (N : ℝ)^lam / c := div_nonneg (rpow_nonneg (Nat.cast_nonneg N) _) (Nat.cast_nonneg c)
  exact mem_labels.mpr ⟨(mem_primesIcc hw).mpr ⟨ha,hza,hab'.trans (hbc'.trans hcw.le)⟩,
    (mem_primesIcc hw).mpr ⟨hb,hab',hbc'.trans hcw.le⟩,
    (mem_primesIcc hw).mpr ⟨hc,hbc',hcw.le⟩,
    (mem_primesIcc hv).mpr ⟨hd,hwd,hdV.le⟩⟩

theorem strictFibre_subset {N : ℕ} {q : Quad} (hD : 0 < fourModulusProduct q) :
    strictFibre N q ⊆ cofactor N q := by
  intro n hn
  obtain ⟨_,hn1,hr,hlt⟩ := mem_filter.mp hn
  apply mem_erase.mpr
  refine ⟨by omega, mem_roughNumbers.mpr ⟨by omega, ?_, hr⟩⟩
  apply (le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < fourModulusProduct q)).mpr
  have hm : (fourModulusProduct q : ℝ)*n ≤ N := by exact_mod_cast hlt.le
  nlinarith

theorem strictMass_le {N : ℕ} {S U : Finset Quad} (hS : S ⊆ U)
    (hD : ∀ q ∈ S, 0 < fourModulusProduct q) : strictMass N S ≤ mass N U := by
  calc
    _ ≤ mass N S := sum_le_sum fun q hq => by
      exact_mod_cast card_le_card (strictFibre_subset (hD q hq))
    _ ≤ mass N U := sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)

theorem original_strict_masses_le (N : ℕ) :
    strictMass N (T10 N) ≤ rawMass10 N ∧ strictMass N (T11 N) ≤ rawMass11 N :=
  ⟨strictMass_le (T10_subset N) (fun _ h => domain_product_pos (T10_sub N h)),
   strictMass_le (T11_subset N) (fun _ h => domain_product_pos (T11_sub N h))⟩

/-- Dropping the output-prime test is only a positive enlargement. -/
theorem physical_card_le_strictMass (N : ℕ) (S : Finset Quad) :
    ((physical N S).card : ℝ) ≤ strictMass N S := by
  simp only [physical, card_sigma, Nat.cast_sum, strictMass]
  apply sum_le_sum
  intro q _
  exact_mod_cast card_le_card (show
    (range (N+1)).filter (fun n => 1 < n ∧ Rough (q.2.1 : ℝ) n ∧
      fourModulusProduct q*n < N ∧ (N-fourModulusProduct q*n).Prime) ⊆ strictFibre N q from
    fun n hn => by
      obtain ⟨hn,hn1,hr,hlt,_⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hn,hn1,hr,hlt⟩)

theorem original_physical_cards_le (N : ℕ) :
    ((Physical10 N).card : ℝ) ≤ rawMass10 N ∧
    ((Physical11 N).card : ℝ) ≤ rawMass11 N :=
  ⟨(physical_card_le_strictMass N _).trans (original_strict_masses_le N).1,
   (physical_card_le_strictMass N _).trans (original_strict_masses_le N).2⟩

end
end Wu2008DoubleSieve.FourRoughClosedMass
