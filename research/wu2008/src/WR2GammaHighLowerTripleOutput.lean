import WR2GammaHighLowerTripleGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFixedOutput

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGrouped HighBoxRecovery Finset
open scoped Classical

/-- Original physical fibre, retaining the prime-output condition exactly. -/
def outputFibre (j : Fin 3) (N : ℕ) (δ : ℝ) (k : Fin 6) (x : Label) : Finset ℕ :=
  ((sourceFamily j N δ k).primes x).filter (fun r => (N-cofactor x*r).Prime)

/-- Both labelled primes inherit their original mother-window bounds. -/
theorem label_prime_data {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) {x : Label}
    (hx : x ∈ (sourceFamily j N δ k).labels) :
    (x.2.1.Prime ∧ (N : ℝ)^(highEta) ≤ (x.2.1 : ℝ)) ∧
    (x.2.2.1.Prime ∧ (N : ℝ)^(highEta) ≤ (x.2.2.1 : ℝ)) := by
  obtain ⟨hd,hp,hq,_⟩ := (mem_labels x).mp hx
  exact ⟨window_lower j hN hδ hδhi hd hp,
    window_lower j hN hδ hδhi hd hq⟩

/-- Full original sigma multiplicity at every output, including empty fibres.
The ordered window coordinates are expanded by weighted_labels_le. -/
theorem actual_fixed_output {N : ℕ} {δ : ℝ} (j : Fin 3) (k : Fin 6)
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (ell : ℕ) :
    (∑ x ∈ (sourceFamily j N δ k).labels,
      (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((outputFibre j N δ k x).filter (fun r => N-cofactor x*r = ell)).card) ≤
      (max 1 (1/(highEta)))^4 := by
  let L := sourceFamily j N δ k
  let S := L.labels.sigma fun x =>
    (outputFibre j N δ k x).filter (fun r => N-cofactor x*r = ell)
  have data (a : Σ _ : Label, ℕ) (ha : a ∈ S) :
      a.1 ∈ L.labels ∧ a.2.Prime ∧
      (N : ℝ)^(highEta) ≤ (a.2 : ℝ) ∧
      cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hr,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    have hp := (mem_filter.mp hr).1
    obtain ⟨_,hpr,hlo,_⟩ := mem_filter.mp hp
    have hg := source_geometry j k hN hδ hδhi hx
    have hcap := L.output_le hx hp
    refine ⟨hx,hpr,hg.lower_large.trans hlo.le,?_⟩
    change cofactor a.1*a.2 ≤ N at hcap
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (windows j N) a.1.1 : ℝ)) =
      ∑ x ∈ L.labels, (convolutionCoeff (windows j N) x.1 : ℝ) *
        ((outputFibre j N δ k x).filter (fun r => N-cofactor x*r = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := source_geometry j k hN hδ hδhi da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.positive da.2.1.pos
    apply HighNonunit.weighted_labels_le (windows j N) S
      (fun a => a.1.1) LowerTripleGroupedOutput.selected (by norm_num : 1 ≤ 1) (by omega : 1 < N) hepos (Nat.sub_le N ell)
      (by norm_num [highEta] : 0 < highEta) (fun a q hq => by
        have h := prime_geometry j hN hδ hδhi hq
        exact ⟨h.1,h.2.2.1⟩)
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact (cofactor_divisors a.1).1.trans (dvd_mul_right _ _)
    · intro a ha s
      have da := data a ha
      have gp := label_prime_data j k hN hδ hδhi da.1
      have dp : a.1.2.1 ∣ N-ell := by
        rw [← da.2.2.2]
        exact (cofactor_divisors a.1).2.1.trans (dvd_mul_right _ _)
      have dq : a.1.2.2.1 ∣ N-ell := by
        rw [← da.2.2.2]
        exact (cofactor_divisors a.1).2.2.trans (dvd_mul_right _ _)
      have dr : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
      refine Fin.cases ?_ (fun t => Fin.cases ?_ (fun u => Fin.cases ?_ (fun z => Fin.elim0 z) u) t) s
      · exact ⟨gp.1.1,dp,gp.1.2⟩
      · exact ⟨gp.2.1,dq,gp.2.2⟩
      · exact ⟨da.2.1,dr,da.2.2.1⟩
    · intro a ha b hb' hd ht
      have da := data a ha
      have db := data b hb'
      have hp : a.1.2.1 = b.1.2.1 := congr_fun ht 0
      have hq : a.1.2.2.1 = b.1.2.2.1 := congr_fun ht 1
      have hr : a.2 = b.2 := congr_fun ht 2
      have hE : cofactor a.1 = cofactor b.1 := by
        apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
        exact da.2.2.2.trans (by simpa only [← hr] using db.2.2.2.symm)
      have gx := source_geometry j k hN hδ hδhi da.1
      have hx : a.1 = b.1 := fixedE_projection_injective gx.positive rfl hE.symm
        (by simp only [hd,hp,hq])
      exact Sigma.ext hx (heq_of_eq hr)
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity


end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.actual_fixed_output
