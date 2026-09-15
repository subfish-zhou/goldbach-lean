import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleGroupedActual
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.LowerTripleGroupedOutput
open Finset LowerTripleGrouped

/-- The three selected coordinates include the varying physical prime. -/
def selected (a : Σ _ : Label, ℕ) : Fin 3 → ℕ := ![a.1.2.1, a.1.2.2.1, a.2]

/-- Original physical fibre, retaining the prime-output condition exactly. -/
noncomputable def outputFibre {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (x : Label) : Finset ℕ :=
  ((sourceFamily N δ Δ V P j).primes x).filter (fun r => (N-cofactor x*r).Prime)

/-- Both labelled primes inherit their original mother-window bounds. -/
theorem label_prime_data {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) (j : Fin 6) {x : Label}
    (hx : x ∈ (sourceFamily N δ Δ V P j).labels) :
    (x.2.1.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (x.2.1 : ℝ)) ∧
    (x.2.2.1.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (x.2.2.1 : ℝ)) := by
  obtain ⟨hd,hp,hq,_⟩ := (mem_labels x).mp hx
  exact ⟨HighNonunit.mother_window_lower hN hδ hδhi hb P hP hd hp,
    HighNonunit.mother_window_lower hN hδ hδhi hb P hP hd hq⟩

/-- Full original sigma multiplicity at every output, including empty fibres.
The ordered window coordinates are expanded by weighted_labels_le. -/
theorem actual_fixed_output {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hP : P.MotherAdmissible) (j : Fin 6)
    (hW : ∀ s q, q ∈ convolutionWuWindows N Δ V s →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (ell : ℕ) :
    (∑ x ∈ (sourceFamily N δ Δ V P j).labels,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) := by
  let L := sourceFamily N δ Δ V P j
  let S := L.labels.sigma fun x =>
    (outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)
  have data (a : Σ _ : Label, ℕ) (ha : a ∈ S) :
      a.1 ∈ L.labels ∧ a.2.Prime ∧
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (a.2 : ℝ) ∧
      cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hr,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    have hp := (mem_filter.mp hr).1
    obtain ⟨_,hpr,hlo,_⟩ := mem_filter.mp hp
    have hg := source_geometry hN hδ hδhi hb P hP j hx
    have hcap := L.output_le hx hp
    refine ⟨hx,hpr,hg.lower_large.trans hlo.le,?_⟩
    change cofactor a.1*a.2 ≤ N at hcap
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) =
      ∑ x ∈ L.labels, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := source_geometry hN hδ hδhi hb P hP j da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.positive da.2.1.pos
    apply HighNonunit.weighted_labels_le (convolutionWuWindows N Δ V) S
      (fun a => a.1.1) selected hb.1 (by omega) hepos (Nat.sub_le N ell)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact (cofactor_divisors a.1).1.trans (dvd_mul_right _ _)
    · intro a ha s
      have da := data a ha
      have gp := label_prime_data hN hδ hδhi hb P hP j da.1
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
      have gx := source_geometry hN hδ hδhi hb P hP j da.1
      have hx : a.1 = b.1 := fixedE_projection_injective gx.positive rfl hE.symm
        (by simp only [hd,hp,hq])
      exact Sigma.ext hx (heq_of_eq hr)
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

/-- The window hypothesis is supplied internally, before all later parameters. -/
theorem source_output_multiplicity (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible → ∀ j : Fin 6, ∀ ell : ℕ,
      (∑ x ∈ (sourceFamily N δ Δ V P j).labels,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card) ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) := by
  obtain ⟨T,hT,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hP j ell
  apply actual_fixed_output (by omega) hδ hδhi hb P hP j _ ell
  intro s q hq
  have h := hw N hN i Δ V hb s q hq
  exact ⟨h.1,h.2.2⟩

end Wu2008DoubleSieve.LowerTripleGroupedOutput
