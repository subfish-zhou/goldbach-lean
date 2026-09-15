import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunitActualFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Layers

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset

def selected (x : Gamma16Profile) : Fin 3 → ℕ := ![x.2.2.2.1, x.2.2.1, x.2.1]

theorem profile_recover {x y : Gamma16Profile}
    (hd : x.1 = y.1) (ht : selected x = selected y)
    (hp : 0 < x.1*x.2.2.2.1*x.2.2.1*x.2.1)
    (hc : gamma16Cofactor x = gamma16Cofactor y) : x = y := by
  have h1 : x.2.2.2.1 = y.2.2.2.1 := congr_fun ht 0
  have h2 : x.2.2.1 = y.2.2.1 := congr_fun ht 1
  have h3 : x.2.1 = y.2.1 := congr_fun ht 2
  have hn : x.2.2.2.2 = y.2.2.2.2 := by
    apply Nat.eq_of_mul_eq_mul_left hp
    change x.1*x.2.2.2.2*x.2.2.2.1*x.2.2.1*x.2.1 =
      y.1*y.2.2.2.2*y.2.2.2.1*y.2.2.1*y.2.1 at hc
    simpa only [← hd, ← h1, ← h2, ← h3, mul_assoc, mul_left_comm, mul_comm] using hc
  rcases x with ⟨d,p3,p2,p1,n⟩
  rcases y with ⟨d',p3',p2',p1',n'⟩
  dsimp only at hd h1 h2 h3 hn
  subst d'; subst p3'; subst p2'; subst p1'; subst n'
  rfl

theorem selected_dvd (x : Gamma16Profile) (j : Fin 3) : selected x j ∣ gamma16Cofactor x := by
  fin_cases j <;> dsimp [selected, gamma16Cofactor]
  · exact (dvd_mul_left _ _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · exact dvd_mul_left _ _

theorem actual_profile_data {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 4) {x : Gamma16Profile}
    (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j) :
    (∀ r, (selected x r).Prime ∧
      (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (selected x r : ℝ)) ∧
    0 < x.1*x.2.2.2.1*x.2.2.1*x.2.1 ∧
    0 < gamma16Cofactor x ∧ gamma16Cofactor x ≤ N := by
  obtain ⟨hd,h3,h2,h1,_,hn,_,_,_,_,hcap⟩ := profile_data hx
  have g1 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h1
  have g2 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h2
  have g3 := HighNonunit.mother_window_lower hN hδ hδhi hb p hp hd h3
  have hdpos := (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  refine ⟨?_, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos g1.1.pos) g2.1.pos) g3.1.pos,
    ?_, (Nat.le_mul_of_pos_right _ g3.1.pos).trans hcap⟩
  · intro r
    fin_cases r
    · exact g1
    · exact g2
    · exact g3
  · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdpos (by omega))
      g1.1.pos) g2.1.pos) g3.1.pos

theorem actual_fixed_cofactor {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 4)
    (hW : ∀ r q, q ∈ convolutionWuWindows N Δ V r →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
      (fun x => gamma16Cofactor x = e),
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) j).filter
    (fun x => gamma16Cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have gx := actual_profile_data hN hδ hδhi hb p hp j (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply HighNonunit.weighted_labels_le _ S (fun x => x.1) selected hb.1 (by omega)
      (he ▸ gx.2.2.1) (he ▸ gx.2.2.2)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact (((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have ga := actual_profile_data hN hδ hδhi hb p hp j (mem_filter.mp ha).1
      exact ⟨(ga.1 r).1, (mem_filter.mp ha).2 ▸ selected_dvd a r, (ga.1 r).2⟩
    · intro a ha b hb' hd ht
      have ga := actual_profile_data hN hδ hδhi hb p hp j (mem_filter.mp ha).1
      exact profile_recover hd ht ga.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem actual_fixed_output {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (j : Fin 4)
    (hW : ∀ r q, q ∈ convolutionWuWindows N Δ V r →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (ell : ℕ) :
    (∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+4) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) j).sigma fun x =>
    (actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)
  let t (a : Σ _ : Gamma16Profile, ℕ) : Fin (3+1) → ℕ :=
    Fin.append (selected a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Gamma16Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j ∧
      a.2.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (a.2 : ℝ) ∧
      gamma16Cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hq,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,ho,_,_,hcap,_⟩ := mem_filter.mp hq
    have gx := actual_profile_data hN hδ hδhi hb p hp j hx
    have hl : (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (a.1.2.1 : ℝ) := (gx.1 2).2
    refine ⟨hx,hpr,hl.trans (by exact_mod_cast ho.le), ?_⟩
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) =
      ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) j,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := actual_profile_data hN hδ hδhi hb p hp j da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.1 da.2.1.pos
    apply HighNonunit.weighted_labels_le (convolutionWuWindows N Δ V) S (fun a => a.1.1) t
      hb.1 (by omega) hepos (Nat.sub_le N ell)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · intro a ha
      rw [← (data a ha).2.2.2]
      exact ((((dvd_mul_right _ _).trans (dvd_mul_right _ _)).trans
        (dvd_mul_right _ _)).trans (dvd_mul_right _ _)).trans (dvd_mul_right _ _)
    · intro a ha r
      have da := data a ha
      have ga := actual_profile_data hN hδ hδhi hb p hp j da.1
      refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · have hdv : selected a.1 r ∣ N-ell := by
          rw [← da.2.2.2]
          exact (selected_dvd a.1 r).trans (dvd_mul_right _ _)
        simpa only [t, Fin.append_left] using
          And.intro (ga.1 r).1 (And.intro hdv (ga.1 r).2)
      · have hdv : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
        simpa only [t, Fin.append_right] using And.intro da.2.1 (And.intro hdv da.2.2.1)
    · intro a ha b hb' hd ht
      have da := data a ha
      have db := data b hb'
      have ga := actual_profile_data hN hδ hδhi hb p hp j da.1
      have hs : selected a.1 = selected b.1 := by
        funext r
        simpa only [t, Fin.append_left] using congr_fun ht (Fin.castAdd 1 r)
      have hq : a.2 = b.2 := by
        simpa only [t, Fin.append_right] using congr_fun ht (Fin.natAdd 3 0)
      have hc : gamma16Cofactor a.1 = gamma16Cofactor b.1 := by
        apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
        exact da.2.2.2.trans (by simpa only [← hq] using db.2.2.2.symm)
      exact Sigma.ext (profile_recover hd hs ga.2.1 hc) (heq_of_eq hq)
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

theorem source_multiplicities (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      let W := convolutionWuWindows N Δ V
      let H := max 1 (1/(wuLocalExponent k δ / 10))
      (∀ e, (∑ x ∈ (actualProfiles N δ p W j).filter (fun x => gamma16Cofactor x = e),
        (convolutionCoeff W x.1 : ℝ)) ≤ H^(k+3)) ∧
      (∀ ell, (∑ x ∈ actualProfiles N δ p W j, (convolutionCoeff W x.1 : ℝ) *
        ((actualFibre N δ p j x).filter (fun q => N-gamma16Cofactor x*q = ell)).card) ≤ H^(k+4)) := by
  obtain ⟨T,hT,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  have hW : ∀ r q, q ∈ convolutionWuWindows N Δ V r →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
    intro r q hq
    have h := hw N hN i Δ V hb r q hq
    exact ⟨h.1,h.2.2⟩
  exact ⟨actual_fixed_cofactor (by omega) hδ hδhi hb p hp j hW,
    actual_fixed_output (by omega) hδ hδhi hb p hp j hW⟩

end Wu2008DoubleSieve.FourPrimeNonunit
