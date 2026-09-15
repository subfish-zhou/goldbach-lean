import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitWindowBounds
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveMultiplicity

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighNonunit
open Finset

/-- Expand the original convolution coefficient before counting ordered labels. -/
theorem weighted_labels_le {A : Type*} {i k m N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (S : Finset A) (d : A → ℕ) (t : A → Fin m → ℕ)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ (p : ℝ))
    (hd : ∀ a ∈ S, d a ∣ e)
    (ht : ∀ a ∈ S, ∀ j, (t a j).Prime ∧ t a j ∣ e ∧ (N : ℝ)^η ≤ (t a j : ℝ))
    (hi : ∀ a ∈ S, ∀ b ∈ S, d a = d b → t a = t b → a = b) :
    (∑ a ∈ S, (convolutionCoeff W (d a) : ℝ)) ≤ (max 1 (1/η))^(k+m) := by
  let L := S.sigma fun a => (Fintype.piFinset W).filter fun u => ∏ j, u j = d a
  let enc (a : Σ _ : A, Fin i → ℕ) : Fin (i+m) → ℕ := Fin.append a.2 (t a.1)
  have hinj : Set.InjOn enc L := by
    intro a ha b hb h
    obtain ⟨ha, hau, had⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨hb, hbu, hbd⟩ := mem_sigma.mp hb |>.imp_right mem_filter.mp
    have hu : a.2 = b.2 := by
      funext j
      simpa only [enc, Fin.append_left] using congr_fun h (Fin.castAdd m j)
    have htt : t a.1 = t b.1 := by
      funext j
      simpa only [enc, Fin.append_right] using congr_fun h (Fin.natAdd i j)
    have hdd := had.symm.trans ((congrArg (fun u : Fin i → ℕ => ∏ j, u j) hu).trans hbd)
    exact Sigma.ext (hi _ ha _ hb hdd htt) (heq_of_eq hu)
  have hc := omega3_prime_labels_card_le L enc hinj hN he heN hη (by
    intro a ha j
    obtain ⟨ha, hau, had⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hw := hW j (a.2 j) (Fintype.mem_piFinset.mp hau j)
      simpa only [enc, Fin.append_left] using
        (show (a.2 j).Prime ∧ a.2 j ∣ e ∧ (N : ℝ)^η ≤ (a.2 j : ℝ) from
          ⟨hw.1, ((had ▸ dvd_prod_of_mem a.2 (mem_univ j))).trans (hd _ ha), hw.2⟩)
    · simpa only [enc, Fin.append_right] using ht _ ha j)
  have heq : (L.card : ℝ) = ∑ a ∈ S, (convolutionCoeff W (d a) : ℝ) := by
    simp only [L, card_sigma, Nat.cast_sum, convolutionCoeff]
  rw [heq] at hc
  exact hc.trans ((pow_le_pow_left₀ (by positivity) (le_max_right 1 (1/η)) _).trans
    (pow_le_pow_right₀ (le_max_left 1 (1/η)) (Nat.add_le_add_right hik m)))

/-- Positivity is a fact of the original support, including arbitrary empty families. -/
theorem actual_coefficient_pos {i N : ℕ} {δ : ℝ} {p : SecondFunctionalParameters}
    {W : Fin i → Finset ℕ} {high : Bool} {x : Profile}
    (hx : x ∈ actualProfiles N δ p W high) : 0 < convolutionCoeff W x.1 :=
  mem_boxConvolutionSupport.mp (mem_sigma.mp hx).1

/-- Unweight only after proving that every retained original coefficient is positive. -/
theorem actual_card_fibre_le_weight {i N e : ℕ} (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) :
    (((actualProfiles N δ p W high).filter (fun x => cofactor x = e)).card : ℝ) ≤
      ∑ x ∈ (actualProfiles N δ p W high).filter (fun x => cofactor x = e),
        (convolutionCoeff W x.1 : ℝ) := by
  calc
    _ = ∑ _x ∈ (actualProfiles N δ p W high).filter (fun x => cofactor x = e), (1 : ℝ) := by simp
    _ ≤ _ := sum_le_sum fun x hx => by exact_mod_cast actual_coefficient_pos (mem_filter.mp hx).1

/-- Number of retained primePrefix primes, excluding the last fibre prime. -/
def arity (high : Bool) : ℕ := if high then 5 else 4

def primePrefix (x : Profile) : List ℕ := x.2.1 ++ [x.2.2.1]

def selected (m : ℕ) (x : Profile) : Fin m → ℕ := fun j => (primePrefix x).getD j 0

/-- Recover the whole ordered list, rather than its product image. -/
theorem list_eq_of_getD {m : ℕ} {l l' : List ℕ}
    (hl : l.length = m) (hl' : l'.length = m)
    (h : (fun j : Fin m => l.getD j 0) = fun j : Fin m => l'.getD j 0) : l = l' := by
  apply List.ext_getElem
  · omega
  · intro j hj hj'
    have hh := congr_fun h ⟨j, by omega⟩
    simpa only [List.getD_eq_getElem l 0 hj, List.getD_eq_getElem l' 0 hj'] using hh

/-- The quotient is recovered by positive multiplication, never counted as a prime. -/
theorem profile_recover {m : ℕ} {x y : Profile}
    (hx : (primePrefix x).length = m) (hy : (primePrefix y).length = m)
    (hd : x.1 = y.1) (ht : selected m x = selected m y)
    (hp : 0 < x.1 * (primePrefix x).prod) (hc : cofactor x = cofactor y) : x = y := by
  have hpre := list_eq_of_getD hx hy ht
  have hlen : x.2.1.length = y.2.1.length := by simpa [primePrefix] using congrArg List.length hpre
  have hh := List.append_inj hpre hlen
  have hpen : x.2.2.1 = y.2.2.1 := by simpa using hh.2
  have hn : x.2.2.2 = y.2.2.2 := by
    apply Nat.eq_of_mul_eq_mul_left hp
    change x.1 * x.2.2.2 * (primePrefix x).prod = y.1 * y.2.2.2 * (primePrefix y).prod at hc
    simpa only [← hd, ← hpre, mul_assoc, mul_left_comm, mul_comm] using hc
  rcases x with ⟨d,pre,p,n⟩
  rcases y with ⟨d',pre',p',n'⟩
  dsimp only at hd hh hpen hn
  have hpp := hh.1
  subst d'; subst pre'; subst p'; subst n'
  rfl

/-- Every actual primePrefix coordinate inherits the mother-window lower bound. -/
theorem actual_profile_data {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool) {x : Profile}
    (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high) :
    x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
    (primePrefix x).length = arity high ∧
    (∀ r ∈ primePrefix x, r.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (r : ℝ)) ∧
    0 < x.1 * (primePrefix x).prod ∧ 0 < cofactor x ∧ cofactor x ≤ N := by
  obtain ⟨hd,ht,hpn⟩ := mem_sigma.mp hx |>.imp_right mem_sigma.mp
  obtain ⟨hlen,_,hpre⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp ht
  obtain ⟨hpn,hn,_,_,_,hcap⟩ := mem_filter.mp hpn
  have hpen := (mem_product.mp hpn).1
  have hr : ∀ r ∈ primePrefix x, r.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (r : ℝ) := by
    intro r hr
    apply mother_window_lower hN hδ hδhi hb p hp hd
    rcases List.mem_append.mp hr with hr | hr
    · exact hpre r hr
    · have he : r = x.2.2.1 := by simpa using hr
      simpa [he] using hpen
  have hdpos := (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  have hpp : 0 < (primePrefix x).prod := List.prod_pos (fun r hr' => (hr r hr').1.pos)
  have hco : 0 < cofactor x := by
    exact Nat.mul_pos (Nat.mul_pos hdpos (by omega)) hpp
  refine ⟨hd, ?_, hr, Nat.mul_pos hdpos hpp, hco, ?_⟩
  · cases high <;> simp_all [primePrefix, arity, word, HighUnitSource.word20, HighUnitSource.word21]
  · exact (Nat.le_mul_of_pos_right _ (mem_primeWindow.mp hpen).1.pos).trans hcap

/-- Fixed-cofactor full original sigma, with all ordered window and primePrefix labels. -/
theorem actual_fixed_cofactor {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool)
    (hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (e : ℕ) :
    (∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
      (fun x => cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ)) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+arity high) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter (fun x => cofactor x = e)
  by_cases hs : S.Nonempty
  · obtain ⟨x,hx⟩ := hs
    have hg := actual_profile_data hN hδ hδhi hb p hp high (mem_filter.mp hx).1
    have he := (mem_filter.mp hx).2
    apply weighted_labels_le _ S (fun x => x.1) (selected (arity high)) hb.1 (by omega)
      (he ▸ hg.2.2.2.2.1) (he ▸ hg.2.2.2.2.2)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    · intro a ha
      rw [← (mem_filter.mp ha).2]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · intro a ha j
      obtain ⟨ha,he⟩ := mem_filter.mp ha
      have hg := actual_profile_data hN hδ hδhi hb p hp high ha
      have hj : j.val < (primePrefix a).length := by rw [hg.2.1]; exact j.isLt
      have hm : selected (arity high) a j ∈ primePrefix a := by
        simp only [selected, List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hr := hg.2.2.1 _ hm
      refine ⟨hr.1, ?_, hr.2⟩
      rw [← he]
      exact (List.dvd_prod hm).trans (dvd_mul_left _ _)
    · intro a ha b hb' hd ht
      have ga := actual_profile_data hN hδ hδhi hb p hp high (mem_filter.mp ha).1
      have gb := actual_profile_data hN hδ hδhi hb p hp high (mem_filter.mp hb').1
      exact profile_recover ga.2.1 gb.2.1 hd ht ga.2.2.2.1
        ((mem_filter.mp ha).2.trans (mem_filter.mp hb').2.symm)
  · change (∑ x ∈ S, _) ≤ _
    rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

/-- Fixed output counts the final prime as well as every original sigma label. -/
theorem actual_fixed_output {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool)
    (hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ)) (ell : ℕ) :
    (∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card) ≤
      (max 1 (1/(wuLocalExponent k δ / 10)))^(k+arity high+1) := by
  let S := (actualProfiles N δ p (convolutionWuWindows N Δ V) high).sigma fun x =>
    (actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)
  let t (a : Σ _ : Profile, ℕ) : Fin (arity high+1) → ℕ :=
    Fin.append (selected (arity high) a.1) (fun _ : Fin 1 => a.2)
  have data (a : Σ _ : Profile, ℕ) (ha : a ∈ S) :
      a.1 ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high ∧
      a.2.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (a.2 : ℝ) ∧
      cofactor a.1*a.2 = N-ell := by
    obtain ⟨hx,hq,he⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨_,hpr,ho,_,_,hcap,_⟩ := mem_filter.mp hq
    have hg := actual_profile_data hN hδ hδhi hb p hp high hx
    have hl := (hg.2.2.1 a.1.2.2.1 (by simp [primePrefix])).2
    refine ⟨hx,hpr,hl.trans (by exact_mod_cast ho.le), ?_⟩
    omega
  have heq : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) =
      ∑ x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card := by
    simp only [S, sum_sigma, sum_const, nsmul_eq_mul, mul_comm]
  rw [← heq]
  by_cases hs : S.Nonempty
  · obtain ⟨a,ha⟩ := hs
    have da := data a ha
    have ga := actual_profile_data hN hδ hδhi hb p hp high da.1
    have hepos : 0 < N-ell := da.2.2.2 ▸ Nat.mul_pos ga.2.2.2.2.1 da.2.1.pos
    have hbound := weighted_labels_le (convolutionWuWindows N Δ V) S (fun a => a.1.1) t
      hb.1 (by omega) hepos (Nat.sub_le N ell)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hW
    have hresult : (∑ a ∈ S, (convolutionCoeff (convolutionWuWindows N Δ V) a.1.1 : ℝ)) ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+(arity high+1)) := by
      apply hbound
      · intro a ha
        rw [← (data a ha).2.2.2]
        exact (dvd_mul_of_dvd_left (dvd_mul_right _ _) _).trans (dvd_mul_right _ _)
      · intro a ha j
        have da := data a ha
        have ga := actual_profile_data hN hδ hδhi hb p hp high da.1
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have hj : j.val < (primePrefix a.1).length := by rw [ga.2.1]; exact j.isLt
          have hm : selected (arity high) a.1 j ∈ primePrefix a.1 := by
            simp only [selected, List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem hj
          have hr := ga.2.2.1 _ hm
          have hdv : selected (arity high) a.1 j ∣ N-ell := by
            rw [← da.2.2.2]
            exact ((List.dvd_prod hm).trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
          simpa only [t, Fin.append_left] using And.intro hr.1 (And.intro hdv hr.2)
        · have hdv : a.2 ∣ N-ell := by rw [← da.2.2.2]; exact dvd_mul_left _ _
          simpa only [t, Fin.append_right] using And.intro da.2.1 (And.intro hdv da.2.2.1)
      · intro a ha b hb' hd ht
        have da := data a ha
        have db := data b hb'
        have ga := actual_profile_data hN hδ hδhi hb p hp high da.1
        have gb := actual_profile_data hN hδ hδhi hb p hp high db.1
        have hs : selected (arity high) a.1 = selected (arity high) b.1 := by
          funext j
          simpa only [t, Fin.append_left] using congr_fun ht (Fin.castAdd 1 j)
        have hq : a.2 = b.2 := by
          simpa only [t, Fin.append_right] using congr_fun ht (Fin.natAdd (arity high) 0)
        have hc : cofactor a.1 = cofactor b.1 := by
          apply Nat.eq_of_mul_eq_mul_right da.2.1.pos
          exact da.2.2.2.trans (by simpa only [← hq] using db.2.2.2.symm)
        exact Sigma.ext (profile_recover ga.2.1 gb.2.1 hd hs ga.2.2.2.1 hc) (heq_of_eq hq)
    simpa only [Nat.add_assoc] using hresult
  · rw [not_nonempty_iff_eq_empty.mp hs, sum_empty]
    positivity

/-- One threshold before N, all source boxes, mother parameters and both words. -/
theorem source_multiplicities (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      let W := convolutionWuWindows N Δ V
      let H := max 1 (1/(wuLocalExponent k δ / 10))
      (∀ e, (∑ x ∈ (actualProfiles N δ p W high).filter (fun x => cofactor x = e),
        (convolutionCoeff W x.1 : ℝ)) ≤ H^(k+arity high)) ∧
      (∀ ell, (∑ x ∈ actualProfiles N δ p W high, (convolutionCoeff W x.1 : ℝ) *
        ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card) ≤ H^(k+arity high+1)) := by
  obtain ⟨T,hT,hw⟩ := omega3_source_window_lower k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp high
  have hW : ∀ j q, q ∈ convolutionWuWindows N Δ V j →
      q.Prime ∧ (N : ℝ)^(wuLocalExponent k δ / 10) ≤ (q : ℝ) := by
    intro j q hq
    have h := hw N hN i Δ V hb j q hq
    exact ⟨h.1,h.2.2⟩
  exact ⟨actual_fixed_cofactor (by omega) hδ hδhi hb p hp high hW,
    actual_fixed_output (by omega) hδ hδhi hb p hp high hW⟩

end Wu2008DoubleSieve.HighNonunit
