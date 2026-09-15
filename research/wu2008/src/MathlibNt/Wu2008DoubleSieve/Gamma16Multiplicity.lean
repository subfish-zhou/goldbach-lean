import MathlibNt.Wu2008DoubleSieve.Gamma16Profiles
import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity
import MathlibNt.Wu2008DoubleSieve.Omega3LayerGeometry

/-! # Full window-tuple and three-selected-prime cofactor multiplicity -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def gamma16Selected (c : Gamma16Profile) : Fin 3 → ℕ :=
  ![c.2.2.2.1, c.2.2.1, c.2.1]

theorem gamma16_weighted_fibre_le {i k N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (S : Finset Gamma16Profile)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hprod : ∀ c ∈ S, gamma16Cofactor c = e)
    (ht : ∀ c ∈ S, ∀ j, (gamma16Selected c j).Prime ∧
      gamma16Selected c j ∣ e ∧ (N : ℝ) ^ η ≤ (gamma16Selected c j : ℝ)) :
    (∑ c ∈ S, (convolutionCoeff W c.1 : ℝ)) ≤ (max 1 (1 / η)) ^ (k + 3) := by
  let L := S.sigma fun c =>
    (Fintype.piFinset W).filter fun t => ∏ j, t j = c.1
  let labels (a : Σ _ : Gamma16Profile, Fin i → ℕ) : Fin (i + 3) → ℕ :=
    Fin.append a.2 (gamma16Selected a.1)
  have hinj : Set.InjOn labels L := by
    rintro ⟨⟨d, p3, p2, p1, n⟩, t⟩ ha ⟨⟨d', p3', p2', p1', n'⟩, t'⟩ hb hh
    obtain ⟨haS, hat, hatp⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    obtain ⟨hbS, hbt, hbtp⟩ := mem_sigma.mp hb |>.imp_right mem_filter.mp
    have htt : t = t' := by
      funext j
      simpa only [labels, Fin.append_left] using congr_fun hh (Fin.castAdd 3 j)
    have hs : gamma16Selected ⟨d, p3, p2, p1, n⟩ =
        gamma16Selected ⟨d', p3', p2', p1', n'⟩ := by
      funext j
      simpa only [labels, Fin.append_right] using congr_fun hh (Fin.natAdd i j)
    have hd : d = d' := hatp.symm.trans ((congrArg (fun t : Fin i → ℕ => ∏ j, t j) htt).trans hbtp)
    have hp1 : p1 = p1' := congr_fun hs 0
    have hp2 : p2 = p2' := congr_fun hs 1
    have hp3 : p3 = p3' := congr_fun hs 2
    subst d'; subst p1'; subst p2'; subst p3'; subst t'
    have hna : (d * p1 * p2 * p3) * n = e := by
      simpa only [gamma16Cofactor, mul_assoc, mul_left_comm, mul_comm] using hprod _ haS
    have hnb : (d * p1 * p2 * p3) * n' = e := by
      simpa only [gamma16Cofactor, mul_assoc, mul_left_comm, mul_comm] using hprod _ hbS
    have hn := Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_mul_pos_right (hna ▸ he)) (hna.trans hnb.symm)
    subst n'
    rfl
  have hcard := omega3_prime_labels_card_le L labels hinj hN he heN hη (by
    intro a ha j
    obtain ⟨hc, htW, htd⟩ := mem_sigma.mp ha |>.imp_right mem_filter.mp
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · have hw := hW j (a.2 j) (Fintype.mem_piFinset.mp htW j)
      have hd : a.1.1 ∣ e := by
        rw [← hprod _ hc]
        exact ⟨a.1.2.2.2.2 * a.1.2.2.2.1 * a.1.2.2.1 * a.1.2.1, by
          simp only [gamma16Cofactor, mul_assoc]⟩
      simpa only [labels, Fin.append_left] using
        (show (a.2 j).Prime ∧ a.2 j ∣ e ∧ (N : ℝ) ^ η ≤ (a.2 j : ℝ) from
          ⟨hw.1, ((htd ▸ dvd_prod_of_mem a.2 (mem_univ j))).trans hd, hw.2⟩)
    · simpa only [labels, Fin.append_right] using ht _ hc j)
  have heq : (L.card : ℝ) = ∑ c ∈ S, (convolutionCoeff W c.1 : ℝ) := by
    simp only [L, card_sigma, Nat.cast_sum, convolutionCoeff]
  rw [heq] at hcard
  exact hcard.trans ((pow_le_pow_left₀ (by positivity) (le_max_right 1 (1 / η)) _).trans
    (pow_le_pow_right₀ (le_max_left 1 (1 / η)) (Nat.add_le_add_right hik 3)))

end Wu2008DoubleSieve