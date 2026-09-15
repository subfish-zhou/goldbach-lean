import MathlibNt.Wu2008DoubleSieve.ReboxingEndpoints
import Mathlib.GroupTheory.Perm.Fin

/-!
# Sorted insertion into the actual Wu family

Wu04, proof of Proposition 2 after (3.15), lines 1024--1044.
The inserted coordinate is a box upper endpoint, not a selected prime.
Insertion is an actual permutation, so repeated endpoints and all ordered
convolution multiplicities are preserved.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem boxSquaredPrefixes_cons_iff {i : ℕ} {Q x : ℝ} {V : Fin i → ℝ}
    (hx : 0 < x) :
    boxSquaredPrefixes Q (Fin.cons x V) ↔
      x ^ 2 ≤ Q ∧ boxSquaredPrefixes (Q / x) V := by
  simp only [boxSquaredPrefixes_iff]
  constructor
  · intro h
    constructor
    · simpa using h 0
    · intro j
      have hj := h j.succ
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        show (0 : Fin (i + 1)) < j.succ by change 0 < j.val + 1; omega, if_true,
        Fin.succ_lt_succ_iff] at hj
      apply (le_div_iff₀ hx).2
      nlinarith [hj]
  · rintro ⟨h0, hV⟩ j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa using h0
    · have hl := (le_div_iff₀ hx).1 (hV l)
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        show (0 : Fin (i + 1)) < l.succ by change 0 < l.val + 1; omega, if_true,
        Fin.succ_lt_succ_iff]
      nlinarith [hl]

theorem box_prefix_mul_entry_le_product {i : ℕ} {V : Fin i → ℝ}
    (hV : ∀ j, 1 ≤ V j) (j : Fin i) :
    (∏ l, if l < j then V l else 1) * V j ≤ ∏ l, V l := by
  have hle : (∏ l, if l < j then V l else 1) ≤
      ∏ l ∈ univ.erase j, V l := by
    have heq :
        (∏ l, if l < j then V l else 1) =
          ∏ l ∈ univ.erase j, if l < j then V l else 1 := by
      rw [← prod_erase_mul _ _ (mem_univ j)]
      simp
    rw [heq]
    apply prod_le_prod
    · intro l _
      split_ifs <;> linarith [hV l]
    · intro l _
      split_ifs <;> linarith [hV l]
  have hmul := mul_le_mul_of_nonneg_right hle (by linarith [hV j] : 0 ≤ V j)
  simpa only [prod_erase_mul _ _ (mem_univ j)] using hmul

/-- If the new endpoint is largest, every new squared prefix is controlled
by the full old product times its square. -/
theorem boxSquaredPrefixes_cons_of_largest {i : ℕ} {Q α : ℝ} {V : Fin i → ℝ}
    (hα : 1 ≤ α) (hV : ∀ j, 1 ≤ V j) (hmax : ∀ j, V j ≤ α)
    (hfull : (∏ j, V j) * α ^ 2 ≤ Q) :
    boxSquaredPrefixes Q (Fin.cons α V) := by
  apply (boxSquaredPrefixes_cons_iff (by linarith : 0 < α)).2
  constructor
  · have hp : 1 ≤ ∏ j, V j := one_le_prod (fun j _ => hV j)
    nlinarith [sq_nonneg α]
  · rw [boxSquaredPrefixes_iff]
    intro j
    apply (le_div_iff₀ (by linarith : 0 < α)).2
    have hp := box_prefix_mul_entry_le_product hV j
    have hnon : 0 ≤ ∏ l, if l < j then V l else 1 :=
      prod_nonneg (fun l _ => by split_ifs <;> linarith [hV l])
    calc
      _ = ((∏ l, if l < j then V l else 1) * V j) * (V j * α) := by ring
      _ ≤ (∏ l, V l) * (α * α) := by
        apply mul_le_mul hp
        · nlinarith [hmax j]
        · nlinarith [hV j]
        · exact prod_nonneg (fun l _ => by linarith [hV l])
      _ ≤ Q := by nlinarith [hfull]

/-- Construct a position for insertion and prove all squared prefixes.
The induction keeps preceding old coordinates unchanged and handles the
inserted coordinate and all following coordinates by the full-product bound. -/
theorem exists_sorted_box_insertion {i : ℕ} {Q α : ℝ} {V : Fin i → ℝ}
    (hα : 1 ≤ α) (hV : ∀ j, 1 ≤ V j) (hanti : Antitone V)
    (hprefix : boxSquaredPrefixes Q V) (hfull : (∏ j, V j) * α ^ 2 ≤ Q) :
    ∃ p : Fin (i + 1), Antitone (p.insertNth α V) ∧
      boxSquaredPrefixes Q (p.insertNth α V) := by
  induction i generalizing Q with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · intro a b _
      have hab : a = b := Fin.ext (by omega)
      subst b
      exact le_rfl
    · simpa [boxSquaredPrefixes] using hfull
  | succ i ih =>
    let x := V 0
    let T : Fin i → ℝ := fun j => V j.succ
    have hVeq : V = Fin.cons x T := by ext j; exact (Fin.cases rfl (fun _ => rfl) j)
    have hx : 0 < x := by dsimp [x]; linarith [hV 0]
    have hT : ∀ j, 1 ≤ T j := fun j => hV j.succ
    have hTanti : Antitone T := fun a b hab => hanti (Fin.succ_le_succ_iff.2 hab)
    have hsplit := (boxSquaredPrefixes_cons_iff hx).1 (hVeq ▸ hprefix)
    by_cases hax : x ≤ α
    · refine ⟨0, ?_, ?_⟩
      · rw [Fin.insertNth_zero']
        intro a b hab
        cases a using Fin.cases with
        | zero =>
          cases b using Fin.cases with
          | zero => exact le_rfl
          | succ b' => exact (hanti (Fin.zero_le b')).trans hax
        | succ a' =>
          cases b using Fin.cases with
          | zero => simp at hab
          | succ b' => exact hanti (Fin.succ_le_succ_iff.mp hab)
      · rw [Fin.insertNth_zero']
        exact boxSquaredPrefixes_cons_of_largest hα hV
          (fun j => (hanti (Fin.zero_le j)).trans hax) hfull
    · have hfullT : (∏ j, T j) * α ^ 2 ≤ Q / x := by
        apply (le_div_iff₀ hx).2
        have h := hfull
        rw [hVeq, Fin.prod_univ_succ] at h
        simpa only [Fin.cons_zero, Fin.cons_succ, mul_assoc, mul_comm, mul_left_comm] using h
      obtain ⟨p, hpanti, hpprefix⟩ := ih hT hTanti hsplit.2 hfullT
      refine ⟨p.succ, ?_, ?_⟩ <;> rw [hVeq, Fin.insertNth_succ_cons]
      · have hmax : ∀ j : Fin (i + 1), (p.insertNth α T : Fin (i + 1) → ℝ) j ≤ x := by
          have hbound : p.insertNth α T ≤ fun _ => x :=
            Fin.insertNth_le_iff.2 ⟨(lt_of_not_ge hax).le,
              fun j => hanti (Fin.zero_le j.succ)⟩
          exact hbound
        intro a b hab
        cases a using Fin.cases with
        | zero =>
          cases b using Fin.cases with
          | zero => exact le_rfl
          | succ b' => exact hmax b'
        | succ a' =>
          cases b using Fin.cases with
          | zero => simp at hab
          | succ b' => exact hpanti (Fin.succ_le_succ_iff.mp hab)
      · exact (boxSquaredPrefixes_cons_iff hx).2 ⟨hsplit.1, hpprefix⟩

/-- All original lower endpoints, the inserted lower endpoint, ordering,
and every squared prefix hold in the next actual source family. -/
theorem wuSourceBox_sorted_insertion {i k N : ℕ} {δ Δ α s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (ht : 0 < t) (ht10 : t ≤ 10)
    (hαlo : ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) ≤ α)
    (hαhi : α ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s)) :
    ∃ e : Equiv.Perm (Fin (i + 1)),
      wuSourceBox (k + 1) δ N (i + 1) Δ (Fin.cons α V ∘ e) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < (N : ℝ) ^ (δ ^ (k + 2)) := one_lt_rpow hNr (pow_pos hδ _)
  have hαlow := reboxing_endpoint_lower hN hδ hδhi hb ht ht10 hαlo
  have hα1 : 1 ≤ α := hw.le.trans hαlow
  have hb' := wuSourceBox_mono_depth (Nat.le_succ k) hδ
    (show δ ≤ 1 by linarith) (show 1 ≤ N by omega) hb
  have hVlow : ∀ j, (N : ℝ) ^ (δ ^ (k + 2)) ≤ V j := by
    simpa only [Nat.add_assoc] using hb'.2.2.2.2.1
  have hV1 : ∀ j, 1 ≤ V j := fun j => hw.le.trans (hVlow j)
  have hfull := reboxing_endpoint_squared_product hN hδ hδhi hb hs
    (show 0 ≤ α by linarith) hαhi
  obtain ⟨p, hpanti, hpprefix⟩ := exists_sorted_box_insertion hα1 hV1
    hb.2.2.2.1 hb.2.2.2.2.2 hfull
  refine ⟨p.cycleRange, ?_⟩
  rw [Fin.cons_comp_cycleRange]
  refine ⟨Nat.succ_le_succ hb.1, hb.2.1, hb.2.2.1, hpanti, ?_, hpprefix⟩
  intro j
  rw [← Fin.cons_comp_cycleRange]
  change (N : ℝ) ^ (δ ^ (k + 1 + 1)) ≤ (Fin.cons α V : Fin (i + 1) → ℝ) (p.cycleRange j)
  simpa only [Nat.add_assoc] using
    (Fin.cases hαlow (fun l => hVlow l) (p.cycleRange j))

theorem convolutionWuWindows_cons {i : ℕ} (N : ℕ) (Δ α : ℝ) (V : Fin i → ℝ) :
    convolutionWuWindows N Δ (Fin.cons α V) =
      Fin.cons (primeWindow N (α / Δ) α) (convolutionWuWindows N Δ V) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

/-- The constructed sorting permutation is harmless to the literal
convolution coefficient, including overlapping windows and repeated primes. -/
theorem wuSourceBox_sorted_insertion_convolution {i k N : ℕ} {δ Δ α s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (ht : 0 < t) (ht10 : t ≤ 10)
    (hαlo : ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / t) ≤ α)
    (hαhi : α ≤ ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s)) :
    ∃ e : Equiv.Perm (Fin (i + 1)),
      wuSourceBox (k + 1) δ N (i + 1) Δ (Fin.cons α V ∘ e) ∧
      ∀ d : ℕ,
        convolutionCoeff (convolutionWuWindows N Δ (Fin.cons α V ∘ e)) d =
          ∑ p ∈ primeWindow N (α / Δ) α,
            if p ∣ d then convolutionCoeff (convolutionWuWindows N Δ V) (d / p) else 0 := by
  obtain ⟨e, he⟩ := wuSourceBox_sorted_insertion hN hδ hδhi hb hs ht ht10 hαlo hαhi
  refine ⟨e, he, ?_⟩
  intro d
  rw [convolutionWuWindows_permute, convolutionWuWindows_cons]
  exact convolutionCoeff_insert_permute _ _ e (fun p hp => (mem_primeWindow.mp hp).1.pos) d

end Wu2008DoubleSieve
