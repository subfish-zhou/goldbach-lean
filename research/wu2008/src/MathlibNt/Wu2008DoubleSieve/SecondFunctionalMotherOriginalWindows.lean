import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherFinite
import MathlibNt.Wu2008DoubleSieve.FourthRowMotherOriginalWindows

/-! # Three separate original negative windows and explicit bad-prime errors -/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

theorem secondFunctionalMother_tuples_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q) (r : ℕ) :
    secondFunctionalMotherTuples P r ⊆ secondFunctionalMotherTuples Q r := by
  intro l hl
  obtain ⟨hlen, hord, hm⟩ := (secondFunctionalMother_tuple_mem P r l).mp hl
  exact (secondFunctionalMother_tuple_mem Q r l).mpr ⟨hlen, hord, fun p hp => hPQ (hm p hp)⟩

theorem secondFunctionalMother_prefix_mono (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    secondFunctionalMotherPrefixTerm N d (d*N) a b c e f cs ≤
      secondFunctionalMotherPrefixTerm N d N a b c e f cs := by
  apply sum_le_sum_of_subset_of_nonneg
    (secondFunctionalMother_tuples_mono (fourthRowMother_window_subset N d a f) cs.length)
  intro l _ _
  split_ifs <;> positivity

theorem secondFunctionalMother_list_sum_mono {α : Type*} (L : List α) (F G : α → ℝ)
    (h : ∀ x ∈ L, F x ≤ G x) : (L.map F).sum ≤ (L.map G).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem secondFunctionalMother_restore_windows (N d : ℕ) (a b c e f : ℝ) :
    secondFunctionalMotherLocal N d (d*N) a b c e f ≤
      secondFunctionalMotherLocal N d N a b c e f +
        fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c +
        fourthRowMotherBadPrime N d a e := by
  have h5 := fourthRowMother_pair_mono N d a c a c
  have h6 := fourthRowMother_pair_mono N d a b c e
  have hp := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d (d*N) a b c e f)).sum)
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d N a b c e f)).sum)
    (fun i _ => secondFunctionalMother_list_sum_mono (secondFunctionalMotherGammaWords i)
      _ _ (fun cs _ => secondFunctionalMother_prefix_mono N d a b c e f cs))
  have hf := fourthRowMother_negative_split N d a f
  have hc := fourthRowMother_negative_split N d a c
  have he := fourthRowMother_negative_split N d a e
  rw [secondFunctionalMother_local_expand, secondFunctionalMother_local_expand]
  linarith

theorem secondFunctionalMother_original_windows (N d : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    5 * (sourceSieveCount N d (d*N) f : ℝ) ≤
      secondFunctionalMotherLocal N d N a b c e f +
        fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c +
        fourthRowMotherBadPrime N d a e :=
  (secondFunctionalMother_masked N d hab hbc hce hef).trans
    (secondFunctionalMother_restore_windows N d a b c e f)

/-- Only the raw-to-prefix direction is asserted; the masks are not identified. -/
theorem secondFunctionalMother_raw_subset_prefix (N d : ℕ) (l : List ℕ) :
    sourceSieveCarrier N (d*l.prod) (d*N) (l.getD (l.length-2) 0) ⊆
      secondFunctionalMotherPrefixCarrier N d l := by
  intro ell hell
  obtain ⟨hrange, hprime, hdiv, hs⟩ := mem_filter.mp hell
  apply mem_filter.mpr
  refine ⟨hrange, hprime, hdiv, ?_⟩
  intro q hq hqM hqlt
  exact hs q hq (hqM.of_dvd_right
    (show d*N ∣ d*(l.take (l.length-2)).prod*N from
      ⟨(l.take (l.length-2)).prod, by ring⟩)) hqlt

end Wu2008DoubleSieve
