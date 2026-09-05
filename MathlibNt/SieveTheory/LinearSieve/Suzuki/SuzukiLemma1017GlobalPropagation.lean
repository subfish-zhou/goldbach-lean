import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1017Comparison

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1017Comparison

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A weak envelope on one closed unit interval propagates to the next
closed unit interval.  The proof is genuinely over the reals: if the envelope
first failed, compactness supplies a first nonnegative point; continuity makes
it an equality point, while Claim 10.18 makes it strict. -/
theorem propagate_one_unit
    {P Q : ℝ → ℝ} (h : SignedPQData P Q) {ρ a : ℝ}
    (hρ : 0 < ρ) (ha : 4 ≤ a)
    (hprev : ∀ t ∈ Icc (a - 1) a, |P t| ≤ ρ * Q t) :
    ∀ t ∈ Icc a (a + 1), |P t| ≤ ρ * Q t := by
  let F : ℝ → ℝ := fun t => |P t| - ρ * Q t
  have hFcont : Continuous F :=
    h.continuousP.abs.sub (continuous_const.mul h.continuousQ)
  have ha_strict : F a < 0 := by
    dsimp [F]
    have := claim10_18_one_step_strict h hρ (by linarith) hprev
    linarith
  intro x hx
  by_contra hfail
  have hFx : 0 < F x := by
    dsimp [F]
    push_neg at hfail
    linarith
  let B : Set ℝ := Icc a x ∩ F ⁻¹' Ici 0
  have hBcompact : IsCompact B :=
    isCompact_Icc.inter_right (isClosed_Ici.preimage hFcont)
  have hxB : x ∈ B := by
    constructor
    · exact ⟨hx.1, le_rfl⟩
    · exact hFx.le
  obtain ⟨c, hcB, hcmin⟩ :=
    hBcompact.exists_isMinOn ⟨x, hxB⟩ continuousOn_id
  have hcax : c ∈ Icc a x := hcB.1
  have hFc_nonneg : 0 ≤ F c := hcB.2
  have hac : a < c := by
    rcases lt_or_eq_of_le hcax.1 with hac | rfl
    · exact hac
    · linarith
  have hFc_nonpos : F c ≤ 0 := by
    by_contra hposnot
    have hFcpos : 0 < F c := lt_of_not_ge hposnot
    have hzmem : (0 : ℝ) ∈ Icc (F a) (F c) := ⟨ha_strict.le, hFcpos.le⟩
    obtain ⟨d, hdac, hFd⟩ :=
      (intermediate_value_Icc hac.le (hFcont.continuousOn)) hzmem
    have hdB : d ∈ B := by
      constructor
      · exact ⟨hdac.1, hdac.2.trans hcax.2⟩
      · simpa [hFd]
    have hcd : c ≤ d := hcmin hdB
    have hdc : d < c := lt_of_le_of_ne hdac.2 (by
      intro hdc
      subst d
      linarith)
    linarith
  have hFc : F c = 0 := le_antisymm hFc_nonpos hFc_nonneg
  have hc_upper : c ≤ a + 1 := hcax.2.trans hx.2
  have hcwindow : ∀ t ∈ Icc (c - 1) c, |P t| ≤ ρ * Q t := by
    intro t ht
    have hFt : F t ≤ 0 := by
      by_cases hta : t ≤ a
      · have htprev : t ∈ Icc (a - 1) a := by
          constructor
          · linarith [ht.1, hc_upper]
          · exact hta
        dsimp [F]
        linarith [hprev t htprev]
      · have hat : a < t := lt_of_not_ge hta
        by_cases htc : t = c
        · simpa [htc, hFc]
        · have htc_lt : t < c := lt_of_le_of_ne ht.2 htc
          by_contra hnot
          have hFt0 : 0 ≤ F t := le_of_not_ge hnot
          have htB : t ∈ B := by
            constructor
            · exact ⟨hat.le, htc_lt.le.trans hcax.2⟩
            · exact hFt0
          exact (not_le_of_gt htc_lt) (hcmin htB)
    dsimp [F] at hFt
    linarith
  have hc3 : 3 ≤ c := by linarith
  have hcstrict := claim10_18_one_step_strict h hρ hc3 hcwindow
  dsimp [F] at hFc
  linarith

/-- A compact strict seed on `[3,4]` propagates to every real `s ≥ 3`.
The natural-number induction is only used to cover successive real unit
intervals; `propagate_one_unit` proves every point of each interval. -/
theorem global_eta_of_compact_seed
    {P Q : ℝ → ℝ} (h : SignedPQData P Q)
    (hpoint : ∀ t ∈ Icc (3 : ℝ) 4, |P t| < Q t) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ s, 3 ≤ s → |P s| ≤ η * Q s := by
  obtain ⟨η, hη, hη1, hseed, _⟩ :=
    compact_eta_and_one_step h (a := (4 : ℝ)) (by norm_num) (by
      intro t ht
      apply hpoint t
      constructor <;> linarith [ht.1, ht.2])
  refine ⟨η, hη, hη1, ?_⟩
  have hcovered : ∀ n : ℕ, ∀ t ∈ Icc (3 : ℝ) (4 + n), |P t| ≤ η * Q t := by
    intro n
    induction n with
    | zero =>
        intro t ht
        norm_num at ht
        apply hseed t
        constructor
        · norm_num
          exact ht.1
        · exact ht.2
    | succ n ih =>
        have ha : (4 : ℝ) ≤ 4 + n := by
          exact le_add_of_nonneg_right (Nat.cast_nonneg n)
        have hprev : ∀ t ∈ Icc ((4 + (n : ℝ)) - 1) (4 + n),
            |P t| ≤ η * Q t := by
          intro t ht
          apply ih t
          constructor
          · linarith [ht.1]
          · exact ht.2
        have hnext := propagate_one_unit h hη ha hprev
        intro t ht
        rw [Nat.cast_succ] at ht
        by_cases hta : t ≤ 4 + (n : ℝ)
        · exact ih t ⟨ht.1, hta⟩
        · apply hnext t
          constructor
          · exact le_of_not_ge hta
          · linarith [ht.2]
  intro s hs
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (s - 4)
  exact hcovered n s ⟨hs, by exact_mod_cast (show s ≤ 4 + (n : ℝ) by linarith)⟩

/-- Lemma 10.17, source-facing global endpoint.  Positivity of the two hat
layers automatically supplies the compact seed; no global `P/Q` comparison is
assumed. -/
theorem lemma10_17_global_uniform_eta
    {Tplus Tminus P Q : ℝ → ℝ} (h : SignedPQData P Q)
    (hP : P = fun s => Tplus s - Tminus s)
    (hQ : Q = fun s => Tplus s + Tminus s)
    (hp_pos : ∀ s ∈ Icc (3 : ℝ) 4, 0 < Tplus s)
    (hm_pos : ∀ s ∈ Icc (3 : ℝ) 4, 0 < Tminus s) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ s, 3 ≤ s → |P s| ≤ η * Q s := by
  apply global_eta_of_compact_seed h
  intro s hs
  rw [hP, hQ, abs_lt]
  simp only [Pi.sub_apply, Pi.add_apply]
  constructor <;> linarith [hp_pos s hs, hm_pos s hs]


end Section10Lemma1017Comparison
