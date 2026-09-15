import W01WeightedGain
import MixedFinalNormalization

noncomputable section
namespace WuTarget.W01
open Wu2008DoubleSieve NodeExtension Filter
open scoped Classical Topology

theorem B_normalization {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        (truncatedSixthLowerF6lin+lowGain x-ε)*truncatedSixthMassScale N ≤
          LowComplement.B N n δ := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,hahi,hFa⟩ := truncatedSixthZeroDelta_Fdelta_close he
  obtain ⟨b,hb,hb0,_,hHb⟩ := lowGain_Hadm_payment hn hd0 hx he
  refine ⟨min a b, lt_min ha hb, (min_le_right _ _).trans hb0,
    (min_le_left _ _).trans hahi, ?_⟩
  intro δ hδ hδd
  have hδa := hδd.trans_le (min_le_left a b)
  have hδb := hδd.trans_le (min_le_right a b)
  have hF := (abs_lt.mp (hFa δ hδ hδa)).1
  have hH := hHb δ hδ hδb
  filter_upwards [LowComplement.B_delta_normalization hδ (hδa.trans_le hahi) he] with n hn
  filter_upwards [hn, eventually_ge_atTop (4:ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [hF,hH])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

/-- Low replacement, high replacement and eta payment share delta, grid and count scale. -/
theorem mixed_normalization {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
        ∀ δ : ℝ, 0 < δ → δ < d → ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          (truncatedSixthLowerF6lin+lowGain x+HighConsumer.highGain-ε)*
            truncatedSixthMassScale N ≤ MixedSixth.main N n δ η := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a,ha,ha0,hahi,hB⟩ := B_normalization hn hd0 hx he
  obtain ⟨b,hb,hE⟩ := HighIncrement.actual_highGain_lower he
  obtain ⟨η,hη,hη1,hpay⟩ := LowComplement.uniform_eta_payment_capped he
  refine ⟨η,hη,hη1,min a b,lt_min ha hb,
    (min_le_left _ _).trans ha0,(min_le_left _ _).trans hahi,?_⟩
  intro δ hδ hδd
  obtain ⟨n0,hn0⟩ := hE δ hδ.le (hδd.le.trans (min_le_right _ _))
  have hEn := eventually_atTop.mpr ⟨n0,hn0⟩
  filter_upwards [hB δ hδ (hδd.trans_le (min_le_left _ _)),hEn] with n hBn hEn
  filter_upwards [hBn,hEn,hpay] with N hBN hEN hηN
  have hp := hηN δ hδ.le n
  unfold LowComplement.B at hBN
  linarith only [hBN,hEN,hp]

theorem actual_sixth {x : Fin 9 → ℝ} {d0 ε : ℝ}
    (hn : ∀ i, 0 ≤ x i) (hd0 : 0 < d0)
    (hx : ∀ δ : ℝ, 0 < δ → δ ≤ d0 → ∀ i, x i ≤ actualNine δ i)
    (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ d ≤ d0 ∧ d ≤ 1/100 ∧
      ∀ δ : ℝ, 0 < δ → δ < d →
        ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
          (truncatedSixthLowerF6lin+lowGain x+HighConsumer.highGain-ε)*
            U8CanonicalMother.M N ≤ SixthSlotCore.sixth N := by
  obtain ⟨η,hη,hη1,a,ha,ha0,ha1,hm⟩ := mixed_normalization hn hd0 hx (half_pos hε)
  refine ⟨min a (50*HighBoxRecovery.highEta),
    lt_min ha (by norm_num [HighBoxRecovery.highEta]),
    (min_le_left _ _).trans ha0,(min_le_left _ _).trans ha1,?_⟩
  intro δ hδ hδd
  have hda := hδd.trans_le (min_le_left _ _)
  have hdhi := hδd.le.trans (min_le_right _ _)
  obtain ⟨n,hn⟩ := (hm δ hδ hda).exists
  obtain ⟨Tm,hTm⟩ := eventually_atTop.mp hn
  obtain ⟨Tc,hTc,hc⟩ := MixedSixth.actual_count hδ hdhi (hda.trans_le ha1)
    hη hη1 (half_pos hε) n
  refine ⟨max Tm Tc,hTc.trans (le_max_right _ _),?_⟩
  intro N hN he
  have hmN := hTm N ((le_max_left _ _).trans hN)
  have hcN := hc N ((le_max_right _ _).trans hN) he
  change (truncatedSixthLowerF6lin+lowGain x+HighConsumer.highGain-ε/2)*
    U8CanonicalMother.M N ≤ MixedSixth.main N n δ η at hmN
  linarith only [hmN,hcN]

end WuTarget.W01
