import HodgeLean.Foundations.AnalyticDivisorAlgebraic22Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

private theorem gaga22_localDivisorSupport_add_iff {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ))
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (p : Fin g → ℂ) :
    p + l ∈ localDivisorSupport V f ↔ p ∈ localDivisorSupport V f := by
  obtain ⟨i, hi⟩ : ∃ i, p ∈ V i := by
    apply mem_iUnion.mp
    rw [hD.2.1]
    exact mem_univ p
  obtain ⟨j, hj⟩ : ∃ j, p + l ∈ V j := by
    apply mem_iUnion.mp
    rw [hD.2.1]
    exact mem_univ (p + l)
  obtain ⟨u, _, hu, he⟩ := hper l i j p hi hj
  have hep : f i p = u p * f j (p + l) := he.self_of_nhds
  have zero_iff {q : Fin g → ℂ} {k m : ι} (hqk : q ∈ V k) (hqm : q ∈ V m) :
      f k q = 0 ↔ f m q = 0 := by
    obtain ⟨v, _, hv, hev⟩ := hD.2.2.2.2 k m q ⟨hqk, hqm⟩
    have heq : f k q = v q * f m q := hev.self_of_nhds
    constructor
    · intro hz
      rw [hz] at heq
      exact (mul_eq_zero.mp heq.symm).resolve_left hv
    · intro hz
      rw [heq, hz, mul_zero]
  constructor
  · rintro ⟨k, hk, hz⟩
    have hzj : f j (p + l) = 0 := (zero_iff hk hj).mp hz
    exact ⟨i, hi, by rw [hep, hzj, mul_zero]⟩
  · rintro ⟨k, hk, hz⟩
    have hzi : f i p = 0 := (zero_iff hk hi).mp hz
    refine ⟨j, hj, ?_⟩
    rw [hzi] at hep
    exact (mul_eq_zero.mp hep.symm).resolve_left hu

private theorem gaga22_regularSupport_add {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) {p : Fin g → ℂ} (hp : p ∈ gaga21_regularSupport V f) :
    p + l ∈ gaga21_regularSupport V f := by
  rcases hp with ⟨hps, h, hha, hh0, hhd, he⟩
  refine ⟨(gaga22_localDivisorSupport_add_iff Λ hD hper l p).2 hps,
    (fun z ↦ h (z - l)), ?_, ?_, ?_, ?_⟩
  · exact hha.comp_of_eq (analyticAt_id.sub analyticAt_const) (add_sub_cancel_right p l)
  · simpa only [add_sub_cancel_right] using hh0
  · rw [fderiv_comp_sub]
    simpa only [add_sub_cancel_right] using hhd
  · have ht : Tendsto (fun z : Fin g → ℂ ↦ z - l) (𝓝 (p + l)) (𝓝 p) := by
      have hc : Continuous (fun z : Fin g → ℂ ↦ z - (l : Fin g → ℂ)) :=
        continuous_id.sub continuous_const
      simpa only [add_sub_cancel_right] using hc.tendsto (p + l)
    filter_upwards [ht.eventually he] with z hz
    have hs := gaga22_localDivisorSupport_add_iff Λ hD hper l (z - l)
    simpa only [sub_add_cancel] using hs.trans hz

theorem gaga22_continuation_translate_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a b : gaga21_LocalFactorOccurrence V f)
    (hab : gaga21_continuation a b) :
    gaga21_continuation (gaga22_translateOccurrence Λ hD hper l a)
      (gaga22_translateOccurrence Λ hD hper l b) := by
  rcases hab with ⟨R, hRc, hRS, ha, hb⟩
  refine ⟨(fun z ↦ z + (l : Fin g → ℂ)) '' R,
    hRc.image (fun z ↦ z + (l : Fin g → ℂ))
      (show ContinuousOn (fun z : Fin g → ℂ ↦ z + (l : Fin g → ℂ)) R from
        (continuous_id.add continuous_const).continuousOn), ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact gaga22_regularSupport_add Λ hD hper l (hRS hz)
  have htransport (c : gaga21_LocalFactorOccurrence V f)
      (hc : ∀ᶠ y in 𝓝 c.point,
        c.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R) :
      ∀ᶠ z in 𝓝 (gaga22_translateOccurrence Λ hD hper l c).point,
        (gaga22_translateOccurrence Λ hD hper l c).factor z = 0 →
        z ∈ gaga21_regularSupport V f →
        z ∈ (fun y ↦ y + (l : Fin g → ℂ)) '' R := by
    have ht : Tendsto (fun z : Fin g → ℂ ↦ z - l) (𝓝 (c.point + l)) (𝓝 c.point) := by
      have hcont : Continuous (fun z : Fin g → ℂ ↦ z - (l : Fin g → ℂ)) :=
        continuous_id.sub continuous_const
      simpa only [add_sub_cancel_right] using hcont.tendsto (c.point + l)
    filter_upwards [ht.eventually hc] with z hz hzf hzreg
    refine ⟨z - l, hz ?_ ?_, sub_add_cancel z l⟩
    · exact hzf
    · exact gaga22_regularSupport_add Λ hD hper (-l) (by simpa using hzreg)
  · exact htransport a ha
  · have ht : Tendsto (fun z : Fin g → ℂ ↦ z - l) (𝓝 (b.point + l)) (𝓝 b.point) := by
      have hcont : Continuous (fun z : Fin g → ℂ ↦ z - (l : Fin g → ℂ)) :=
        continuous_id.sub continuous_const
      simpa only [add_sub_cancel_right] using hcont.tendsto (b.point + l)
    filter_upwards [ht.eventually hb] with z hz hzf hzreg
    refine ⟨z - l, hz ?_ ?_, sub_add_cancel z l⟩
    · exact hzf
    · exact gaga22_regularSupport_add Λ hD hper (-l) (by simpa using hzreg)

theorem gaga22_translateComponent_mk_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a : gaga21_LocalFactorOccurrence V f) :
    gaga22_translateComponent Λ hD hper l (Quotient.mk _ a) =
      Quotient.mk _ (gaga22_translateOccurrence Λ hD hper l a) := by
  unfold gaga22_translateComponent
  generalize hx : Quotient.out (Quotient.mk (gaga21_componentSetoid V f) a) = x
  apply Quotient.sound
  have ha : Relation.EqvGen gaga21_continuation x a := by
    apply (@Quotient.exact _ (gaga21_componentSetoid V f) x a)
    rw [← hx]
    exact Quotient.out_eq _
  clear hx
  induction ha with
  | rel c d hcd =>
      exact Relation.EqvGen.rel _ _ (gaga22_continuation_translate_aux Λ hD hper l c d hcd)
  | refl c => exact Relation.EqvGen.refl _
  | symm c d _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans c d e _ _ ihcd ihde => exact Relation.EqvGen.trans _ _ _ ihcd ihde

private theorem gaga22_mk_eq_of_factor_germ {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f) (a b : gaga21_LocalFactorOccurrence V f)
    (hp : b.point = a.point)
    (he : ∀ᶠ z in 𝓝 a.point, b.factor z = 0 ↔ a.factor z = 0) :
    Quotient.mk (gaga21_componentSetoid V f) a =
      Quotient.mk (gaga21_componentSetoid V f) b := by
  let C : gaga21_GlobalComponent V f := Quotient.mk _ a
  let R := gaga21_regularSupport V f ∩ gaga21_componentCarrier C
  have hRc : IsConnected R := (gaga21_carrier_geometry hD C).2.2.2.1
  have ha := gaga21_br_germ_in_carrier hD a
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨R, hRc, inter_subset_left, ?_, ?_⟩
  · filter_upwards [ha] with z hz hzf hzreg
    exact ⟨hzreg, hz hzf⟩
  · rw [hp]
    filter_upwards [ha, he] with z hz hez hzf hzreg
    exact ⟨hzreg, hz (hez.mp hzf)⟩

theorem gaga22_translation_laws_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    :
    (∀ C, gaga22_translateComponent Λ hD hper 0 C = C) ∧
    (∀ (l m : Λ) C, gaga22_translateComponent Λ hD hper (l + m) C =
      gaga22_translateComponent Λ hD hper l (gaga22_translateComponent Λ hD hper m C)) := by
  constructor
  · intro C
    refine Quotient.inductionOn C ?_
    intro a
    rw [gaga22_translateComponent_mk_aux]
    apply gaga22_mk_eq_of_factor_germ hD
    · rw [show (gaga22_translateOccurrence Λ hD hper 0 a).point =
          a.point + (0 : Λ) from rfl]
      simp
    · exact Eventually.of_forall fun z ↦ by
        rw [show (gaga22_translateOccurrence Λ hD hper 0 a).factor z =
          a.factor (z - (0 : Λ)) from rfl]
        simp
  · intro l m C
    refine Quotient.inductionOn C ?_
    intro a
    rw [gaga22_translateComponent_mk_aux, gaga22_translateComponent_mk_aux,
      gaga22_translateComponent_mk_aux]
    apply gaga22_mk_eq_of_factor_germ hD
    · change (a.point + (m : Fin g → ℂ)) + l = a.point + (l + m : Λ)
      simp only [AddSubgroup.coe_add]
      abel
    · exact Eventually.of_forall fun z ↦ by
        change a.factor ((z - (l : Fin g → ℂ)) - m) = 0 ↔
          a.factor (z - (l + m : Λ)) = 0
        simp only [AddSubgroup.coe_add]
        abel_nf

theorem gaga22_carrier_translate_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) :
    gaga21_componentCarrier (gaga22_translateComponent Λ hD hper l C) =
      (fun z ↦ z + (l : Fin g → ℂ)) '' gaga21_componentCarrier C := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := hq
    let b := gaga22_translateOccurrence Λ hD hper (-l) a
    have hbpoint : b.point + (l : Fin g → ℂ) = a.point := by
      simp only [b, AddSubgroup.coe_neg, gaga22_translateOccurrence, neg_add_cancel_right]
    refine ⟨b.point, ?_, hbpoint⟩
    refine ⟨b, ?_, rfl⟩
    rw [← gaga22_translateComponent_mk_aux Λ hD hper (-l) a, ha]
    calc
      gaga22_translateComponent Λ hD hper (-l)
          (gaga22_translateComponent Λ hD hper l C) =
          gaga22_translateComponent Λ hD hper 0 C := by
            symm
            simpa only [neg_add_cancel] using
              (gaga22_translation_laws_aux Λ hD hper).2 (-l) l C
      _ = C := (gaga22_translation_laws_aux Λ hD hper).1 C
  · rintro q ⟨p, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨gaga22_translateOccurrence Λ hD hper l a, ?_, rfl⟩
    rw [← gaga22_translateComponent_mk_aux Λ hD hper l a, ha]

theorem gaga22_weight_translate_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) :
    (gaga21_gluedDivisor V f).multiplicity (gaga22_translateComponent Λ hD hper l C) =
      (gaga21_gluedDivisor V f).multiplicity C := by
  let a := Quotient.out C
  let b := gaga22_translateOccurrence Λ hD hper l a
  calc
    (gaga21_gluedDivisor V f).multiplicity
        (gaga22_translateComponent Λ hD hper l C) = b.exponents b.selected := by
          exact gaga21_glued_multiplicity hD b
    _ = a.exponents a.selected := rfl
    _ = (gaga21_gluedDivisor V f).multiplicity (Quotient.mk _ a) :=
      (gaga21_glued_multiplicity hD a).symm
    _ = (gaga21_gluedDivisor V f).multiplicity C := by rw [Quotient.out_eq]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
