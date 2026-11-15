import HodgeLean.Foundations.AnalyticDivisorAlgebraic22OrbitDefs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

theorem gaga22_compact_incidence_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (K : Set (Fin g → ℂ)) (hK : IsCompact K) :
    {C : gaga21_GlobalComponent V f | (gaga21_componentCarrier C ∩ K).Nonempty}.Finite := by
  classical
  choose W hW hWfin using fun q : Fin g → ℂ ↦
    gaga21_finite_incidence hD q (mem_univ q)
  let O : (Fin g → ℂ) → Set (Fin g → ℂ) := fun q ↦ interior (W q)
  let A : (Fin g → ℂ) → Set (gaga21_GlobalComponent V f) := fun q ↦
    {C | (gaga21_componentCarrier C ∩ O q).Nonempty}
  have hqO : ∀ q, q ∈ O q := fun q ↦ mem_interior_iff_mem_nhds.mpr (hW q)
  have hAfin : ∀ q, (A q).Finite := fun q ↦
    (hWfin q).subset fun _ ⟨x, hxC, hxO⟩ ↦
      ⟨x, hxC, interior_subset hxO⟩
  obtain ⟨s, hsK⟩ := hK.elim_finite_subcover O
    (fun _ ↦ isOpen_interior) (fun q _ ↦ mem_iUnion.mpr ⟨q, hqO q⟩)
  apply (s.finite_toSet.biUnion fun q _ ↦ hAfin q).subset
  rintro C ⟨x, hxC, hxK⟩
  obtain ⟨q, hqs, hxW⟩ := mem_iUnion₂.mp (hsK hxK)
  exact mem_iUnion₂.mpr ⟨q, hqs, ⟨x, hxC, hxW⟩⟩

theorem gaga22_finite_orbits_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    [CompactSpace ((Fin g → ℂ) ⧸ Λ)] :
    Finite (gaga22_ComponentOrbit Λ hD hper) := by
  classical
  let π : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ := QuotientAddGroup.mk
  choose L hLc hxL using fun x : Fin g → ℂ ↦ exists_compact_mem_nhds x
  let U : (Fin g → ℂ) → Set ((Fin g → ℂ) ⧸ Λ) :=
    fun x ↦ π '' interior (L x)
  have hUo : ∀ x, IsOpen (U x) := fun x ↦
    QuotientAddGroup.isOpenMap_coe (interior (L x)) isOpen_interior
  have hUcover : (univ : Set ((Fin g → ℂ) ⧸ Λ)) ⊆ ⋃ x, U x := by
    intro q _
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact mem_iUnion.mpr ⟨x, ⟨x, mem_interior_iff_mem_nhds.mpr (hxL x), rfl⟩⟩
  obtain ⟨s, hscover⟩ := isCompact_univ.elim_finite_subcover U hUo hUcover
  let K : Set (Fin g → ℂ) := ⋃ x ∈ s, L x
  have hKc : IsCompact K := s.finite_toSet.isCompact_biUnion fun x _ ↦ hLc x
  have hπK : ∀ x, ∃ y ∈ K, π y = π x := by
    intro x
    have hxU : π x ∈ ⋃ q ∈ s, U q := hscover (mem_univ (π x))
    obtain ⟨q, hqs, y, hyL, hyx⟩ := mem_iUnion₂.mp hxU
    exact ⟨y, mem_iUnion₂.mpr ⟨q, hqs, interior_subset hyL⟩, hyx⟩
  let S := {C : gaga21_GlobalComponent V f |
    (gaga21_componentCarrier C ∩ K).Nonempty}
  have hSfin : S.Finite := gaga22_compact_incidence_aux Λ hD hper K hKc
  letI : Fintype S := hSfin.fintype
  letI : Finite S := Finite.of_fintype S
  let toOrbit : S → gaga22_ComponentOrbit Λ hD hper := fun C ↦ Quotient.mk _ C.1
  apply Finite.of_surjective toOrbit
  intro O
  let C : gaga21_GlobalComponent V f := Quotient.out O
  obtain ⟨x, hxC⟩ := (gaga21_carrier_geometry hD C).1
  obtain ⟨y, hyK, hyx⟩ := hπK x
  have hlmem : y - x ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hyx
  let l : Λ := ⟨y - x, hlmem⟩
  let C' := gaga22_translateComponent Λ hD hper l C
  have hyC' : y ∈ gaga21_componentCarrier C' := by
    rw [gaga22_carrier_translate Λ hD hper l C]
    refine ⟨x, hxC, ?_⟩
    simp [l]
  refine ⟨⟨C', ⟨y, hyC', hyK⟩⟩, ?_⟩
  change Quotient.mk _ C' = O
  rw [← Quotient.out_eq O]
  apply Quotient.sound
  letI := gaga22_componentAction Λ hD hper
  exact AddAction.mem_orbit C l

theorem gaga22_descended_representative_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (C : gaga21_GlobalComponent V f) :
    (gaga22_descendedDivisor Λ hD hper).carrier (Quotient.mk _ C) =
      (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) '' gaga21_componentCarrier C ∧
    (gaga22_descendedDivisor Λ hD hper).multiplicity (Quotient.mk _ C) =
      (gaga21_gluedDivisor V f).multiplicity C := by
  letI := gaga22_componentAction Λ hD hper
  let D : gaga21_GlobalComponent V f :=
    Quotient.out (Quotient.mk (gaga22_orbitSetoid Λ hD hper) C)
  have hout : (gaga22_orbitSetoid Λ hD hper).r
      D C :=
    Quotient.exact (Quotient.out_eq (Quotient.mk (gaga22_orbitSetoid Λ hD hper) C))
  obtain ⟨l, hl⟩ := AddAction.mem_orbit_iff.mp hout
  change gaga22_translateComponent Λ hD hper l C = D at hl
  change
    (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) ''
          gaga21_componentCarrier D =
        QuotientAddGroup.mk '' gaga21_componentCarrier C ∧
      (gaga21_gluedDivisor V f).multiplicity D =
        (gaga21_gluedDivisor V f).multiplicity C
  constructor
  · rw [← hl, gaga22_carrier_translate Λ hD hper]
    ext q
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using l.property)⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z + (l : Fin g → ℂ), ⟨z, hz, rfl⟩, ?_⟩
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using l.property)
  · rw [← hl, gaga22_weight_translate Λ hD hper]

theorem gaga22_localDivisorSupport_add_iff {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (p : Fin g → ℂ) :
    p + l ∈ localDivisorSupport V f ↔ p ∈ localDivisorSupport V f := by
  have hfwd : ∀ (m : Λ) (z : Fin g → ℂ), z ∈ localDivisorSupport V f →
      z + m ∈ localDivisorSupport V f := by
    intro m z hz
    obtain ⟨i, hzi, hfz⟩ := hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hD.2.1.symm ▸ mem_univ (z + m))
    obtain ⟨u, -, hu, he⟩ := hper m i j z hzi hzj
    refine ⟨j, hzj, ?_⟩
    have hez := he.self_of_nhds
    change f i z = u z * f j (z + m) at hez
    exact (mul_eq_zero.mp (hez.symm.trans hfz)).resolve_left hu
  constructor
  · intro hp
    have h := hfwd (-l) (p + l) hp
    simpa only [AddSubgroup.coe_neg, add_neg_cancel_right] using h
  · exact hfwd l p

theorem gaga22_regularSupport_add {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) {p : Fin g → ℂ} (hp : p ∈ gaga21_regularSupport V f) :
    p + l ∈ gaga21_regularSupport V f := by
  rcases hp with ⟨hps, h, ha, h0, hd, he⟩
  refine ⟨(gaga22_localDivisorSupport_add_iff Λ hD hper l p).2 hps,
    fun z ↦ h (z - l), ?_, ?_, ?_, ?_⟩
  · exact ha.comp_of_eq (analyticAt_id.sub analyticAt_const) (add_sub_cancel_right p l)
  · simpa only [add_sub_cancel_right] using h0
  · simpa only [fderiv_comp_sub, add_sub_cancel_right] using hd
  · have ht : Tendsto (fun z : Fin g → ℂ ↦ z - l) (𝓝 (p + l)) (𝓝 p) :=
      (continuous_id.sub continuous_const).tendsto' (p + l) p (add_sub_cancel_right p l)
    filter_upwards [ht.eventually he] with z hz
    rw [← hz]
    simpa only [sub_add_cancel] using
      (gaga22_localDivisorSupport_add_iff Λ hD hper l (z - l))

theorem gaga22_descended_support_aux {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    :
    (∀ O, 0 < (gaga22_descendedDivisor Λ hD hper).multiplicity O) ∧
    (⋃ O, (gaga22_descendedDivisor Λ hD hper).carrier O) =
      (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) '' localDivisorSupport V f ∧
    Function.Injective (gaga22_descendedDivisor Λ hD hper).carrier := by
  constructor
  · intro O
    refine Quotient.inductionOn O fun C ↦ ?_
    rw [(gaga22_descended_representative_aux Λ hD hper C).2]
    exact gaga21_glued_positive V f C
  constructor
  · ext q
    constructor
    · intro hq
      obtain ⟨O, hqO⟩ := mem_iUnion.mp hq
      refine Quotient.inductionOn O (fun C hqC ↦ ?_) hqO
      rw [(gaga22_descended_representative_aux Λ hD hper C).1] at hqC
      obtain ⟨p, hpC, rfl⟩ := hqC
      exact ⟨p, gaga21_b2_carrier_support hD C hpC, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨a, rfl⟩ := gaga21_b2_occurrence hD hp
      apply mem_iUnion.mpr
      refine ⟨Quotient.mk _ (Quotient.mk _ a), ?_⟩
      rw [(gaga22_descended_representative_aux Λ hD hper
        (Quotient.mk (gaga21_componentSetoid V f) a)).1]
      exact ⟨a.point, ⟨a, rfl, rfl⟩, rfl⟩
  · intro O P hOP
    revert P
    refine Quotient.inductionOn O ?_
    intro C P hOP
    refine Quotient.inductionOn P (fun D hCD ↦ ?_) hOP
    rw [(gaga22_descended_representative_aux Λ hD hper C).1,
      (gaga22_descended_representative_aux Λ hD hper D).1] at hCD
    obtain ⟨x, hxS, hxC⟩ := (gaga21_b2_regular_connected hD C).1
    have hxq : (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) x ∈
        QuotientAddGroup.mk '' gaga21_componentCarrier D := by
      rw [← hCD]
      exact ⟨x, hxC, rfl⟩
    obtain ⟨y, hyD, hyx⟩ := hxq
    have hmem : y - x ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp hyx
    let l : Λ := ⟨y - x, hmem⟩
    have hyl : x + (l : Fin g → ℂ) = y := by
      simp only [l, add_sub_cancel]
    have hyT : y ∈ gaga21_componentCarrier (gaga22_translateComponent Λ hD hper l C) := by
      rw [gaga22_carrier_translate Λ hD hper l C]
      exact ⟨x, hxC, hyl⟩
    obtain ⟨a, haT, hay⟩ := hyT
    obtain ⟨b, hbD, hby⟩ := hyD
    have hyr : y ∈ gaga21_regularSupport V f := by
      rw [← hyl]
      exact gaga22_regularSupport_add Λ hD hper l hxS
    have hTD : gaga22_translateComponent Λ hD hper l C = D := by
      rw [← haT, ← hbD]
      exact gaga21_f2_regular_class hD a b (hby.trans hay.symm) (hay.symm ▸ hyr)
    apply Quotient.sound
    apply (gaga22_orbitSetoid Λ hD hper).symm
    letI := gaga22_componentAction Λ hD hper
    exact AddAction.mem_orbit_iff.mpr ⟨l, hTD⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
