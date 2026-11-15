import HodgeLean.Foundations.Program.G32Native.PairedConormalStabilization

/-! # A presentation from a lift of the original quotient arrow -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program.G32Native

/-- Two original exact sequences with a common quotient and a specified
lift give a presentation of the original middle object. Both its source
inclusion and its last relation coefficient are retained. -/
theorem paired_c3_presentation_of_quotient_lift
    {C : Type*} [Category* C] [Abelian C]
    {A M I F T : C} (f : A ⟶ M) (g : M ⟶ T) (i : I ⟶ F) (q : F ⟶ T)
    (hfg : f ≫ g = 0) (hiq : i ≫ q = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hT : (ShortComplex.mk i q hiq).ShortExact)
    (l : F ⟶ M) (hl : l ≫ g = q) :
    ∃ (u : I ⟶ A ⊞ F) (v : A ⊞ F ⟶ M) (huv : u ≫ v = 0),
      (ShortComplex.mk u v huv).ShortExact ∧
      u ≫ biprod.snd = i ∧ biprod.inl ≫ v = f ∧ biprod.inr ≫ v = l := by
  obtain ⟨a, b, ha, hb, haf, hbi, hP, hM⟩ :=
    paired_quotient_stabilization f g i q hfg hiq hS hT
  let s : F ⟶ pullback g q := pullback.lift l (𝟙 F) (by rw [hl, Category.id_comp])
  have hs : s ≫ pullback.snd g q = 𝟙 F := pullback.lift_snd _ _ _
  let split := ShortComplex.Splitting.ofExactOfSection
    (ShortComplex.mk a (pullback.snd g q) ha) hP.exact s hs hP.mono_f
  let e := split.isoBinaryBiproduct
  have he : a ≫ e.hom = biprod.inl := by
    apply biprod.hom_ext
    · simp only [Category.assoc, e, ShortComplex.Splitting.isoBinaryBiproduct_hom,
        biprod.lift_fst, biprod.inl_fst]
      exact split.f_r
    · simp only [Category.assoc, e, ShortComplex.Splitting.isoBinaryBiproduct_hom,
        biprod.lift_snd, biprod.inl_snd]
      exact ha
  let u := b ≫ e.hom
  let v := e.inv ≫ pullback.fst g q
  have huv : u ≫ v = 0 := by
    dsimp only [u, v]
    rw [Category.assoc, Iso.hom_inv_id_assoc, hb]
  let es : ShortComplex.mk b (pullback.fst g q) hb ≅ ShortComplex.mk u v huv :=
    ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by
      change 𝟙 _ ≫ u = b ≫ e.hom
      exact Category.id_comp u) (by
      change e.hom ≫ (e.inv ≫ pullback.fst g q) = pullback.fst g q ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
  refine ⟨u, v, huv, ShortComplex.shortExact_of_iso es hM, ?_, ?_, ?_⟩
  · dsimp only [u, e]
    rw [Category.assoc, ShortComplex.Splitting.isoBinaryBiproduct_hom,
      biprod.lift_snd, hbi]
  · rw [← he]
    dsimp only [v]
    rw [Category.assoc, Iso.hom_inv_id_assoc, haf]
  · change biprod.inr ≫ (split.isoBinaryBiproduct.inv ≫ pullback.fst g q) = l
    rw [ShortComplex.Splitting.isoBinaryBiproduct_inv, biprod.inr_desc_assoc]
    exact pullback.lift_fst _ _ _

#print axioms paired_c3_presentation_of_quotient_lift
end HodgeLean.Foundations.Program.G32Native
