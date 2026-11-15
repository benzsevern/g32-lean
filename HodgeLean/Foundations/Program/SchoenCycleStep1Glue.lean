import HodgeLean.Foundations.Program.SchoenCycleStep1Local

/-! # Gluing extensions of generic maps to integral targets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The generic map into a nonempty affine chart factors the generic stalk map. -/
theorem s2e_step1_generic_chart_comp (X : Scheme) [IsIntegral X]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (Spec.map (X.germToFunctionField U) ≫ hU.isoSpec.inv) ≫ U.ι =
      X.fromSpecStalk (genericPoint X) := by
  rw [Category.assoc, hU.isoSpec_inv_ι]
  exact hU.fromSpecStalk_eq_fromSpecStalk _

/-- Generic maps to integral targets extend across a finite smooth source. -/
theorem s2e_step1_integralTarget_lift
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (T : Scheme) (p : T ⟶ Y.left) [IsIntegralHom p]
    (v : Spec X.left.functionField ⟶ T)
    (hv : v ≫ p = X.left.fromSpecStalk (genericPoint X.left) ≫ f.left) :
    ∃ g : X.left ⟶ T, g ≫ p = f.left ∧
      X.left.fromSpecStalk (genericPoint X.left) ≫ g = v := by
  classical
  have hl : ∀ U : Y.left.AffineZariskiSite,
      ∃ g : (f.left ⁻¹ᵁ U.1).toScheme ⟶ T,
        g ≫ p = (f.left ⁻¹ᵁ U.1).ι ≫ f.left ∧
        ∀ hn : Nonempty (f.left ⁻¹ᵁ U.1),
          letI := hn
          Spec.map (X.left.germToFunctionField (f.left ⁻¹ᵁ U.1)) ≫
            (U.2.preimage f.left).isoSpec.inv ≫ g = v := by
    intro U
    cases isEmpty_or_nonempty (f.left ⁻¹ᵁ U.1) with
    | inl he =>
      letI : IsEmpty (f.left ⁻¹ᵁ U.1).toScheme := he
      refine ⟨isInitialOfIsEmpty.to T, isInitialOfIsEmpty.hom_ext _ _, ?_⟩
      intro hn
      exact (he.false hn.some).elim
    | inr hn =>
      letI := hn
      obtain ⟨g, hf, hg⟩ := s2e_step1_integralTarget_chart X Y f T p v hv U.1 U.2
      exact ⟨g, hf, fun _ => hg⟩
  choose g hg hgen using hl
  have htrans : ∀ {U V : Y.left.AffineZariskiSite} (i : U ⟶ V),
      X.left.homOfLE (f.left.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le)) ≫
        g V = g U := by
    intro U V i
    let hUV := f.left.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le)
    cases isEmpty_or_nonempty (f.left ⁻¹ᵁ U.1) with
    | inl he =>
      letI : IsEmpty (f.left ⁻¹ᵁ U.1).toScheme := he
      exact isInitialOfIsEmpty.hom_ext _ _
    | inr hn =>
      letI := hn
      have hnV : Nonempty (f.left ⁻¹ᵁ V.1) := ⟨⟨hn.some.1, hUV hn.some.2⟩⟩
      letI := hnV
      let ξU := Spec.map (X.left.germToFunctionField (f.left ⁻¹ᵁ U.1)) ≫
        (U.2.preimage f.left).isoSpec.inv
      let ξV := Spec.map (X.left.germToFunctionField (f.left ⁻¹ᵁ V.1)) ≫
        (V.2.preimage f.left).isoSpec.inv
      have hξU : ξU ≫ (f.left ⁻¹ᵁ U.1).ι = X.left.fromSpecStalk (genericPoint X.left) :=
        s2e_step1_generic_chart_comp X.left _ _
      have hξV : ξV ≫ (f.left ⁻¹ᵁ V.1).ι = X.left.fromSpecStalk (genericPoint X.left) :=
        s2e_step1_generic_chart_comp X.left _ _
      haveI : IsDominant (ξU ≫ (f.left ⁻¹ᵁ U.1).ι) := by
        rw [hξU]
        exact s2e_step1_generic_dominant X.left
      haveI : IsDominant ξU :=
        IsDominant.of_comp_of_isOpenImmersion ξU (f.left ⁻¹ᵁ U.1).ι
      have he : ξU ≫ X.left.homOfLE hUV = ξV := by
        rw [← cancel_mono (f.left ⁻¹ᵁ V.1).ι, Category.assoc,
          Scheme.homOfLE_ι, hξU, hξV]
      refine ext_of_isDominant_of_isSeparated p ?_ ξU ?_
      · rw [Category.assoc, hg, ← Category.assoc, Scheme.homOfLE_ι, hg]
      · rw [← Category.assoc, he]
        exact (hgen V hnV).trans (hgen U hn).symm
  let c : X.left.OpenCover := (Scheme.AffineZariskiSite.directedCover Y.left).pullback₁ f.left
  let gg := fun U : Y.left.AffineZariskiSite =>
    (pullbackRestrictIsoRestrict f.left U.1).hom ≫ g U
  have hgg : ∀ {U V : Y.left.AffineZariskiSite} (i : U ⟶ V),
      c.trans i ≫ gg V = gg U := by
    intro U V i
    have he : (pullbackRestrictIsoRestrict f.left U.1).inv ≫ c.trans i ≫
        (pullbackRestrictIsoRestrict f.left V.1).hom = X.left.homOfLE
          (f.left.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le)) := by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp +instances [c, Cover.trans, Cover.locallyDirectedPullbackCover]
    dsimp only [gg]
    rw [← Iso.inv_comp_eq, reassoc_of% he, htrans i]
  let G := c.glueMorphismsOfLocallyDirected gg hgg
  have hres (U : Y.left.AffineZariskiSite) :
      (f.left ⁻¹ᵁ U.1).ι ≫ G = g U := by
    rw [← cancel_epi (pullbackRestrictIsoRestrict f.left U.1).hom]
    rw [← Category.assoc, pullbackRestrictIsoRestrict_hom_ι]
    exact c.map_glueMorphismsOfLocallyDirected gg hgg U
  refine ⟨G, ?_, ?_⟩
  · apply c.hom_ext
    intro U
    change Limits.pullback.fst f.left U.1.ι ≫ G ≫ p =
      Limits.pullback.fst f.left U.1.ι ≫ f.left
    rw [← pullbackRestrictIsoRestrict_hom_ι f.left U.1]
    simp only [Category.assoc, reassoc_of% (hres U), hg]
  · let y := f.left (genericPoint X.left)
    let U : Y.left.AffineZariskiSite :=
      ⟨(Y.left.affineCover.f (Y.left.affineCover.idx y)).opensRange,
        isAffineOpen_opensRange _⟩
    have hn : Nonempty (f.left ⁻¹ᵁ U.1) :=
      ⟨⟨genericPoint X.left, Y.left.affineCover.covers y⟩⟩
    letI := hn
    rw [← s2e_step1_generic_chart_comp X.left (f.left ⁻¹ᵁ U.1) (U.2.preimage f.left),
      Category.assoc, hres]
    exact hgen U hn

end HodgeLean.Foundations.Program
