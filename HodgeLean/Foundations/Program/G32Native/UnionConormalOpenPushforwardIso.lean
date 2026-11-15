import HodgeLean.Foundations.Program.G32Native.UnionConormalRestrictionExact

/-! # Restricting direct images to ambient open subschemes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- Direct image and ambient open restriction have their natural module identification. -/
def unionConormalOpenPushforwardIso {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U : Y.Opens) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun V => ?_) ?_
  · let he := image_morphismRestrict_preimage f U V.unop
    refine ModuleCat.isoMk (M.presheaf.mapIso (eqToIso he).op) ?_
    intro r
    ext m
    let m₀ : M.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V.unop))) := m
    symm
    change M.presheaf.map (eqToHom he).op
        (f.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv r) •
          m₀) =
      ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V.unop)).inv
        ((f ∣_ U).app V.unop r) • M.presheaf.map (eqToHom he).op
          m₀
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, CommRingCat.id_apply]
    change M.val.map (eqToHom he).op (_ • m₀) = _
    rw [M.val.map_smul]
    rw [morphismRestrict_app]
    rfl
  · intro V W g
    ext m
    let m₀ : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V.unop)) := m
    change M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
        (M.presheaf.map
          (homOfLE (f.preimage_mono (U.ι.image_mono (leOfHom g.unop)))).op m₀) =
      M.presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_mono ((f ∣_ U).preimage_mono (leOfHom g.unop)))).op
        (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op m₀)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1

end HodgeLean.Foundations.Program.G32Native
