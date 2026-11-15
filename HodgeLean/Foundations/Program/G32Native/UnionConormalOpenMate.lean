import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenDirectImageSquare
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The mate of the open direct image identification -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- Mating open direct image comparison along the restriction adjunctions
recovers the ordinary composed direct image identification. -/
lemma unionConormalOpenPushforward_mate
    {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
      (Scheme.Modules.restrictAdjunction U.ι)
      (TwoSquare.mk (Scheme.Modules.pushforward f)
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι)
        (Scheme.Modules.restrictFunctor U.ι)
        (Scheme.Modules.pushforward (f ∣_ U))
        (unionConormalOpenPushforwardNatIso f U).hom)).natTrans =
      (unionConormalOpenDirectImageSquareIso f U).hom := by
  apply NatTrans.ext
  funext M
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.comp_id]
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  let k := (f ⁻¹ᵁ U).ι
  let W := U.ι ⁻¹ᵁ V
  let Z := (f ∣_ U) ⁻¹ᵁ W
  let m₀ : Γ(M, k ⁻¹ᵁ (f ⁻¹ᵁ V)) := m
  change M.presheaf.map (eqToHom (k.preimage_image_eq Z).symm).op
      (M.presheaf.map
        ((TopologicalSpace.Opens.map k.base).map
          (eqToHom (image_morphismRestrict_preimage f U W))).op
        (M.presheaf.map
          ((TopologicalSpace.Opens.map k.base).map
            ((TopologicalSpace.Opens.map f.base).map (homOfLE (U.ι.image_preimage_le V)))).op m₀)) =
    M.presheaf.map (eqToHom (show Z = k ⁻¹ᵁ (f ⁻¹ᵁ V) from by
      dsimp only [Z, W, k]
      rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage])).op m₀
  let a := ((TopologicalSpace.Opens.map k.base).map
    ((TopologicalSpace.Opens.map f.base).map (homOfLE (U.ι.image_preimage_le V)))).op
  let b := ((TopologicalSpace.Opens.map k.base).map
    (eqToHom (image_morphismRestrict_preimage f U W))).op
  let c := (eqToHom (k.preimage_image_eq Z).symm).op
  let d := (eqToHom (show Z = k ⁻¹ᵁ (f ⁻¹ᵁ V) from by
    dsimp only [Z, W, k]
    rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage])).op
  have he : a ≫ b ≫ c = d := Subsingleton.elim _ _
  have hv := congrArg (fun t => M.presheaf.map t m₀) he
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hv

end HodgeLean.Foundations.Program.G32Native
