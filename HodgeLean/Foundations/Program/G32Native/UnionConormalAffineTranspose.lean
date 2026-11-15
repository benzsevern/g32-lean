import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffinePullbackCompatibility
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffinePushforwardCoordinates

/-! # Affine transposition in actual associated-sheaf coordinates -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- The transpose of an affine scalar-extension arrow has the scalar-restriction
transpose as its actual pushed associated-sheaf coordinates. -/
theorem unionAffineTranspose_coordinates
    (R S : CommRingCat.{0}) (φ : R ⟶ S)
    (M : ModuleCat R) (N : ModuleCat S)
    (v : (ModuleCat.extendScalars φ.hom).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
        ((s2e_affine_pullback_tilde_iso R S φ).hom.app M ≫ tilde.map v) =
      tilde.map ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _ v) ≫
        (unionAffinePushforwardTildeIso R S φ N).inv := by
  let a := tilde.adjunction (R := R)
  let b := tilde.adjunction (R := S)
  let c := ModuleCat.extendRestrictScalarsAdj φ.hom
  let ψ := s2e_affine_pushforward_sections_iso R S φ
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)
  let e := unionAffinePushforwardTildeSectionsIso R S φ N
  have htop : b.homEquiv _ _ (tilde.map v) = v ≫ (tilde.isoTop N).hom := by
    rw [Adjunction.homEquiv_unit]
    exact (tilde.toTildeΓNatIso.hom.naturality v).symm
  have he : (b.homEquiv _ _).symm (v ≫ (tilde.isoTop N).hom) = tilde.map v := by
    apply (b.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, htop]
  have ht := Conormal.affinePullbackTilde_transpose R S φ M (tilde N)
    (v ≫ (tilde.isoTop N).hom)
  have hcr := c.homEquiv_naturality_right v (tilde.isoTop N).hom
  rw [he] at ht
  have ht' := ht.trans hcr
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (ψ.hom.app (tilde N))).mp
  change _ = a.homEquiv _ _
    ((tilde.functor R).map (c.homEquiv _ _ v) ≫
      (tilde.functor R).map e.inv ≫ P.fromTildeΓ) ≫ ψ.hom.app (tilde N)
  rw [← Functor.map_comp_assoc]
  change _ = a.homEquiv _ _ ((a.homEquiv _ _).symm
    (c.homEquiv _ _ v ≫ e.inv)) ≫ ψ.hom.app (tilde N)
  rw [Equiv.apply_symm_apply]
  change _ = c.homEquiv _ _ v ≫
    (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N).hom ≫
      ψ.inv.app (tilde N) ≫ ψ.hom.app (tilde N)
  rw [Iso.inv_hom_id_app]
  exact ht'.trans (congrArg (fun z => c.homEquiv _ _ v ≫ z)
    (Category.comp_id ((ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N).hom))).symm

#print axioms unionAffineTranspose_coordinates

end HodgeLean.Foundations.Program.G32Native
