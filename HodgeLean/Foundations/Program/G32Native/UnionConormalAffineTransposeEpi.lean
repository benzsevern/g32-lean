import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineTranspose
import HodgeLean.Foundations.Program.G32Native.UnionConormalScalarTransposeEpi

/-! # Epimorphy of affine transposition along a quotient map -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- For associated sheaves and a surjective ring map, epimorphy passes to the transpose. -/
lemma unionConormal_affineTranspose_epi
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)
    (M : ModuleCat R) (N : ModuleCat S)
    (v : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶ tilde N)
    [Epi v] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ v) := by
  let e := (s2e_affine_pullback_tilde_iso R S φ).app M
  let w := (tilde.functor S).preimage (e.inv ≫ v)
  have hw : (tilde.functor S).map w = e.inv ≫ v :=
    (tilde.functor S).map_preimage _
  haveI : Epi ((tilde.functor S).map w) := by
    rw [hw]
    infer_instance
  haveI : Epi w := (tilde.functor S).epi_of_epi_map inferInstance
  haveI := unionConormal_scalarTranspose_epi R S φ.hom hφ _ _ w
  have hv : v = e.hom ≫ (tilde.functor S).map w := by
    rw [hw, Iso.hom_inv_id_assoc]
  have ht := (congrArg
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _) hv).trans
      (unionAffineTranspose_coordinates R S φ M N w)
  rw [ht]
  change Epi ((tilde.functor R).map
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N w) ≫
      (unionAffinePushforwardTildeIso R S φ N).inv)
  infer_instance

#print axioms unionConormal_affineTranspose_epi
end HodgeLean.Foundations.Program.G32Native
