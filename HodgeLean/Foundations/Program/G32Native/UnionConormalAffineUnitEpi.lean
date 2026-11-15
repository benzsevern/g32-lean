import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineTransposePresentation

/-! # Epic pullback units on affine quotient diagrams -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Along a surjective affine ring map, the unit on an associated module sheaf is epic. -/
lemma unionConormal_affineUnit_epi
    (R S : CommRingCat.{0}) (φ : R ⟶ S) (hφ : Function.Surjective φ.hom)
    (M : ModuleCat R) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)) := by
  have ht := unionConormal_affineTranspose_epi_of_presentations R S φ hφ M
    ((ModuleCat.extendScalars φ.hom).obj M) (Iso.refl _)
    ((s2e_affine_pullback_tilde_iso R S φ).app M)
    (𝟙 ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)))
  change Epi ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv
    (tilde M) _ (𝟙 _)) at ht
  rw [Adjunction.homEquiv_id] at ht
  exact ht

end HodgeLean.Foundations.Program.G32Native
