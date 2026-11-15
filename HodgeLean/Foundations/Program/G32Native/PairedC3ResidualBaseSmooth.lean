import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedIntersection
import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneModels
import HodgeLean.Adapters.IntersectionProductScaf

/-! # Smoothness of the base of the residual ruling -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Adapters

/-- A centre cutting a retained coordinate hyperplane has a smooth intersection
with the slice in the penultimate ambient scheme.
Source: Hartshorne, Algebraic Geometry, II.3 and II.8; Schoen,
Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi). -/
theorem pairedC3_residual_base_smooth (k : ℕ) (hk : 0 < k)
    {X : Over (Spec ↧ℂ)}
    (i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ X)
    [IsClosedImmersion i.left] (K : X.left.IdealSheafData)
    (j : Fin (k + 1)) (hK : K.comap i.left = s2e_s2b_residueIdeal k j) :
    Smooth ((K ⊔ i.left.ker).subschemeι ≫ X.hom) := by
  let H := s2e_s2b_residueIdeal k j
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let MP := Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  obtain ⟨E⟩ := EulerModel.residue_hyperplane_projective_model k hk j
  have : Smooth MP.hom := IntersectionProductScaf_projective_smooth (k - 1)
  have hH : Smooth (H.subschemeι ≫ PP.hom) := by
    change Smooth (s2c_subscheme PP H).hom
    rw [← Over.w E.hom]
    infer_instance
  obtain ⟨e, he⟩ := (residual_intersection_subscheme_iff i K H).mpr hK
  have hfac : (residualIntersection i K).hom =
      e.hom ≫ (H.subschemeι ≫ PP.hom) := by
    rw [← Category.assoc, he]
    exact (Over.w (residualIntersectionFirst i K)).symm
  have : Smooth (residualIntersection i K).hom := by
    rw [hfac]
    infer_instance
  change Smooth ((i.left.ker ⊔ K).subschemeι ≫ X.hom) at this
  rw [sup_comm] at this
  exact this

#print axioms pairedC3_residual_base_smooth
end HodgeLean.Foundations.Program.G32Native
