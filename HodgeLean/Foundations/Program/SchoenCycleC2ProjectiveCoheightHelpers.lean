import HodgeLean.Foundations.Program.SchoenCycleC2OrbitCoheightHelpers
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A projective model retains its specified dimension. -/
theorem s2e_projective_model_dimension
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    dim Q.left = k := by
  have he : topologicalKrullDim Q.left =
      topologicalKrullDim (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) : Scheme) :=
    eQ.hom.left.homeomorph.isHomeomorph.topologicalKrullDim_eq
  unfold TopologicalSpace.dim
  rw [he]
  exact s0_complex_projective_dimension k

/-- The exact projective projection identifies the coheight of each forward
component once the retained base dimension is known. -/
theorem s2e_projective_orbit_component_coheight
    {Q W B : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [IsIntegral B.left] [Smooth B.hom] (k : ℕ)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (β : W ⟶ B) (hd : δ ≫ β = β)
    (hproj : ι ≫ β = eQ.hom ≫ ℓ)
    (U : B.left.Opens) (hU : Set.range ℓ.left ⊆ U)
    (hfin : IsFinite (β.left ∣_ U)) (he : Etale (β.left ∣_ U))
    (hB : dim B.left = 2 * k) (t : ℕ) :
    ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of δ ^ t).asHom) ℚ).support,
      Order.coheight x = k := by
  let : IsClosedImmersion (ι ≫ β).left := by
    rw [hproj]
    change IsClosedImmersion (eQ.hom.left ≫ ℓ.left)
    infer_instance
  apply s2e_orbit_component_coheight_of_dimensions ι δ β hd U
  · rw [hproj]
    rintro _ ⟨x, rfl⟩
    exact hU ⟨eQ.hom.left x, rfl⟩
  · exact hfin
  · exact he
  · exact s2e_projective_model_dimension Q k eQ
  · simpa only [two_mul] using hB

end HodgeLean.Foundations.Program
