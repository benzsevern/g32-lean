import HodgeLean.Foundations.Program.SchoenTowerVanishingSuppliers
import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem n2b_proper_over_projective_base {W B : Over (Spec ↧ℂ)}
    [IsProjective B.hom] (β : W ⟶ B) [IsFinite β.left] : IsProper W.hom := by
  rw [← β.w]
  infer_instance

theorem n2b_projective_of_over_iso {W X : Over (Spec ↧ℂ)}
    [IsProjective X.hom] (e : W ≅ X) : IsProjective W.hom := by
  exact s2v_projective_of_closedImmersion e.hom

theorem n2b_exceptional_geometry {B' B W : Over (Spec ↧ℂ)}
    [IsProjective B'.hom] [IsProjective B.hom] [IsProjective W.hom]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (β : W ⟶ B') [IsFinite β.left] :
    let K := s2c_subscheme B I
    let E := s2c_exceptional b I
    let j : E ⟶ B' := pullback.fst b (s2c_subschemeι B I)
    IsProjective K.hom ∧ IsProjective E.hom ∧
      IsProjective (s2b_preimage β j).hom ∧ IsFinite (s2b_toExceptional β j).left := by
  dsimp only
  obtain ⟨hK, hE⟩ := s2v_centre_and_exceptional_projective b I
  letI := hE
  exact ⟨hK, hE, s2v_preimage_projective β _, s2v_preimage_projection_finite β _⟩

end HodgeLean.Foundations.Program
