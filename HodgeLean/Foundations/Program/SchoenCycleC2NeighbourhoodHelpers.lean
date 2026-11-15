import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An étale restriction over a smooth base gives a smooth ambient neighbourhood. -/
theorem s2e_smooth_neighbourhood_of_etale
    {Q W B : Over (Spec ↧ℂ)} [Smooth B.hom]
    (ι : Q ⟶ W) (β : W ⟶ B) (U : B.left.Opens)
    (hU : Set.range (ι ≫ β).left ⊆ U) (he : Etale (β.left ∣_ U)) :
    ∃ V : W.left.Opens, Set.range ι.left ⊆ V ∧ Smooth (V.ι ≫ W.hom) := by
  let V := β.left ⁻¹ᵁ U
  refine ⟨V, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hU ⟨x, rfl⟩
  · have he' : Smooth ((β.left ∣_ U) ≫ U.ι ≫ B.hom) := by
      infer_instance
    rw [morphismRestrict_ι_assoc, Over.w β] at he'
    exact he'

/-- Powers of an endomorphism over the base retain the same projection. -/
theorem s2e_power_projection {W B : Over (Spec ↧ℂ)}
    (δ : W ⟶ W) (β : W ⟶ B) (hd : δ ≫ β = β) (n : ℕ) :
    (End.of δ ^ n).asHom ≫ β = β := by
  induction n with
  | zero => simp only [pow_zero, End.one_asHom, Category.id_comp]
  | succ n ih =>
    rw [pow_succ, End.mul_asHom, Category.assoc, ih]
    exact hd

/-- Every forward translate lies in the same smooth inverse-image neighbourhood. -/
theorem s2e_orbit_smooth_neighbourhood_of_etale
    {Q W B : Over (Spec ↧ℂ)} [Smooth B.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (β : W ⟶ B)
    (hd : δ ≫ β = β) (U : B.left.Opens)
    (hU : Set.range (ι ≫ β).left ⊆ U) (he : Etale (β.left ∣_ U)) (n : ℕ) :
    ∃ V : W.left.Opens,
      Set.range (ι ≫ (End.of δ ^ n).asHom).left ⊆ V ∧ Smooth (V.ι ≫ W.hom) := by
  apply s2e_smooth_neighbourhood_of_etale (ι ≫ (End.of δ ^ n).asHom) β U
  · simpa only [Category.assoc, s2e_power_projection δ β hd n] using hU
  · exact he

end HodgeLean.Foundations.Program
