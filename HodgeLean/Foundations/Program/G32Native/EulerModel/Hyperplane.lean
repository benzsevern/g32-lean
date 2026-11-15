import HodgeLean.Foundations.Program.G32Native.EulerModel.Defs
import HodgeLean.Foundations.Program.SchoenCycleS3IntersectionBase

/-! # The coordinate hyperplane on the specified projective component -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The chosen hyperplane ideal is the singleton coordinate intersection. -/
theorem hyperplaneIdeal_eq_intersection (k : ℕ) :
    s2e_hyperplaneIdeal k = s2e_s2b_intersectionIdeal k {0} := by
  classical
  simp only [s2e_s2b_intersectionIdeal, Finset.mem_singleton, iSup_iSup_eq_left]
  rfl

#print axioms hyperplaneIdeal_eq_intersection
/-- The actual coordinate hyperplane is projective space of dimension one less. -/
theorem hyperplane_projective_model (k : ℕ) (hk : 0 < k) :
    Nonempty (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_hyperplaneIdeal k) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))) := by
  rw [hyperplaneIdeal_eq_intersection]
  have he := s2e_coordinate_intersection_over k {0}
    (by simp only [Finset.card_singleton]; omega)
  have hcard : ({0} : Finset (Fin (k + 1))).card = 1 := Finset.card_singleton _
  rw [hcard] at he
  exact he

#print axioms hyperplane_projective_model
/-- Pulling an ideal back through the specified isomorphism preserves its subscheme over the base. -/
theorem subscheme_comap_model {Q P : Over (Spec ↧ℂ)}
    (e : Q ≅ P) (I : P.left.IdealSheafData) :
    Nonempty (s2c_subscheme Q (I.comap e.hom.left) ≅ s2c_subscheme P I) := by
  let E : (I.comap e.hom.left).subscheme ≅ I.subscheme :=
    I.comapIso e.hom.left ≪≫ asIso (pullback.snd e.hom.left I.subschemeι)
  refine ⟨Over.isoMk E ?_⟩
  change E.hom ≫ (I.subschemeι ≫ P.hom) = (I.comap e.hom.left).subschemeι ≫ Q.hom
  dsimp only [E, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, ← pullback.condition_assoc, ← Category.assoc, I.comapIso_hom_fst,
    Over.w e.hom]

#print axioms subscheme_comap_model
/-- The pulled-back hyperplane retains its projective model on the same component. -/
theorem coordinate_hyperplane_model {Q : Over (Spec ↧ℂ)} {k : ℕ}
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (hk : 0 < k) :
    Nonempty (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))) := by
  obtain ⟨E⟩ := subscheme_comap_model eQ (s2e_hyperplaneIdeal k)
  obtain ⟨F⟩ := hyperplane_projective_model k hk
  exact ⟨E ≪≫ F⟩

#print axioms coordinate_hyperplane_model
end HodgeLean.Foundations.Program.G32Native.EulerModel
