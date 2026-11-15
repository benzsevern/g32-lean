import HodgeLean.Foundations.Program.SchoenTransferQ3FlatOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Smooth source and target opens for the retained tangent comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- A dense etale base open refines to a dense open on which both actual
source and target are smooth over the complex field. -/
theorem s4_q3_smooth_etale_refinement
    {X W : Over (Spec ↧ℂ)} [IsIntegral W.left] [LocallyOfFinitePresentation W.hom]
    (q : X ⟶ W) (U₀ : W.left.Opens) (hU₀ : Dense (U₀ : Set W.left))
    (hEt₀ : Etale (q.left ∣_ U₀)) :
    ∃ U : W.left.Opens, Dense (U : Set W.left) ∧ U ≤ U₀ ∧
      Smooth (U.ι ≫ W.hom) ∧ Etale (q.left ∣_ U) ∧
      Smooth ((q.left ⁻¹ᵁ U).ι ≫ X.hom) := by
  let V := U₀.ι ⁻¹ᵁ W.hom.smoothLocus
  let U := U₀.ι ''ᵁ V
  have hUeq : U = U₀ ⊓ W.hom.smoothLocus := by
    ext t
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, hv⟩
    · intro ht
      exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩
  have hUsmooth : U ≤ W.hom.smoothLocus := by rw [hUeq]; exact inf_le_right
  have hUbase : U ≤ U₀ := by rw [hUeq]; exact inf_le_left
  have hdense : Dense (U : Set W.left) := by
    rw [hUeq]
    exact hU₀.inter_of_isOpen_right W.hom.dense_smoothLocus_of_perfectField
      W.hom.smoothLocus.isOpen
  letI : Etale (q.left ∣_ U₀) := hEt₀
  have hEt : Etale (q.left ∣_ U) :=
    (MorphismProperty.arrow_mk_iso_iff @Etale.{0}
      (morphismRestrictRestrict q.left U₀ V)).mp inferInstance
  have hsmooth : Smooth (U.ι ≫ W.hom) := boundary_smooth_restrict W.hom U hUsmooth
  letI := hEt
  letI := hsmooth
  have hsource : Smooth ((q.left ∣_ U) ≫ U.ι ≫ W.hom) := inferInstance
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q] at hsource
  exact ⟨U, hdense, hUbase, hsmooth, hEt, hsource⟩

end HodgeLean.Foundations.Program
