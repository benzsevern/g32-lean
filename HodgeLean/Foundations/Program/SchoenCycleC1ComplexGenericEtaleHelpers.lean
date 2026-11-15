import HodgeLean.Foundations.Program.SchoenCycleC1AffineGenericEtaleHelpers
import HodgeLean.Foundations.Program.SchoenCycleStep1AffineAction

/-! # Generic etale neighbourhoods of the retained complex cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An actual finite surjection between integral complex schemes has a
nonempty finite etale base neighbourhood when the base is locally Noetherian. -/
theorem s2e_c1_complex_finite_exists_etale_base_open
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left] :
    ∃ U : Y.left.Opens, (U : Set Y.left).Nonempty ∧
      IsFinite (f.left ∣_ U) ∧ Etale (f.left ∣_ U) := by
  obtain ⟨A, hA, hyA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := genericPoint Y.left) (U := ⊤) (by trivial)
  haveI : Nonempty A := ⟨⟨genericPoint Y.left, hyA⟩⟩
  obtain ⟨x, hx⟩ := f.left.surjective (genericPoint Y.left)
  haveI : Nonempty (f.left ⁻¹ᵁ A) := ⟨⟨x, by change f.left x ∈ A; rwa [hx]⟩⟩
  haveI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  haveI : IsIntegral (f.left ⁻¹ᵁ A).toScheme :=
    isIntegral_of_isOpenImmersion (f.left ⁻¹ᵁ A).ι
  haveI : IsAffine A.toScheme := hA
  haveI : IsAffine (f.left ⁻¹ᵁ A).toScheme := hA.preimage f.left
  let YA : Over (Spec ↧ℂ) := Over.mk (A.ι ≫ Y.hom)
  letI : Algebra ℂ Γ(A.toScheme, ⊤) := s2e_step1_sectionAlgebra YA ⊤
  haveI : CharZero Γ(A.toScheme, ⊤) :=
    charZero_of_injective_algebraMap (algebraMap ℂ Γ(A.toScheme, ⊤)).injective
  haveI : Surjective (f.left ∣_ A) := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := f.left.surjective y.1
    refine ⟨⟨z, by change f.left z ∈ A; rw [hz]; exact y.property⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe f.left A _).trans hz
  obtain ⟨V, hV, _, hEt⟩ := s2e_c1_finite_affine_exists_etale_base_open
    (f.left ⁻¹ᵁ A).toScheme A.toScheme (f.left ∣_ A)
  haveI : Etale (f.left ∣_ A.ι ''ᵁ V) :=
    (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictRestrict f.left A V)).mp hEt
  obtain ⟨v, hv⟩ := hV
  refine ⟨A.ι ''ᵁ V, ⟨A.ι v, ?_⟩, inferInstance, inferInstance⟩
  exact ⟨v, hv, rfl⟩

end HodgeLean.Foundations.Program
