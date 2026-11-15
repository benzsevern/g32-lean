import HodgeLean.Foundations.Program.SchoenCycleC1SectionFieldTowerHelpers

/-! # Ranks under the actual open restriction section isomorphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program

/-- The global-section rank of the restricted projection is the rank of
the original projection's section algebra on that base open. -/
theorem s2e_c1_restricted_section_finrank
    {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
      (f ∣_ U).appTop.hom.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.finrank Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) =
      Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  letI : Algebra Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤) :=
    (f ∣_ U).appTop.hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let eY : Γ(U.toScheme, ⊤) ≅ Γ(Y, U) := (Scheme.restrictFunctorΓ (X := Y)).app (op U)
  let eX : Γ((f ⁻¹ᵁ U).toScheme, ⊤) ≅ Γ(X, f ⁻¹ᵁ U) := (Scheme.restrictFunctorΓ (X := X)).app (op (f ⁻¹ᵁ U))
  apply Algebra.finrank_eq_of_equiv_equiv
    eY.commRingCatIsoToRingEquiv eX.commRingCatIsoToRingEquiv
  change (eY.hom ≫ f.app U).hom = ((f ∣_ U).appTop ≫ eX.hom).hom
  congr 1
  change Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top.symm).op ≫ f.app U =
    (f ∣_ U).appTop ≫
      X.presheaf.map (eqToHom (f ⁻¹ᵁ U).isOpenEmbedding_obj_top.symm).op
  rw [f.naturality, morphismRestrict_appTop]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

end HodgeLean.Foundations.Program
