import HodgeLean.Foundations.Program.SchoenCycleC11AffineAssemblyHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FibreDegreeHelpers
import HodgeLean.Foundations.Program.CompensationAssemblyAffineFiber

/-! # Actual affine section maps and their complex fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The existing affine coordinate construction uses exactly the actual
global-section pullback, including the prescribed complex structures. -/
theorem s2e_c1_affineCoordinateAlgHom_eq_appTop
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    (s2e_c11_affineCoordinateAlgHom X Y f).toRingHom = f.left.appTop.hom := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  have h : CommRingCat.ofHom (s2e_c11_affineCoordinateAlgHom X Y f).toRingHom =
      f.left.appTop := by
    apply Spec.map_injective
    rw [s2e_c11_affineCoordinateAlgHom_spec]
    change X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom = Spec.map f.left.appTop
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality f.left]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom h

/-- The actual fibre of an affine complex morphism is counted by its
section algebra maps over evaluation at the specified base point. -/
theorem s2e_c1_affine_complex_fibre_card_eq_section_algHom_card
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (y : ComplexPoint Y) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    let g := s2e_c11_affineCoordinateAlgHom X Y f
    letI : Algebra Γ(Y.left, ⊤) Γ(X.left, ⊤) := g.toRingHom.toAlgebra
    letI : Algebra Γ(Y.left, ⊤) ℂ :=
      (s2e_c11_affineCoordinateHomeomorph Y y).toRingHom.toAlgebra
    Nat.card ((Point.map f) ⁻¹' {y}) = Nat.card (Γ(X.left, ⊤) →ₐ[Γ(Y.left, ⊤)] ℂ) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let g := s2e_c11_affineCoordinateAlgHom X Y f
  let φ := s2e_c11_affineCoordinateHomeomorph Y y
  let e : ((Point.map f) ⁻¹' {y}) ≃
      {a : Γ(X.left, ⊤) →ₐ[ℂ] ℂ // a.comp g = φ} :=
    Equiv.subtypeEquiv (s2e_c11_affineCoordinateHomeomorph X).toEquiv (fun z => by
      change Point.map f z = y ↔
        (s2e_c11_affineCoordinateHomeomorph X z).comp g = φ
      rw [← s2e_c11_affineCoordinateHomeomorph_naturality X Y f z]
      exact (s2e_c11_affineCoordinateHomeomorph Y).injective.eq_iff.symm)
  exact (Nat.card_congr e).trans
    (Nat.card_congr (cq_algHom_fiber_equiv Γ(Y.left, ⊤) Γ(X.left, ⊤) g φ)).symm


/-- The actual complex fibre of a finite etale affine projection counts
the rank of its actual global-section algebra. -/
theorem s2e_c1_finite_etale_affine_section_rank_eq_fibre_card
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral Y.left] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (y : ComplexPoint Y) :
    letI : Algebra Γ(Y.left, ⊤) Γ(X.left, ⊤) := f.left.appTop.hom.toAlgebra
    Module.finrank Γ(Y.left, ⊤) Γ(X.left, ⊤) = Nat.card ((Point.map f) ⁻¹' {y}) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  letI : Algebra Γ(Y.left, ⊤) Γ(X.left, ⊤) := f.left.appTop.hom.toAlgebra
  letI : Algebra Γ(Y.left, ⊤) ℂ :=
    (s2e_c11_affineCoordinateHomeomorph Y y).toRingHom.toAlgebra
  haveI : Module.Finite Γ(Y.left, ⊤) Γ(X.left, ⊤) := f.left.finite_appTop
  haveI : Algebra.Etale Γ(Y.left, ⊤) Γ(X.left, ⊤) :=
    HasRingHomProperty.appTop (P := @Etale) f.left (inferInstance : Etale f.left)
  have hc := s2e_c1_affine_complex_fibre_card_eq_section_algHom_card X Y f y
  dsimp only at hc
  rw [s2e_c1_affineCoordinateAlgHom_eq_appTop X Y f] at hc
  exact (s2e_c1_finiteFlat_rank_eq_geometric_fibre_card
    Γ(Y.left, ⊤) Γ(X.left, ⊤) ℂ).trans hc.symm


end HodgeLean.Foundations.Program
