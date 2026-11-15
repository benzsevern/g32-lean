import HodgeLean.Foundations.Program.SchoenCycleC11StandardHelpers
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import HodgeLean.Foundations.Program.SchoenCycleC11FiniteHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11ProperHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The complex algebra of global sections induced by the actual affine structure map.
Source: Mathlib, Scheme.isoSpec and Spec.preimage. -/
def s2e_c11_affineSectionAlgebra (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    Algebra ℂ Γ(X.left, ⊤) :=
  (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom.toAlgebra

/-- The affine coordinate isomorphism respects the specified complex structure map.
Source: Mathlib, Scheme.isoSpec and Spec.map_preimage. -/
def s2e_c11_affineCoordinateIso (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    letI := s2e_c11_affineSectionAlgebra X
    X ≅ Over.mk (affineSpecStructureMap Γ(X.left, ⊤)) := by
  letI := s2e_c11_affineSectionAlgebra X
  refine Over.isoMk X.left.isoSpec ?_
  change X.left.isoSpec.hom ≫ Spec.map (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)) = X.hom
  rw [Spec.map_preimage, Iso.hom_inv_id_assoc]

/-- Affine complex points in the specified structure are section-algebra homomorphisms.
Source: ComplexPoint.affineSpecHomeomorph and Point.isoMapHomeomorph. -/
def s2e_c11_affineCoordinateHomeomorph (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    letI := s2e_c11_affineSectionAlgebra X
    Point ℂ X ≃ₜ (Γ(X.left, ⊤) →ₐ[ℂ] ℂ) := by
  letI := s2e_c11_affineSectionAlgebra X
  exact (Point.isoMapHomeomorph (s2e_c11_affineCoordinateIso X)).trans
    (affineSpecHomeomorph Γ(X.left, ⊤))

/-- An affine scheme map induces its actual complex section-algebra map.
Source: Mathlib, fully faithful Spec and over-category morphism equations. -/
def s2e_c11_affineCoordinateAlgHom
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let f' := (s2e_c11_affineCoordinateIso X).inv ≫ f ≫ (s2e_c11_affineCoordinateIso Y).hom
  refine ⟨(Spec.preimage f'.left).hom, ?_⟩
  have h : CommRingCat.ofHom (algebraMap ℂ Γ(Y.left, ⊤)) ≫ Spec.preimage f'.left =
      CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w f'
  intro c
  exact congrArg (fun a => a c) (congrArg CommRingCat.Hom.hom h)

/-- The induced algebra map represents the conjugated scheme morphism exactly.
Source: Mathlib, Spec.map_preimage. -/
theorem s2e_c11_affineCoordinateAlgHom_spec
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    Spec.map (CommRingCat.ofHom (s2e_c11_affineCoordinateAlgHom X Y f).toRingHom) =
      (s2e_c11_affineCoordinateIso X).inv.left ≫ f.left ≫
        (s2e_c11_affineCoordinateIso Y).hom.left := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  exact Spec.map_preimage _

/-- Affine coordinate homeomorphisms intertwine actual point maps with precomposition.
Source: ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap and scheme isomorphism identities. -/
theorem s2e_c11_affineCoordinateHomeomorph_naturality
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (z : Point ℂ X) :
    letI := s2e_c11_affineSectionAlgebra X
    letI := s2e_c11_affineSectionAlgebra Y
    s2e_c11_affineCoordinateHomeomorph Y (Point.map f z) =
      (s2e_c11_affineCoordinateHomeomorph X z).comp (s2e_c11_affineCoordinateAlgHom X Y f) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let ex := s2e_c11_affineCoordinateIso X
  let ey := s2e_c11_affineCoordinateIso Y
  let g := s2e_c11_affineCoordinateAlgHom X Y f
  have hs : affineSpecComplexPointMap g (Point.map ex.hom z) =
      Point.map ey.hom (Point.map f z) := by
    apply Over.OverMorphism.ext
    change (z.left ≫ ex.hom.left) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) =
      (z.left ≫ f.left) ≫ ey.hom.left
    rw [s2e_c11_affineCoordinateAlgHom_spec]
    simp only [Category.assoc]
    have he : ex.hom.left ≫ ex.inv.left = 𝟙 X.left := by
      exact congrArg (fun a => a.left) ex.hom_inv_id
    rw [← Category.assoc ex.hom.left ex.inv.left, he, Category.id_comp]
  have h := affineSpecEquiv_affineSpecComplexPointMap g (Point.map ex.hom z)
  rw [hs] at h
  exact h

/-- Finite maps between affine complex schemes have proper point maps.
Source: Hartshorne, Algebraic Geometry, Appendix B, finite affine analytification. -/
theorem s2e_c11_affine_scheme_finite_proper
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [IsFinite f.left] : IsProperMap (Point.map f) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let A := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let g : A →ₐ[ℂ] B := s2e_c11_affineCoordinateAlgHom X Y f
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
    rw [s2e_c11_affineCoordinateAlgHom_spec]
    infer_instance
  letI : Module.Finite A B := (IsFinite.SpecMap_iff (CommRingCat.ofHom g.toRingHom)).mp hfin
  letI : T2Space (A →ₐ[ℂ] ℂ) := (s2e_c11_algebraHom_isClosedEmbedding A).isEmbedding.t2Space
  have hp : IsProperMap (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) := by
    apply s2e_c11_proper_of_coordinate_bounds
      (fun φ : B →ₐ[ℂ] ℂ => (φ : B → ℂ)) (s2e_c11_algebraHom_isClosedEmbedding B)
    · rw [continuous_induced_rng]
      exact continuous_pi (fun a => continuous_affineAlgebraHom_apply B (g a))
    · exact s2e_c11_finite_element_continuous_bound
  let ex := s2e_c11_affineCoordinateHomeomorph X
  let ey := s2e_c11_affineCoordinateHomeomorph Y
  have heq : Point.map f = ey.symm ∘ (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) ∘ ex := by
    funext z
    apply ey.injective
    exact (s2e_c11_affineCoordinateHomeomorph_naturality X Y f z).trans
      (ey.apply_symm_apply _).symm
  rw [heq]
  exact ey.symm.isProperMap.comp (hp.comp ex.isProperMap)

/-- The actual scheme restriction retains its specified complex structure.
Source: Mathlib, morphismRestrict_ι. -/
def s2e_c11_restrictOver (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens) :
    openScheme X (f.left ⁻¹ᵁ U) ⟶ openScheme Y U :=
  Over.homMk (f.left ∣_ U) (by
    change (f.left ∣_ U) ≫ (U.ι ≫ Y.hom) = (f.left ⁻¹ᵁ U).ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w f])

/-- Open-subscheme homeomorphisms intertwine the actual restricted point maps.
Source: ComplexPoint.openHomeomorph and Mathlib, morphismRestrict_ι. -/
theorem s2e_c11_restrictOver_point_square
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens)
    (z : Point ℂ (openScheme X (f.left ⁻¹ᵁ U))) :
    openHomeomorph Y U (Point.map (s2e_c11_restrictOver X Y f U) z) =
      (Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)
        (openHomeomorph X (f.left ⁻¹ᵁ U) z) := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (z.left ≫ (f.left ∣_ U)) ≫ U.ι =
    (z.left ≫ (f.left ⁻¹ᵁ U).ι) ≫ f.left
  rw [Category.assoc, morphismRestrict_ι, Category.assoc]

/-- Etale maps between affine complex schemes have analytic local inverses.
Source: Mathlib, etale affine comparison and standard-etale neighbourhoods. -/
theorem s2e_c11_affine_scheme_etale_local_inverse
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [Etale f.left] : IsLocalHomeomorph (Point.map f) := by
  letI := s2e_c11_affineSectionAlgebra X
  letI := s2e_c11_affineSectionAlgebra Y
  let A := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let g : A →ₐ[ℂ] B := s2e_c11_affineCoordinateAlgHom X Y f
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have het : g.toRingHom.Etale := by
    have h : Etale (Spec.map (CommRingCat.ofHom g.toRingHom)) := by
      rw [s2e_c11_affineCoordinateAlgHom_spec]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h
    exact h
  letI : Algebra.Etale A B := RingHom.etale_algebraMap.mp het
  have hp : IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) :=
    s2e_c11_etaleAlgebra_local_inverse
  let ex := s2e_c11_affineCoordinateHomeomorph X
  let ey := s2e_c11_affineCoordinateHomeomorph Y
  have heq : Point.map f = ey.symm ∘ (fun φ : B →ₐ[ℂ] ℂ => φ.comp g) ∘ ex := by
    funext z
    apply ey.injective
    exact (s2e_c11_affineCoordinateHomeomorph_naturality X Y f z).trans
      (ey.apply_symm_apply _).symm
  rw [heq]
  exact ey.symm.isLocalHomeomorph.comp (hp.comp ex.isLocalHomeomorph)

end HodgeLean.Foundations.Program
