import HodgeLean.Foundations.Program.SchoenDegreeOneProjective
import HodgeLean.Foundations.Program.SchoenAdjoinGenerators
import HodgeLean.Foundations.Program.SchoenRescaledBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A common positive degree gives projectivity of the actual rescaled adjoin Proj over its coefficients. -/
theorem s2_commonDegreeAdjoin_projective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ 𝒜 D) :
    let R := Algebra.adjoin (𝒜 0) (Set.range v)
    let ℬ := fun k => s2_subringGradedPiece 𝒜 R.toSubring (D * k)
    letI := s2_homogeneousAdjoinGrading 𝒜 (Set.range v)
      (by rintro _ ⟨i, rfl⟩; exact ⟨D, hv i⟩)
    letI := s2_commonDegreeAdjoinGrading 𝒜 D hD v hv
    let e : 𝒜 0 ≃+* ℬ 0 := s2_adjoinDegreeZeroEquiv 𝒜 (Set.range v)
    IsProjective (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  let R := Algebra.adjoin (𝒜 0) (Set.range v)
  let ℬ := fun k => s2_subringGradedPiece 𝒜 R.toSubring (D * k)
  letI := s2_homogeneousAdjoinGrading 𝒜 (Set.range v)
    (by rintro _ ⟨i, rfl⟩; exact ⟨D, hv i⟩)
  letI := s2_commonDegreeAdjoinGrading 𝒜 D hD v hv
  let e : 𝒜 0 ≃+* ℬ 0 := s2_adjoinDegreeZeroEquiv 𝒜 (Set.range v)
  letI : Algebra (𝒜 0) (ℬ 0) := e.toRingHom.toAlgebra
  apply s2_projective_of_degree_one ℬ e.bijective n
    (fun i => (⟨v i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : R))
  · intro i
    change v i ∈ 𝒜 (D * 1)
    simpa only [Nat.mul_one] using hv i
  · exact s2_adjoin_generators 𝒜 v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original inherited grading on a common-degree adjoin also gives a projective Proj. -/
theorem s2_commonDegreeAdjoin_original_projective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D)
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ 𝒜 D) :
    let R := Algebra.adjoin (𝒜 0) (Set.range v)
    let ℭ := s2_subringGradedPiece 𝒜 R.toSubring
    letI : GradedRing ℭ := s2_homogeneousAdjoinGrading 𝒜 (Set.range v)
      (by rintro _ ⟨i, rfl⟩; exact ⟨D, hv i⟩)
    let e := s2_adjoinDegreeZeroEquiv 𝒜 (Set.range v)
    IsProjective (Proj.toSpecZero ℭ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  let R := Algebra.adjoin (𝒜 0) (Set.range v)
  let ℭ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℭ := s2_homogeneousAdjoinGrading 𝒜 (Set.range v)
    (by rintro _ ⟨i, rfl⟩; exact ⟨D, hv i⟩)
  letI : GradedRing (fun k => ℭ (D * k)) := s2_commonDegreeAdjoinGrading 𝒜 D hD v hv
  let e := s2_adjoinDegreeZeroEquiv 𝒜 (Set.range v)
  letI : CommRing (ℭ (D * 0)) := inferInstanceAs (CommRing (ℭ 0))
  haveI : IsProjective (Proj.toSpecZero (fun k => ℭ (D * k)) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    s2_commonDegreeAdjoin_projective 𝒜 D hD n v hv
  haveI := S2RescaledProj.map_isIso ℭ D hD
  change IsProjective (Proj.toSpecZero ℭ ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  rw [← S2RescaledProj.map_toSpecZero ℭ D hD, Category.assoc]
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f :=
    Proj.toSpecZero (fun k => ℭ (D * k)) ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  letI := P.isClosedImmersion
  refine ⟨⟨⟨P.ambientDimension, S2RescaledProj.map ℭ D hD ≫ P.immersion, ?_⟩⟩⟩
  rw [Category.assoc, P.immersion_toBase]

end HodgeLean.Foundations.Program
