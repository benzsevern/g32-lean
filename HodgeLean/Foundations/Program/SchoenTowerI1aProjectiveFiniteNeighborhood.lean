import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import HodgeLean.Foundations.Program.SchoenTowerI1aProjNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI1aFiniteAffineShrink
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_projective_finite_neighborhood
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (N : X.left.Opens) (s : Finset X.left) (hs : ∀ x ∈ s, x ∈ N) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ U ≤ N ∧ ∀ x ∈ s, x ∈ U := by
  classical
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := X.hom)
  let 𝒜 := homogeneousSubmodule (Fin (P.ambientDimension + 1)) (ULift.{0} ℤ)
  let π : ℙ(Fin (P.ambientDimension + 1); Spec ↧ℂ) ⟶ Proj 𝒜 :=
    pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj 𝒜))
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  haveI : IsAffine (terminal (C := Scheme)) :=
    IsAffine.of_isIso (terminalIsTerminal.uniqueUpToIso specZIsTerminal).hom
  haveI : IsAffineHom π := MorphismProperty.pullback_snd
    (terminal.from (Spec ↧ℂ)) (terminal.from (Proj 𝒜))
    (inferInstance : IsAffineHom (terminal.from (Spec ↧ℂ)))
  let f : X.left ⟶ Proj 𝒜 := P.immersion ≫ π
  haveI : IsAffineHom f := by dsimp [f]; infer_instance
  obtain ⟨A, hA, hsA⟩ := s2v_i1ahi_proj_finite_affine_neighborhood 𝒜 (s.image f)
  let U := f ⁻¹ᵁ A
  have hU : IsAffineOpen U := hA.preimage f
  have hsU : ∀ x ∈ s, x ∈ U := fun x hx => hsA (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  let t : Finset U.toScheme := s.attach.image (fun x => ⟨x.val, hsU x.val x.property⟩)
  have ht : ∀ x ∈ t, x ∈ U.ι ⁻¹ᵁ N := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact hs y.val y.property
  letI : IsAffine U.toScheme := hU
  obtain ⟨V, hV, hVN, htV⟩ := s2v_i1ahi_finite_affine_shrink U.toScheme (U.ι ⁻¹ᵁ N) t ht
  refine ⟨U.ι ''ᵁ V, hV.image_of_isOpenImmersion U.ι, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hVN hy
  · intro x hx
    refine ⟨⟨x, hsU x hx⟩, ?_, rfl⟩
    exact htV _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)

end HodgeLean.Foundations.Program
