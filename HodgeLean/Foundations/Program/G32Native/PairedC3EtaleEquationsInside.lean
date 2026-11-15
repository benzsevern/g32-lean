import HodgeLean.Foundations.Program.G32Native.PairedC3EtaleSliceEquations
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Prescribed equations inside the original affine neighbourhood -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Étale slice coordinates can be chosen inside an existing affine chart.
Any original section with the prescribed coordinate germ then agrees with
that coordinate as an actual section on the smaller chart.
Source: Hartshorne, Algebraic Geometry, II.3, II.5 and II.8;
EGA IV, 17.11.1. -/
theorem paired_c3_etale_equations_inside
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (I : X.left.IdealSheafData)
    (x : ComplexPoint X) (V : X.left.affineOpens) (hxV : x.underlying ∈ V.1) :
    let A := X.left.presheaf.stalk x.underlying
    ∀ (c : Fin n → A) (hc : ∀ j, c j ∈ IsLocalRing.maximalIdeal A)
      (b : Module.Basis (Fin n) (IsLocalRing.ResidueField A)
        (IsLocalRing.maximalIdeal A).Cotangent),
      (∀ j, b j = (IsLocalRing.maximalIdeal A).toCotangent ⟨c j, hc j⟩) →
      ∀ (k : ℕ) (sel : Fin k → Fin n),
      I.stalkIdeal x.underlying = Ideal.span (Set.range (c ∘ sel)) →
      ∃ (U : X.left.affineOpens) (hUV : U ≤ V) (hxU : x.underlying ∈ U.1),
        letI := s2e_step1_sectionAlgebra X U.1
        ∃ F : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, U.1),
          F.toRingHom.Etale ∧
          I.ideal U = Ideal.span (Set.range (fun j => F (MvPolynomial.X (sel j)))) ∧
          (∀ j, (X.left.presheaf.germ U.1 x.underlying hxU).hom
            (F (MvPolynomial.X j)) = c j) ∧
          ∀ (j : Fin n) (d : Γ(X.left, V.1)),
            (X.left.presheaf.germ V.1 x.underlying hxV).hom d = c j →
            (X.left.presheaf.map (homOfLE hUV).op).hom d = F (MvPolynomial.X j) := by
  dsimp only
  intro c hc b hb k sel hgen
  obtain ⟨W, hxW, G, hG, hI, hg⟩ :=
    paired_c3_etale_slice_equations X n I x c hc b hb k sel hgen
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x.underlying ∈ W.1 ⊓ V.1 from ⟨hxW, hxV⟩)
  let Ub : X.left.affineOpens := ⟨U, hU⟩
  have hUW : Ub ≤ W := hsub.trans inf_le_left
  have hUV : Ub ≤ V := hsub.trans inf_le_right
  letI := s2e_step1_sectionAlgebra X W.1
  letI := s2e_step1_sectionAlgebra X U
  let ρ := s2e_sectionRestrictionAlgHom X W.1 U hUW
  let F := ρ.comp G
  have hF : F.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _ hG
    (s2e_affine_section_restriction_etale X W Ub hUW)
  have hf (j : Fin n) : (X.left.presheaf.germ U x.underlying hxU).hom
      (F (MvPolynomial.X j)) = c j := by
    change (X.left.presheaf.map (homOfLE hUW).op ≫
      X.left.presheaf.germ U x.underlying hxU).hom (G (MvPolynomial.X j)) = c j
    exact (congrArg (fun q : Γ(X.left, W.1) ⟶ X.left.presheaf.stalk x.underlying =>
      q.hom (G (MvPolynomial.X j)))
      (X.left.presheaf.germ_res (homOfLE hUW) x.underlying hxU)).trans (hg j)
  refine ⟨Ub, hUV, hxU, F, hF, ?_, hf, ?_⟩
  · rw [← I.map_ideal hUW, hI, Ideal.map_span, ← Set.range_comp]
    rfl
  · intro j d hd
    apply germ_injective_of_isIntegral X.left x.underlying hxU
    rw [hf]
    change (X.left.presheaf.map (homOfLE hUV).op ≫
      X.left.presheaf.germ U x.underlying hxU).hom d = c j
    exact (congrArg (fun q : Γ(X.left, V.1) ⟶ X.left.presheaf.stalk x.underlying =>
      q.hom d) (X.left.presheaf.germ_res (homOfLE hUV) x.underlying hxU)).trans hd

#print axioms paired_c3_etale_equations_inside
end HodgeLean.Foundations.Program.G32Native
