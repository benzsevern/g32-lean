import HodgeLean.Foundations.Program.SchoenTowerL1aAffineOpenEquations
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantPrincipalSupport
import HodgeLean.Foundations.Program.SchoenTowerL1aPointAction

/-! # Compatible principal restrictions of actual affine quotients

Implication from the actual invariant section image and a prescribed orbit
neighborhood to a principal quotient neighborhood with compatible preimage.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- An actual affine invariant quotient can be restricted inside any prescribed
open containing the specified finite rational orbit.
Source: Stacks Project, tag 04A9; Hartshorne, Algebraic Geometry, II.2, principal opens. -/
theorem s2v_l1a_scheme_open_refinement
    (X Y : Over (Spec ↧ℂ)) [IsAffine X.left] [IsAffine Y.left]
    (G : Type) [Group G] [Fintype G] (a : G →* Aut X) (q : X ⟶ Y)
    (himage : ∀ s : Γ(X.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
      ∀ g, (a g).asIso.hom.left.appTop.hom s = s)
    (p : ComplexPoint X) (W : X.left.Opens)
    (hW : ∀ g, (Point.map (a g).asIso.hom p).underlying ∈ W) :
    ∃ c : Γ(Y.left, ⊤), Point.evaluate ⊤ c (Point.map q p) ≠ 0 ∧
      q.left ⁻¹ᵁ Y.left.basicOpen c ≤ W := by
  let a' := ((Over.forget (Spec ↧ℂ)).mapAut X).comp a
  letI := s2_schemeSectionAction X.left G a'
  letI := s2t_overSectionAction_smulCommClass X G a
  let φ := s2t_affinePointAlgHom X p
  let I := (Scheme.IdealSheafData.vanishingIdeal
    ⟨(W : Set X.left)ᶜ, W.isOpen.isClosed_compl⟩).ideal ⟨⊤, isAffineOpen_top X.left⟩
  have himage' (s : Γ(X.left, ⊤)) : s ∈ Set.range q.left.appTop.hom ↔
      ∀ g : G, g • s = s := by
    constructor
    · intro hs g
      exact ((himage s).mp hs) g⁻¹
    · intro hs
      apply (himage s).mpr
      intro g
      have H := hs g⁻¹
      change (a ((g⁻¹)⁻¹)).asIso.hom.left.appTop s = s at H
      simpa only [inv_inv] using H
  have hI (g : G) : ∃ r ∈ I, φ (g • r) ≠ 0 := by
    let p' := Point.map (a g⁻¹).asIso.hom p
    obtain ⟨r, hrW, hrp⟩ := (isAffineOpen_top X.left).exists_basicOpen_le
      ⟨p'.underlying, hW g⁻¹⟩ trivial
    refine ⟨r, (s2v_l1a_affine_open_vanishing_equation X.left W r).mpr hrW, ?_⟩
    have heval : φ (g • r) = Point.evaluate ⊤ r p' := by
      change ((s2t_affinePointAlgHom X p).comp
        (s2t_overSectionsAlgHom (a g⁻¹).asIso.hom)) r = _
      rw [← s2v_l1a_affine_point_evaluation_map]
      exact s2t_affinePointAlgHom_apply X p' r
    rw [heval]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r p'
      (show p' ∈ Point.overOpen ⊤ from trivial)).mp hrp
  obtain ⟨c, hc, hnc⟩ := s2v_l1a_invariant_principal_support
    q.left.appTop.hom himage' φ I hI
  refine ⟨c, ?_, ?_⟩
  · rw [← s2t_affinePointAlgHom_apply, s2v_l1a_affine_point_evaluation_map]
    exact hnc
  · rw [Scheme.preimage_basicOpen]
    exact (s2v_l1a_affine_open_vanishing_equation X.left W _).mp hc

end HodgeLean.Foundations.Program
