import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aAffineHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1aRestrictedInvariants
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! # Affine restrictions of the retained symmetric quotient

Implication from finiteness and permutation invariance of the retained map to
invariant affine neighborhoods over the actual complex base.
The parameter assertions remain separate; invariant section images are included.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained quotient has invariant affine neighborhoods with the actual
finite restricted map, invariant section image and the specified complex point.
Source: Hartshorne, Algebraic Geometry, II.3, finite morphisms and affine restriction. -/
theorem s2v_l1a_retained_affine_invariant_neighborhood
    (Z B : Over (Spec ↧ℂ)) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (W : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ W),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B ⟶ W, γ ≫ u = f)
    (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ (U V : Over (Spec ↧ℂ)) (_ : IsAffine U.left) (_ : IsAffine V.left)
      (u : U ⟶ B) (v : V ⟶ g3_power Z (h + 1)) (q : V ⟶ U),
      IsOpenImmersion u.left ∧ IsOpenImmersion v.left ∧ IsFinite q.left ∧
      v ≫ γ = q ≫ u ∧ x ∈ Set.range (Point.map v) ∧
      ∃ ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V),
        (∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ) ∧
        (∀ τ, ρ τ ≫ q = q) ∧
        Function.Injective q.left.appTop.hom ∧
        (∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
          ∀ τ, (ρ τ).left.appTop.hom s = s) := by
  let X := g3_power Z (h + 1)
  obtain ⟨U, hx, hV, hq, ρ, hρ, hρq⟩ := s2v_l1a_invariant_affine_neighborhood
    γ.left (fun τ => (s2_permute Z (h + 1) τ).left)
    (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) x.underlying
  let V := γ.left ⁻¹ᵁ U.1
  let Uo := ComplexPoint.openScheme B U.1
  let Vo := ComplexPoint.openScheme X V
  let u : Uo ⟶ B := ComplexPoint.openInclusion B U.1
  let v : Vo ⟶ X := ComplexPoint.openInclusion X V
  let q : Vo ⟶ Uo := Over.homMk (γ.left ∣_ U.1) (by
    change (γ.left ∣_ U.1) ≫ (U.1.ι ≫ B.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  let ρo (τ : Equiv.Perm (Fin (h + 1))) : Vo ⟶ Vo := Over.homMk (ρ τ) (by
    change ρ τ ≫ (V.ι ≫ X.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, hρ τ, Category.assoc, Over.w])
  refine ⟨Uo, Vo, U.2, hV, u, v, q, ?_, ?_, hq,
    ?_, ?_, ρo, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsOpenImmersion U.1.ι)
  · exact inferInstanceAs (IsOpenImmersion V.ι)
  · apply Over.OverMorphism.ext
    exact (morphismRestrict_ι γ.left U.1).symm
  · refine ⟨ComplexPoint.asOpenPoint X V x hx, ?_⟩
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X V x hx
  · intro τ
    apply Over.OverMorphism.ext
    exact hρ τ
  · intro τ
    apply Over.OverMorphism.ext
    exact hρq τ

  · obtain ⟨hinj, himage⟩ := s2v_l1a_retained_affine_invariants Z B h γ hγinv hγ U
    exact s2v_l1a_restricted_lift_invariant_image γ.left
      (fun τ => (s2_permute Z (h + 1) τ).left)
      (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) U.1 hinj himage ρ hρ

end HodgeLean.Foundations.Program
