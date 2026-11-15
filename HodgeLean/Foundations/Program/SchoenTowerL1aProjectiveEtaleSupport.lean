import HodgeLean.Foundations.Program.SchoenTowerL1aProjectiveAffine
import HodgeLean.Foundations.Program.SchoenTowerL1aFiniteParameterNeighborhood

/-! # Etale coordinates retaining projective curve support

Implication from a smooth integral projective curve to one affine etale
coordinate neighborhood retaining a finite tuple, including repetitions.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual projective curve has an affine etale parameter neighborhood
retaining a finite tuple, vanishing at its first point and separating its support.
Source: Stacks Project, tag 054L; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_projective_etale_support
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1)
    (n : ℕ) (p : Fin (n + 1) → ComplexPoint Z) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ Z)
      (y : Fin (n + 1) → ComplexPoint U) (z : Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ (∀ j, Point.map u (y j) = p j) ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      Point.evaluate ⊤ z (y 0) = 0 ∧
      (∀ j k, p j ≠ p k → Point.evaluate ⊤ z (y j) ≠ Point.evaluate ⊤ z (y k)) := by
  classical
  obtain ⟨A, hpA⟩ := s2v_l1a_projective_finite_affine_neighborhood Z p
  let X := ComplexPoint.openScheme Z A.1
  let v := ComplexPoint.openInclusion Z A.1
  let a (j : Fin (n + 1)) : ComplexPoint X :=
    ComplexPoint.asOpenPoint Z A.1 (p j) (hpA j)
  letI : IsAffine X.left := A.2
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  letI : SmoothOfRelativeDimension 1 X.hom := by
    change SmoothOfRelativeDimension 1 (A.1.ι ≫ Z.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 A.1.ι Z.hom
  letI : Smooth X.hom := by
    change Smooth (A.1.ι ≫ Z.hom)
    infer_instance
  have ha (j : Fin (n + 1)) : Point.map v (a j) = p j := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac Z A.1 (p j) (hpA j)
  letI : Nonempty X.left := ⟨(a 0).underlying⟩
  letI : IsIntegral X.left := isIntegral_of_isOpenImmersion A.1.ι
  let κ := Set.range a
  letI : Fintype κ := (Set.finite_range a).fintype
  let k₀ : κ := ⟨a 0, ⟨0, rfl⟩⟩
  letI : Nonempty κ := ⟨k₀⟩
  let c (k : κ) : ℂ := ((Fintype.equivFin κ k).val : ℂ) -
    ((Fintype.equivFin κ k₀).val : ℂ)
  have hc : Function.Injective c := by
    intro i j hij
    apply (Fintype.equivFin κ).injective
    apply Fin.ext
    dsimp only [c] at hij
    exact_mod_cast (sub_left_inj.mp hij)
  obtain ⟨U, hU, u, y, z, hu, hy, hEt, hz⟩ :=
    s2v_l1a_finite_parameter_neighborhood X (fun k : κ => k.1) Subtype.val_injective c
  let k (j : Fin (n + 1)) : κ := ⟨a j, ⟨j, rfl⟩⟩
  letI : IsOpenImmersion u.left := hu
  refine ⟨U, hU, u ≫ v, (fun j => y (k j)), z,
    inferInstanceAs (IsOpenImmersion (u.left ≫ A.1.ι)), ?_, hEt, ?_, ?_⟩
  · intro j
    change Point.map v (Point.map u (y (k j))) = p j
    rw [hy]
    exact ha j
  · simpa only [k, k₀, c, sub_self] using hz k₀
  · intro j l hjl heq
    have hkl : k j = k l := hc ((hz (k j)).symm.trans (heq.trans (hz (k l))))
    have hal : a j = a l := congrArg Subtype.val hkl
    exact hjl ((ha j).symm.trans ((congrArg (Point.map v) hal).trans (ha l)))

end HodgeLean.Foundations.Program
