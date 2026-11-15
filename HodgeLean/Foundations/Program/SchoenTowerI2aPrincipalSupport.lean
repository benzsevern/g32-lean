import HodgeLean.Foundations.Program.SchoenTowerI2aActualBranchSections

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- An actual principal pullback ideal contains the specified point exactly
when its defining section evaluates to zero there.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, principal support and residue evaluation. -/
theorem s2v_i2a_principal_pullback_support_evaluation
    (U X : Over (Spec ↧ℂ)) [IsAffine U.left] (u : U ⟶ X)
    (I : X.left.IdealSheafData) (f : Γ(U.left, ⊤))
    (hI : (I.comap u.left).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {f})
    (p : ComplexPoint U) :
    (Point.map u p).underlying ∈ I.support ↔ Point.evaluate ⊤ f p = 0 := by
  have H := Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := I.comap u.left) (U := ⟨⊤, isAffineOpen_top U.left⟩)
    (x := p.underlying) (show p.underlying ∈ (⊤ : U.left.Opens) from trivial)
  rw [hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at H
  rw [Scheme.IdealSheafData.support_comap] at H
  change (Point.map u p).underlying ∈ I.support ↔
    p.underlying ∉ U.left.basicOpen f at H
  rw [H]
  have he := Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f p
    (show p ∈ Point.overOpen ⊤ from trivial)
  simpa only [Point.overOpen, Set.mem_setOf_eq, not_not] using not_congr he

/-- An actual descended branch product vanishes exactly when its scalar
value occurs among the actual ordered root evaluations.
Source: The field product criterion and functoriality of residue evaluation. -/
theorem s2v_i2a_actual_branch_evaluation_zero_iff
    (U V : Over (Spec ↧ℂ)) [IsAffine U.left] [IsAffine V.left]
    (q : V ⟶ U) (p : ComplexPoint V) (n : ℕ)
    (z : Fin n → Γ(V.left, ⊤)) (b : ℂ) (f : Γ(U.left, ⊤))
    (hf : q.left.appTop.hom f = ∏ i, (algebraMap ℂ Γ(V.left, ⊤) b - z i)) :
    Point.evaluate ⊤ f (Point.map q p) = 0 ↔
      ∃ i, Point.evaluate ⊤ (z i) p = b := by
  let φ := s2t_affinePointAlgHom V p
  rw [← s2t_affinePointAlgHom_apply, s2v_l1a_affine_point_evaluation_map]
  change φ (q.left.appTop.hom f) = 0 ↔ _
  rw [hf, map_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, map_sub, φ.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero]
  apply exists_congr
  intro i
  change b = (s2t_affinePointAlgHom V p) (z i) ↔ _
  rw [s2t_affinePointAlgHom_apply]
  exact eq_comm

end HodgeLean.Foundations.Program
