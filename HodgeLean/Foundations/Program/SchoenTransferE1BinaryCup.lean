import HodgeLean.Foundations.Program.SchoenTransferE1Binary

/-! The binary comparison on the actual algebraic cohomology spaces. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The binary projection cup transports to the actual topological projection cup.
Source: Hatcher, Algebraic Topology, §3.2, naturality of external cups. -/
theorem s4_e1_binaryCup_comparison
    (A B : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral (A ⊗ B).left] [Smooth (A ⊗ B).hom] [IsProjective (A ⊗ B).hom]
    (p q : ℕ) (x : HQ A p) (y : HQ B q) :
    cohomologyHomeomorphEquiv (complexPointProdHomeomorph A B) (p + q)
      (cupComparison (A ⊗ B) (p + q) ((cupProductOf (A ⊗ B)).cup rfl
        (homPullback (fst A B) p x) (homPullback (snd A B) q y))) =
    cup (TopCat.of (ComplexPoint A × ComplexPoint B)) rfl
      (AlgebraicTopology.Singular.cohomologyMap ℚ p
        (productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B))) (cupComparison A p x))
      (AlgebraicTopology.Singular.cohomologyMap ℚ q
        (productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B))) (cupComparison B q y)) := by
  let h := complexPointProdHomeomorph A B
  let g : TopCat.of (ComplexPoint A × ComplexPoint B) ⟶ TopCat.of (ComplexPoint (A ⊗ B)) :=
    TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hgA : g ≫ TopCat.ofHom (Point.continuousMap (fst A B)) = productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B)) := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Prod.fst (h.apply_symm_apply z)
  have hgB : g ≫ TopCat.ofHom (Point.continuousMap (snd A B)) = productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B)) := by
    apply ConcreteCategory.hom_ext
    intro z
    exact congrArg Prod.snd (h.apply_symm_apply z)
  have hpA : AlgebraicTopology.Singular.cohomologyMap ℚ p g
      (cupComparison (A ⊗ B) p (homPullback (fst A B) p x)) =
      AlgebraicTopology.Singular.cohomologyMap ℚ p (productFirst (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B))) (cupComparison A p x) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    change (AlgebraicTopology.Singular.cohomologyMap ℚ p g ∘ₗ
      AlgebraicTopology.Singular.cohomologyMap ℚ p (TopCat.ofHom (Point.continuousMap (fst A B)))) _ = _
    rw [← AlgebraicTopology.Singular.cohomologyMap_comp, hgA]
  have hpB : AlgebraicTopology.Singular.cohomologyMap ℚ q g
      (cupComparison (A ⊗ B) q (homPullback (snd A B) q y)) =
      AlgebraicTopology.Singular.cohomologyMap ℚ q (productSecond (TopCat.of (ComplexPoint A)) (TopCat.of (ComplexPoint B))) (cupComparison B q y) := by
    simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    change (AlgebraicTopology.Singular.cohomologyMap ℚ q g ∘ₗ
      AlgebraicTopology.Singular.cohomologyMap ℚ q (TopCat.ofHom (Point.continuousMap (snd A B)))) _ = _
    rw [← AlgebraicTopology.Singular.cohomologyMap_comp, hgB]
  rw [cupComparison_cup]
  change AlgebraicTopology.Singular.cohomologyMap ℚ (p + q) g _ = _
  rw [cohomologyMap_cup, hpA, hpB]

set_option backward.isDefEq.respectTransparency false in
/-- The binary equivalence evaluates each pure summand by the specified projection cup.
Source: Hatcher, Algebraic Topology, §3.2, external cup products. -/
theorem s4_e1_binaryEquiv_tmul
    (A B : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral (A ⊗ B).left] [Smooth (A ⊗ B).hom] [IsProjective (A ⊗ B).hom]
    (p q : ℕ) (x : HQ A p) (y : HQ B q) :
    s4_e1_binaryEquiv A B (p + q)
      (DirectSum.lof ℚ _ _ ⟨(p, q), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩ (x ⊗ₜ[ℚ] y)) =
    (cupProductOf (A ⊗ B)).cup rfl
      (homPullback (fst A B) p x) (homPullback (snd A B) q y) := by
  apply (cupComparison (A ⊗ B) (p + q)).injective
  apply (cohomologyHomeomorphEquiv (complexPointProdHomeomorph A B) (p + q)).injective
  rw [s4_e1_binaryCup_comparison]
  simp only [s4_e1_binaryEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  simp only [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, TensorProduct.congr_tmul]
  exact rationalProductCohomologyEquiv_tmul _ _ _ p q _ _

/-- The binary equivalence with the explicit degree-equality indexing used by power iteration.
Source: Hatcher, Algebraic Topology, §3.2, field-coefficient Künneth. -/
def s4_e1_binaryDegreeEquiv
    (A B : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral (A ⊗ B).left] [Smooth (A ⊗ B).hom] [IsProjective (A ⊗ B).hom]
    (n : ℕ) :
    (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = n}, HQ A p.val.1 ⊗[ℚ] HQ B p.val.2) ≃ₗ[ℚ]
      HQ (A ⊗ B) n :=
  (DirectSum.lequivCongrLeft ℚ (M := fun p : {p : ℕ × ℕ // p.1 + p.2 = n} => HQ A p.val.1 ⊗[ℚ] HQ B p.val.2)
    (s4_e1_binaryIndexEquiv n)).trans (s4_e1_binaryEquiv A B n)

/-- The explicitly indexed binary equivalence has the same projection-cup formula.
Source: Hatcher, Algebraic Topology, §3.2, external cup products. -/
theorem s4_e1_binaryDegreeEquiv_tmul
    (A B : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral (A ⊗ B).left] [Smooth (A ⊗ B).hom] [IsProjective (A ⊗ B).hom]
    (n : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = n}) (x : HQ A p.val.1) (y : HQ B p.val.2) :
    s4_e1_binaryDegreeEquiv A B n (DirectSum.lof ℚ _ _ p (x ⊗ₜ[ℚ] y)) =
    (cupProductOf (A ⊗ B)).cup p.property
      (homPullback (fst A B) p.val.1 x) (homPullback (snd A B) p.val.2 y) := by
  rcases p with ⟨⟨i, j⟩, rfl⟩
  dsimp only [s4_e1_binaryDegreeEquiv, LinearEquiv.trans_apply]
  erw [DirectSum.lequivCongrLeft_lof ℚ (e := s4_e1_binaryIndexEquiv (i + j))
    (k := ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩) rfl _ _ rfl]
  exact s4_e1_binaryEquiv_tmul A B i j x y

#print axioms s4_e1_binaryDegreeEquiv_tmul
#print axioms s4_e1_binaryEquiv_tmul
#print axioms s4_e1_binaryEquiv
end HodgeLean.Foundations.Program
