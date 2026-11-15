import HodgeLean.Foundations.Program.G32Native.AnticommutingEigenspaces

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.G32Native

/-- The anticommuting quaternion pairs the two embedding eigenspaces on a
Hodge summand. Conjugation then gives the balanced Weil-type condition.
Source: G32 v0.16, Lemma 8.1, first paragraph of proof;
Birkenhake–Lange, Complex Abelian Varieties, second edition, sections 9.4–9.6. -/
theorem TypeIIISixfoldData.inducedWeilAction_isWeilType
    {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    {pol : HQ A 2} (Q : TypeIIISixfoldData A pol) :
    letI := (torusCohomology_cupProductOf A).finite
    Q.inducedWeilAction.IsWeilType := by
  letI := (torusCohomology_cupProductOf A).finite
  let u : ℍ[ℚ, -3, 0, Q.b] := ⟨0, 1, 0, 0⟩
  let j : ℍ[ℚ, -3, 0, Q.b] := ⟨0, 0, 1, 0⟩
  let W := Q.inducedWeilAction
  let Tq : Module.End ℚ (HQ A 1) := (Q.pullback (Q.endomorphisms j)).unop
  let T := Tq.baseChange ℂ
  have hj : j * j = algebraMap ℚ ℍ[ℚ, -3, 0, Q.b] Q.b := by
    ext <;> simp [j, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.algebraMap_eq]
  have hsqQ : Tq.comp Tq = Q.b • LinearMap.id := by
    have h := congrArg (fun z => (Q.pullback (Q.endomorphisms z)).unop) hj
    simpa only [Tq, j, map_mul, map_smul, map_one, AlgEquiv.commutes, AlgHom.commutes,
      MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_one,
      MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      Algebra.algebraMap_eq_smul_one, Module.End.mul_eq_comp, Module.End.one_eq_id] using h
  have hju : j * u = -(u * j) := by
    ext <;> simp [j, u, QuaternionAlgebra.mk_mul_mk]
  have hantiQ : W.J.comp Tq = -(Tq.comp W.J) := by
    have h := congrArg (fun z => (Q.pullback (Q.endomorphisms z)).unop) hju
    simpa only [W, TypeIIISixfoldData.inducedWeilAction, Tq, j, u,
      map_mul, map_neg, MulOpposite.unop_mul, MulOpposite.unop_neg,
      Module.End.mul_eq_comp] using h
  have hsqC : T.comp T = Q.b • LinearMap.id := by
    have h := congrArg (fun f : Module.End ℚ (HQ A 1) => f.baseChange ℂ) hsqQ
    simpa only [T, LinearMap.baseChange_comp, LinearMap.baseChange_smul,
      LinearMap.baseChange_id] using h
  have hinj : Function.Injective T := by
    intro x y hxy
    have h := congrArg T hxy
    have h' : Q.b • x = Q.b • y := by
      simpa only [← LinearMap.comp_apply, hsqC, LinearMap.smul_apply,
        LinearMap.id_apply] using h
    have h'' := congrArg (fun z => Q.b⁻¹ • z) h'
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_lt Q.b_neg), one_smul] using h''
  have hantiC : ∀ x, W.Jc (T x) = -T (W.Jc x) := by
    have h := congrArg (fun f : Module.End ℚ (HQ A 1) => f.baseChange ℂ) hantiQ
    have h' : W.Jc.comp T = -(T.comp W.Jc) := by
      simpa only [T, HodgeBlocks.WeilAction.Jc, LinearMap.baseChange_comp,
        LinearMap.baseChange_neg] using h
    intro x
    exact LinearMap.congr_fun h' x
  let P := (abelianVarietyCohomologyOf (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A)).weight1.H (0, 1)
  have hP : P.map T ≤ P := Q.pullback_preserves_pieces (Q.endomorphisms j) (0, 1)
  have hdim := finrank_eigenspace_inf_eq_of_anticommutes W.Jc T P hinj hantiC hP
    (HodgeBlocks.WeilAction.omegaC 3)
  have hconj := finrank_Vsbar_inf_H01 (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A) W
  apply (isWeilType_iff_finrank_eq (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A) W).mpr
  exact hconj.symm.trans hdim.symm

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.inducedWeilAction_isWeilType
