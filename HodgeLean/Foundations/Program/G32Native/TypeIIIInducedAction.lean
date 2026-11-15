import HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData
import HodgeLean.Adapters.AbelianCMData

noncomputable section
set_option maxHeartbeats 200000
open scoped Quaternion TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program.G32Native
variable {A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] {pol : HQ A 2}

/-- The retained rational pullback preserves the two lattice Hodge summands.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition,
section 1.2 and Theorem 1.4.1; `spec_abelianEndAction_hodge`. -/
theorem TypeIIISixfoldData.pullback_hodge (Q : TypeIIISixfoldData A pol)
    (x : AbelianEnd0 A) : (Q.pullback x).unop ∈ hodgeEndH1 A := by
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
    have hq : q ⊗ₜ[ℤ] f = q • ((1 : ℚ) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hq, map_smul, Q.pullback_integral]
    change q • abelianEndAction A f ∈ hodgeEndH1 A
    exact Subalgebra.smul_mem _ (spec_abelianEndAction_hodge A f) q
  | add x y hx hy =>
    rw [map_add, MulOpposite.unop_add]
    exact Subalgebra.add_mem _ hx hy

/-- The same preservation, on the canonical weight-one Hodge pieces.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition,
Theorem 1.4.1; `spec_g4_cohomologyHodgePiece_one_eq`. -/
theorem TypeIIISixfoldData.pullback_preserves_pieces (Q : TypeIIISixfoldData A pol)
    (x : AbelianEnd0 A) (pq : ℤ × ℤ) :
    (cohomologyHodgePiece A 1 pq).map ((Q.pullback x).unop.baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq := by
  have hx := Q.pullback_hodge x
  rw [spec_g4_cohomologyHodgePiece_one_eq A]
  unfold latticeHodgePieces
  split_ifs
  · exact hx.1
  · exact hx.2
  · rw [Submodule.map_bot]

/-- The actual induced rational operator has square `−3`.
Source: G32 v0.16, section 8, the chosen quaternion generator `u² = −3`. -/
theorem TypeIIISixfoldData.generator_sq (Q : TypeIIISixfoldData A pol) :
    let J := (Q.pullback (Q.endomorphisms
      (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop
    J.comp J = (-3 : ℚ) • LinearMap.id := by
  let u : ℍ[ℚ, -3, 0, Q.b] := ⟨0, 1, 0, 0⟩
  have hu : u * u = algebraMap ℚ ℍ[ℚ, -3, 0, Q.b] (-3) := by
    ext <;> norm_num [u, QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.algebraMap_eq]
  have h := congrArg (fun z => (Q.pullback (Q.endomorphisms z)).unop) hu
  simpa only [u, map_mul, map_smul, map_one, AlgEquiv.commutes, AlgHom.commutes,
    MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_one,
    MulOpposite.algebraMap_apply, MulOpposite.unop_op,
    Algebra.algebraMap_eq_smul_one, Module.End.mul_eq_comp, Module.End.one_eq_id] using h

/-- The Eisenstein Hodge action induced by the actual quaternionic endomorphism.
Source: G32 v0.16, Lemma 8.1; Birkenhake–Lange, Complex Abelian Varieties,
second edition, sections 1.2 and 9.6. -/
def TypeIIISixfoldData.inducedWeilAction (Q : TypeIIISixfoldData A pol) :
    letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3 :=
  letI := (torusCohomology_cupProductOf A).finite
  { J := (Q.pullback (Q.endomorphisms (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, Q.b]))).unop
    J_sq := Q.generator_sq
    preserves := Q.pullback_preserves_pieces _ }

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.pullback_hodge
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.pullback_preserves_pieces
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.generator_sq
#print axioms HodgeLean.Foundations.Program.G32Native.TypeIIISixfoldData.inducedWeilAction
