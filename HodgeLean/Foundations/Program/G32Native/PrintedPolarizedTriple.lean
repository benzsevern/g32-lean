import HodgeLean.Adapters.PWTheorem42EisensteinDefs
import HodgeLean.Foundations.PositivePolarization
import HodgeLean.Foundations.Program.G32Native.PolarizationDualDeterminant

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.RealDefs.Compare.Markman

namespace HodgeLean.Foundations.Program.G32Native

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- The rational analytic representation on the universal-cover tangent model.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2; `spec_analyticRepresentation_ringHom`.
The coordinates are those of `complexExponential A (dim A.left)`. -/
def printedAnalyticAction : AbelianEnd0 A →ₐ[ℚ] Module.End ℂ (Fin (dim A.left) → ℂ) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ _)
    (Classical.choose (spec_analyticRepresentation_ringHom A)).toIntAlgHom
    fun q _ => by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left q _

/-- The rational analytic representation agrees with the actual analytic lift on integral
endomorphisms.
Source: Birkenhake–Lange, §1.2; `spec_analyticRepresentation_ringHom`. -/
theorem printedAnalyticAction_integral (f : AbelianEnd A) (v : Fin (dim A.left) → ℂ) :
    Additive.toMul (complexExponential A (dim A.left)
      (printedAnalyticAction A ((1 : ℚ) ⊗ₜ[ℤ] f) v)) =
      Point.map f.hom (Additive.toMul (complexExponential A (dim A.left) v)) := by
  have h := Classical.choose_spec (spec_analyticRepresentation_ringHom A) f v
  simp only [printedAnalyticAction, Algebra.TensorProduct.lift_tmul,
    Algebra.ofId_apply, map_one, one_mul]
  exact h

/-- A period-lattice vector as a rational homology functional.
Source: Birkenhake–Lange, §1.1; `abelianPeriod` evaluates cohomology on the specified loop. -/
def printedLatticeVector (l : abelianPeriodLattice A) : Dual ℚ (HQ A 1) :=
  (LinearMap.proj l).comp (abelianPeriod A)

/-- The real extension of a rational homological form, in the dual-of-cohomology model.
Source: Bourbaki, Algebra, II §5; `IsBaseChange.toDualBaseChange`. -/
def printedRealForm (E : LinearMap.BilinForm ℚ (Dual ℚ (HQ A 1))) :
    LinearMap.BilinForm ℝ (Dual ℝ (ℝ ⊗[ℚ] HQ A 1)) :=
  letI := (torusCohomology_cupProductOf A).finite
  let e := ((TensorProduct.isBaseChange ℚ (HQ A 1) ℝ).toDualBaseChange).symm
  (E.baseChange ℝ).compl₁₂ e.toLinearMap e.toLinearMap

/-- Printed geometric input in universal-cover tangent coordinates and rational homology
coordinates. Homology is represented by the dual of `HQ A 1`, with its actual period lattice;
the real complex structure is the transpose of the canonical structure on cohomology.
No cohomological membership field is supplied here.
Source: G32 v0.18, Definition 2.1, lines 133–142; van Geemen, LNM 1594, Lemma 5.2.
The two tangent eigenspaces have dimension three. The trace convention is the coefficient of
`omega` in `E(x,Jy) + omega * E(x,y)`, as in `WeilHermitian.weilHermitian`. -/
structure PrintedPolarizedTriple where
  action : QuadraticAlgebra ℚ (-3) 0 →ₐ[ℚ] AbelianEnd0 A
  dim_eq : TopologicalSpace.dim A.left = 6
  tangent_plus : finrank ℂ (Module.End.eigenspace
    (printedAnalyticAction A (action QuadraticAlgebra.omega)) (HodgeBlocks.WeilAction.omegaC 3)) = 3
  tangent_minus : finrank ℂ (Module.End.eigenspace
    (printedAnalyticAction A (action QuadraticAlgebra.omega)) (-HodgeBlocks.WeilAction.omegaC 3)) = 3
  E : LinearMap.BilinForm ℚ (Dual ℚ (HQ A 1))
  alternating : E.IsAlt
  nondegenerate : E.Nondegenerate
  compatible : ∀ x y,
    E ((pwAction A action QuadraticAlgebra.omega).dualMap x) y =
      -E x ((pwAction A action QuadraticAlgebra.omega).dualMap y)
  riemann_invariant : ∀ x y : Dual ℝ (ℝ ⊗[ℚ] HQ A 1),
    printedRealForm A E
      (x ∘ₗ weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A))
      (y ∘ₗ weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)) =
        printedRealForm A E x y
  riemann_positive : ∀ x : Dual ℝ (ℝ ⊗[ℚ] HQ A 1), x ≠ 0 →
    0 < printedRealForm A E
      (x ∘ₗ weightOneComplexStructure A (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)) x
  integral_scale : ∃ c : ℚ, 0 < c ∧ ∀ l m : abelianPeriodLattice A,
    ∃ z : ℤ, c * E (printedLatticeVector A l) (printedLatticeVector A m) = z

namespace PrintedPolarizedTriple
variable {A}
/-- The induced cohomological action; its Hodge preservation comes from geometric pullback.
Source: Birkenhake–Lange, §1.2; `f1_weilAction`. -/
def W (P : PrintedPolarizedTriple A) :=
  f1_weilAction A P.action QuadraticAlgebra.omega 3 (by
    rw [QuadraticAlgebra.omega_pow_two_eq_add]; norm_num [Algebra.algebraMap_eq_smul_one])

/-- The printed Hermitian discriminant on rational homology.
Source: van Geemen, LNM 1594, Lemma 5.2; G32 v0.18, line 139.
Its form is exactly `E(x,Jy) + omega * E(x,y)`, without a signed determinant factor. -/
def discriminant (P : PrintedPolarizedTriple A) :
    ℚˣ ⧸ HermitianForm.normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  letI := (torusCohomology_cupProductOf A).finite
  weilDetClass P.E (transposeAction ⟨P.W.J, P.W.J_sq⟩)
    P.compatible P.alternating P.nondegenerate
end PrintedPolarizedTriple
end HodgeLean.Foundations.Program.G32Native
