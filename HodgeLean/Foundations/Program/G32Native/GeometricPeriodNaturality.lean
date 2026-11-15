import HodgeLean.Foundations.Program.G32Native.PrintedPolarizedTriple
import HodgeLean.Foundations.AbelianQuotient.Surjectivity

noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- The period equivalence intertwines integral geometric pullback and tangent transpose.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2. -/
theorem geometricPeriod_integral (f : AbelianEnd A) (w : ℂ ⊗[ℚ] HQ A 1) :
    abelianPeriodComplexEquiv A ((abelianEndAction A f).baseChange ℂ w) =
      (abelianPeriodComplexEquiv A w).comp
        ((printedAnalyticAction A ((1 : ℚ) ⊗ₜ[ℤ] f)).restrictScalars ℝ) := by
  apply latticeRestriction_injective A
  funext l
  rw [latticeRestriction_abelianPeriodComplexEquiv]
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb, LinearMap.add_comp,
      LinearMap.add_apply, latticeRestriction]
  | tmul c x =>
    let F := printedAnalyticAction A ((1 : ℚ) ⊗ₜ[ℤ] f)
    let hF := printedAnalyticAction_integral A f
    let m : abelianPeriodLattice A :=
      ⟨F l, AbelianQuotient.homPullback_analyticRepresentation_mem_lattice f.hom F hF l⟩
    have hp := AbelianQuotient.abelianPeriod_homPullback_analyticRepresentation
      f.hom F hF x l
    have hm := congrFun (latticeRestriction_abelianPeriodComplexEquiv A (c ⊗ₜ x)) m
    change c * (abelianPeriod A (abelianEndAction A f x) l : ℂ) = _
    change c * (abelianPeriod A (homPullback f.hom 1 x) l : ℂ) = _
    rw [hp]
    exact hm.symm

/-- Period naturality extends from integral to rational geometric endomorphisms.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2. -/
theorem geometricPeriod_rational (f : AbelianEnd0 A) (w : ℂ ⊗[ℚ] HQ A 1) :
    abelianPeriodComplexEquiv A ((abelianEnd0Action A f).unop.baseChange ℂ w) =
      (abelianPeriodComplexEquiv A w).comp
        ((printedAnalyticAction A f).restrictScalars ℝ) := by
  induction f using TensorProduct.inductionOn with
  | add f g hf hg =>
    simp only [map_add, MulOpposite.unop_add, LinearMap.baseChange_add,
      LinearMap.add_apply, hf, hg]
    apply LinearMap.ext
    intro v
    exact (map_add (abelianPeriodComplexEquiv A w) _ _).symm
  | tmul q f =>
    have hq : q ⊗ₜ[ℤ] f = q • ((1 : ℚ) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hq, map_smul, map_smul, MulOpposite.unop_smul, LinearMap.baseChange_smul,
      LinearMap.smul_apply, LinearMapClass.map_smul_of_tower]
    have hi := geometricPeriod_integral A f w
    rw [spec_g4_abelianEnd0Action_tmul, one_smul, MulOpposite.unop_op] 
    rw [hi]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    exact (LinearMap.map_smul_of_tower (abelianPeriodComplexEquiv A w) q
      (printedAnalyticAction A ((1 : ℚ) ⊗ₜ[ℤ] f) v)).symm

#print axioms geometricPeriod_rational
#print axioms geometricPeriod_integral
end HodgeLean.Foundations.Program.G32Native
