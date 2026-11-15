import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelianIntegralPeriods
import HodgeLean.Foundations.IntegralHomology.Basic
import HodgeLean.Foundations.Singular.TorusRing

/-! # Rational dimension of the actual integral abelian lattice

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations HodgeLean.Foundations.IntegralHomology
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Rationalizing the integral torsion quotient has the dimension of the original exponential lattice.
Source: Hatcher, §3.A; rationalComparison; finrank_cohomology_one_unitAddTorus.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralLattice_rank :
    Module.Finite ℚ (ℚ ⊗[ℤ] IntegralHomology.Lattice (TopCat.of (ComplexPoint A))) ∧
      Module.finrank ℚ (ℚ ⊗[ℤ] IntegralHomology.Lattice (TopCat.of (ComplexPoint A))) =
        2 * TopologicalSpace.dim A.left := by
  let X := TopCat.of (ComplexPoint A)
  let e := Singular.cohomologyHomeomorphEquiv
    (complexPointTorusHomeomorph A (TopologicalSpace.dim A.left)) 1
  letI := Singular.finite_cohomology_unitAddTorus (2 * TopologicalSpace.dim A.left) 1
  letI : Module.Finite ℚ (Cohomology ℚ X 1) := Module.Finite.equiv e.symm
  let d := cohomologyEquivDualHomology ℚ X 1
  letI : Module.Finite ℚ (Module.Dual ℚ (Homology ℚ X 1)) := Module.Finite.equiv d
  letI : Module.Finite ℚ (Homology ℚ X 1) := (Module.finite_dual_iff ℚ).mp inferInstance
  obtain ⟨c, hc⟩ := coefficient_chainMap X
  obtain ⟨r, _⟩ := rationalComparison X c hc
  letI : Module.Finite ℚ ((QChains X).homology 1) := by
    change Module.Finite ℚ (Homology ℚ X 1)
    infer_instance
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] IntegralHomology.Lattice X) := Module.Finite.equiv r.symm
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℚ (ℚ ⊗[ℤ] IntegralHomology.Lattice X) = Module.finrank ℚ (Homology ℚ X 1) := r.finrank_eq
    _ = Module.finrank ℚ (Module.Dual ℚ (Homology ℚ X 1)) := (Subspace.dual_finrank_eq).symm
    _ = Module.finrank ℚ (Cohomology ℚ X 1) := d.finrank_eq.symm
    _ = Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin (2 * TopologicalSpace.dim A.left)))) 1) := e.finrank_eq
    _ = 2 * TopologicalSpace.dim A.left := Singular.finrank_cohomology_one_unitAddTorus _

/-- Integral displacement is injective after the actual torsion quotient.
Source: Hatcher, §3.A; Birkenhake–Lange, §1.1; abelianIntegralLattice_rank.
HC no distance; AV milestone no distance. -/
theorem abelianIntegralPeriod_injective : Function.Injective (abelianIntegralPeriod A) := by
  letI := (abelianIntegralLattice_rank A).1
  letI := isZLattice_complexExponentialLattice A (TopologicalSpace.dim A.left)
  have hd : Module.finrank ℚ (ℚ ⊗[ℤ] IntegralHomology.Lattice (TopCat.of (ComplexPoint A))) =
      Module.finrank ℚ (ℚ ⊗[ℤ] abelianPeriodLattice A) := by
    rw [(abelianIntegralLattice_rank A).2, Module.finrank_baseChange]
    exact (finrank_complexExponentialLattice A (TopologicalSpace.dim A.left)).symm
  have hi : Function.Injective ((abelianIntegralPeriod A).baseChange ℚ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
      (LinearMap.baseChange_surjective ℚ (abelianIntegralPeriod_surjective A))
  intro x y hxy
  have ht : (1 : ℚ) ⊗ₜ[ℤ] x = (1 : ℚ) ⊗ₜ[ℤ] y := by
    apply hi
    simpa only [LinearMap.baseChange_tmul] using
      congrArg (fun l : abelianPeriodLattice A ↦ (1 : ℚ) ⊗ₜ[ℤ] l) hxy
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  let X := TopCat.of (ComplexPoint A)
  obtain ⟨c, hc⟩ := coefficient_chainMap X
  obtain ⟨r, hr⟩ := rationalComparison X c hc
  have huv : coefficientH1 X c u = coefficientH1 X c v :=
    (hr u).symm.trans ((congrArg r ht).trans (hr v))
  apply (Submodule.Quotient.eq _).mpr
  rw [← coefficient_kernel X c hc]
  exact LinearMap.mem_ker.mpr (by rw [map_sub, huv, sub_self])

/-- The integral singular torsion quotient identified with the specified exponential period lattice.
Source: Birkenhake–Lange, §1.1; Hatcher, §3.A; abelianIntegralPeriod_loop.
HC no distance; AV milestone no distance. -/
def abelianIntegralPeriodEquiv :
    IntegralHomology.Lattice (TopCat.of (ComplexPoint A)) ≃ₗ[ℤ] abelianPeriodLattice A :=
  LinearEquiv.ofBijective (abelianIntegralPeriod A)
    ⟨abelianIntegralPeriod_injective A, abelianIntegralPeriod_surjective A⟩

#print axioms abelianIntegralLattice_rank
#print axioms abelianIntegralPeriod_injective
#print axioms abelianIntegralPeriodEquiv

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
