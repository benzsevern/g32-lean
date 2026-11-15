import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeCochainCone

/-! # Relative lifts for the R2 supported pairing

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- A class restricting to zero on the subspace has a relative lift, including degree zero.
Source: Hatcher, Algebraic Topology, §3.1, long exact sequence of a pair.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_relative_lift (P : TopPair.{0}) (n : ℕ)
    (u : Cohomology ℚ P.fst n) (hu : cohomologyMap ℚ n P.hom u = 0) :
    ∃ v : RelativeCohomology ℚ P n, relativeCohomologyToAbsolute ℚ P n v = u := by
  have hse : (relativeDualCochainShortComplexNat ℚ P).ShortExact := by
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
    exact fun j => (relativeDualCochainShortComplexNatDegreewiseSplitting ℚ P j).shortExact
  exact ((ShortComplex.moduleCat_exact_iff _).mp (hse.homology_exact₂ n)) u hu

#print axioms s4_assembly_relative_lift
end HodgeLean.Foundations.Program
