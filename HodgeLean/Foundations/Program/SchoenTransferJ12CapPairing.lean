import HodgeLean.Foundations.Program.SchoenTransferJ12Cap
import HodgeLean.Foundations.Program.CompensationAssemblyCocycleCup

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Evaluation of the actual cup product is evaluation after the transported cap product.
Source: Hatcher, Algebraic Topology, §3.3, the cup-cap evaluation identity. -/
theorem s4_selected_cap_cup_pairing (T : TopCat.{0}) (p q : ℕ)
    (a : Cohomology ℚ T p) (b : Cohomology ℚ T q) (z : Homology ℚ T (p + q)) :
    cohomologyEquivDualHomology ℚ T q b (s4_selected_singular_cap T p q a z) =
      cohomologyEquivDualHomology ℚ T (p + q) (Singular.cup T rfl a b) z := by
  obtain ⟨φ, rfl⟩ := Singular.cohomologyClass_surjective T p a
  obtain ⟨ψ, rfl⟩ := Singular.cohomologyClass_surjective T q b
  let K := SingularChainComplex ℚ T
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (p + q))).mp inferInstance z
  rw [s4_selected_singular_cap_cocycle, cq_cupCocycle_class]
  have hφ : coboundary ℚ p φ.1 = 0 := φ.2
  change cohomologyEquivDualHomology ℚ T q (Singular.cohomologyClass T q ψ)
    (capHomologyMap ℚ p q φ.1 hφ (K.homologyπ (p + q) c)) = _
  have hc := ConcreteCategory.congr_hom (capHomologyMap_on_cycles ℚ p q φ.1 hφ) c
  change capHomologyMap ℚ p q φ.1 hφ (K.homologyπ (p + q) c) =
    K.homologyπ q ((ShortComplex.cyclesMap (capShortComplexHom ℚ p q φ.1 hφ)).hom c) at hc
  rw [hc, cq_cohomologyClass_pairing_homologyπ, cq_cohomologyClass_pairing_homologyπ]
  change ψ.1 (K.iCycles q
    ((ShortComplex.cyclesMap (capShortComplexHom ℚ p q φ.1 hφ)).hom c)) =
      ψ.1 (cap ℚ p q φ.1 (K.iCycles (p + q) c))
  exact congrArg ψ.1 (ConcreteCategory.congr_hom (capCyclesMap_i ℚ p q φ.1 hφ) c)

#print axioms s4_selected_cap_cup_pairing
end HodgeLean.Foundations.Program
