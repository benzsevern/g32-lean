import HodgeLean.Foundations.Program.SchoenTransferR2SupportCup
import HodgeLean.Adapters.DegreeOneLatticeLoops

/-! # Cup annihilation through an actual neighbourhood deformation

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A neighbourhood homotopy factoring through the component turns restriction
vanishing into annihilation by every class supported on the component.
Source: Hatcher, Algebraic Topology, §3.2, relative cup and homotopy invariance.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_neighbourhood_cup_eq_zero
    (X Q : TopCat.{0}) (j : Q ⟶ X) (S : Closeds X) (U : Opens X)
    (hSU : (S : Set X) ⊆ U)
    (r : TopCat.of (U : Set X) ⟶ Q)
    (H : TopCat.Homotopy
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U : Set X), X))) (r ≫ j))
    (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (S : Set X)ᶜ) p)
    (u : Cohomology ℚ X q) (hu : cohomologyMap ℚ q j u = 0) :
    HodgeLean.Foundations.Singular.cup X rfl
      (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (S : Set X)ᶜ) p a) u = 0 := by
  apply s4_assembly_support_cup_eq_zero X S U hSU p q a u
  change cohomologyMap ℚ q
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U : Set X), X))) u = 0
  rw [cohomologyMap_eq_of_homotopy H q, cohomologyMap_comp, LinearMap.comp_apply,
    hu, map_zero]

#print axioms s4_assembly_neighbourhood_cup_eq_zero
end HodgeLean.Foundations.Program
