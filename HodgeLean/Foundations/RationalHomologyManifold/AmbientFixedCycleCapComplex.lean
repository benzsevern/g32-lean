import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapPositiveDifferential
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapZeroDifferential
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetBounded

/-! Literal fixed-cycle cap assembled as a morphism into the bounded supported-chain model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual fixed-cycle cap components assemble into a map of the sheafified ambient cochain complex and the bounded orientation model.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def ambientFixedCycleCapComplexHom (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    ambientCochainSheafComplex X ⟶ capTargetComplex X N :=
  CochainComplex.ofHom (ambientCapTargetComponent X N z) (fun p => by
    by_cases hpN : p < N
    · cases p with
      | zero =>
          cases N with
          | zero => omega
          | succ n => exact (ambientCapTargetComponent_comm_zero X n z hz).symm
      | succ p =>
          exact (ambientCapTargetComponent_comm_positive X N (p + 1) (N - (p + 1) - 1)
            z hz (by omega) (by omega)).symm
    · exact (capTargetComplex_isZero_above X N (p + 1) (by omega)).eq_of_tgt _ _)

#print axioms ambientFixedCycleCapComplexHom
end HodgeLean.Foundations.RationalHomologyManifold
