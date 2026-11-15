import HodgeLean.Foundations.RationalHomologyManifold.KernelCapZeroHomotopy
import Mathlib.Algebra.Homology.Homotopy

/-! The actual kernel null homotopy of the bounded fixed-cycle cap map.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The checked prism identities give the kernel homotopy equation in every positive degree, including the zero upper tail.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
theorem kernelCapTargetPrismComponent_succ (X : TopCat.{0}) [RegularSpace X] (N p : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    (ambientLocalZeroSheafInclusion X).f (p + 1) ≫ ambientCapTargetComponent X N z (p + 1) =
      (ambientLocalZeroSheafComplex X).d (p + 1) (p + 2) ≫ kernelCapTargetPrismComponent X N z (p + 1) +
        kernelCapTargetPrismComponent X N z p ≫ (capTargetComplex X N).d p (p + 1) := by
  by_cases hN : p + 1 ≤ N
  · cases p with
    | zero =>
        cases N with
        | zero => omega
        | succ q => exact kernelCapTargetPrismComponent_first X q z hz
    | succ p =>
        exact kernelCapTargetPrismComponent_interior X N (p + 1) (N - (p + 1 + 1))
          z hz (by omega) (by omega)
  · exact (capTargetComplex_isZero_above X N (p + 1) (by omega)).eq_of_tgt _ _

#print axioms kernelCapTargetPrismComponent_succ
/-- The literal stabilized prism caps form a null homotopy of the actual ambient fixed-cycle cap restricted to the local zero-cochain kernel.
Source: Bredon, Sheaf Theory, second edition, VI.12; Hatcher, Algebraic Topology, sections 2.1 and 3.3.
HC no distance; AV milestone no distance.
-/
def kernelFixedCycleCapNullHomotopy (X : TopCat.{0}) [RegularSpace X] (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) :
    Homotopy (ambientLocalZeroSheafInclusion X ≫ ambientFixedCycleCapComplexHom X N z hz) 0 := by
  classical
  let h (i j : ℕ) : (ambientLocalZeroSheafComplex X).X i ⟶ (capTargetComplex X N).X j :=
    if hij : i = j + 1 then eqToHom (congrArg _ hij) ≫ kernelCapTargetPrismComponent X N z j else 0
  have hh (j : ℕ) : h (j + 1) j = kernelCapTargetPrismComponent X N z j := by
    simp only [h, dif_pos rfl, eqToHom_refl, Category.id_comp]
  refine ⟨h, ?_, ?_⟩
  · intro i j hij
    dsimp [h]
    rw [dif_neg (by intro he; exact hij he.symm)]
  · intro i
    rw [Homotopy.dNext_cochainComplex, hh, HomologicalComplex.zero_f_apply, add_zero]
    change (ambientLocalZeroSheafInclusion X).f i ≫ ambientCapTargetComponent X N z i = _
    cases i with
    | zero =>
        rw [Homotopy.prevD_zero_cochainComplex, add_zero]
        exact kernelCapTargetPrismComponent_initial X N z hz
    | succ p =>
        rw [Homotopy.prevD_succ_cochainComplex, hh]
        exact kernelCapTargetPrismComponent_succ X N p z hz

#print axioms kernelFixedCycleCapNullHomotopy
end HodgeLean.Foundations.RationalHomologyManifold
