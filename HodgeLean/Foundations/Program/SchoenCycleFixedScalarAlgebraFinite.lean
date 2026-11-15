import HodgeLean.Foundations.Program.SchoenCycleFixedActionBaseMap
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Fixed functions over the prescribed smaller scalar ring remain finite over the actual Noetherian quotient base through its canonical fixed-function map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 7. -/
theorem s2e_fixed_scalar_algebra_module_finite
    (k A C G : Type*) [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    [IsNoetherianRing A] [Module.Finite A C]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C] [SMulCommClass G A C] :
    let S := FixedPoints.subalgebra k C G
    letI : Algebra A S := (s2e_fixed_action_base_map k A C G).toAlgebra
    Module.Finite A S := by
  dsimp only
  let S := FixedPoints.subalgebra k C G
  letI : Algebra A S := (s2e_fixed_action_base_map k A C G).toAlgebra
  let j : S →ₗ[A] C :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun a c => by
        change algebraMap A C a * c.val = a • c.val
        exact (Algebra.smul_def a c.val).symm }
  exact Module.Finite.of_injective j Subtype.val_injective

#print axioms s2e_fixed_scalar_algebra_module_finite
end HodgeLean.Foundations.Program
