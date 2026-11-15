import HodgeLean.Foundations.Program.SchoenCycleFixedActionBaseMap

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual invariant subalgebra with its original scalar structure retains both quotient-base scalar towers under the canonical base map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_fixed_function_scalar_towers
    (k A C G : Type*) [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C] [SMulCommClass G A C] :
    let S := FixedPoints.subalgebra k C G
    let f := s2e_fixed_action_base_map k A C G
    letI : Algebra A S := f.toRingHom.toAlgebra
    IsScalarTower k A S ∧ IsScalarTower A S C := by
  let S := FixedPoints.subalgebra k C G
  let f := s2e_fixed_action_base_map k A C G
  letI : Algebra A S := f.toRingHom.toAlgebra
  constructor
  · exact IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  · exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

#print axioms s2e_fixed_function_scalar_towers
end HodgeLean.Foundations.Program
