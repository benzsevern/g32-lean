import HodgeLean.Foundations.Program.G32Native.UnionConormalRingLast

/-! # Exactness of the ideal tensor sequence with explicit ring maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.Program.G32Native

/-- Surjective affine ring coordinates give the exact middle ideal tensor sequence. -/
lemma unionConormalRingLast_exact
    {R B C D : Type} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    (q : R →+* B) (r : R →+* C) (s : C →+* D) (k : B →+* D)
    (hc : s.comp r = k.comp q)
    (hK : (RingHom.ker q).map r = RingHom.ker s)
    (hq : Function.Surjective q) (hr : Function.Surjective r) (hs : Function.Surjective s) :
    Function.Exact
      ((ModuleCat.extendScalars q).map
        (ModuleCat.ofHom (Submodule.inclusion
          (show RingHom.ker q ⊓ RingHom.ker r ≤ RingHom.ker q from inf_le_left))))
      (unionConormalRingLast q r s k hc hK) := by
  letI : Algebra R B := q.toAlgebra
  letI : Algebra R C := r.toAlgebra
  letI : Algebra B D := k.toAlgebra
  letI : Algebra C D := s.toAlgebra
  letI : Algebra R D := (s.comp r).toAlgebra
  letI : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' hc
  exact unionConormalGeneralLast_exact hq hr hs hK

end HodgeLean.Foundations.Program.G32Native
