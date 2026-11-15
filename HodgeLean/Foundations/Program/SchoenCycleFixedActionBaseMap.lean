import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Algebra.Tower

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Scalar functions on the actual quotient chart map into the actual fixed-function algebra of a compatible action.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
def s2e_fixed_action_base_map
    (k A C G : Type*) [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [Algebra A C] [IsScalarTower k A C]
    [Group G] [MulSemiringAction G C] [SMulCommClass G k C] [SMulCommClass G A C] :
    A →ₐ[k] FixedPoints.subalgebra k C G :=
  (IsScalarTower.toAlgHom k A C).codRestrict (FixedPoints.subalgebra k C G)
    (fun a g => smul_algebraMap g a)

#print axioms s2e_fixed_action_base_map
end HodgeLean.Foundations.Program
