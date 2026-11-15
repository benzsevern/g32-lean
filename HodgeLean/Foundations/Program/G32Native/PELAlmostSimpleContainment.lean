import HodgeLean.Foundations.Program.G32Native.PELNormalLieAssembly
import HodgeLean.Foundations.Program.G32Native.PELConnectedNormalIntersection

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- For a matrix group with simple tangent Lie algebra, normalization by the
identity component and a noncentral intersection witness force containment
of that component.
Source: Milne, Algebraic Groups (2017), Chapter 21 and Proposition 24.1;
Borel, Linear Algebraic Groups, second edition, §§1.2, 3.5, 7.1. -/
theorem pel_almost_simple_identityComponent_containment (G : MatrixAlgGroup k n)
    [LieAlgebra.IsSimple k (pelMatrixTangentLie G)]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hclosed : @IsClosed _ (g1_zariski k n) (H : Set (Matrix.GeneralLinearGroup (Fin n) k)))
    (hnormal : ∀ g ∈ g1_identityComponent G, ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : Matrix.GeneralLinearGroup (Fin n) k) (hx : x ∈ H)
    (hxG : x ∈ g1_identityComponent G)
    (hnoncentral : ∃ g ∈ g1_identityComponent G, ¬ Commute x g) :
    g1_identityComponent G ⊆ (H : Set (Matrix.GeneralLinearGroup (Fin n) k)) := by
  letI := g1_zariski k n
  obtain ⟨C, hC⟩ := g1_exists_identityComponent G
  have hLie : g1_lieAlgebra C = g1_lieAlgebra G :=
    (congrArg g1_lieOfSet hC).trans (g1_lie_identityComponent G)
  have hLieC : pelMatrixTangentLie C = pelMatrixTangentLie G := by
    apply LieSubalgebra.toSubmodule_injective
    exact hLie
  have hsimpleC : LieAlgebra.IsSimple k (pelMatrixTangentLie C) := by
    rw [hLieC]
    infer_instance
  letI := hsimpleC
  obtain ⟨eqs, heqs⟩ := (@g1_isClosed_iff k _ n (H : Set _) ).mp hclosed
  let A : MatrixAlgGroup k n := g1_ofEquations eqs H (by
    intro g
    change g ∈ (H : Set _) ↔ _
    rw [heqs]
    rfl)
  have hA : A.carrier = H := rfl
  have hnC : ∀ g ∈ C.carrier, ∀ z ∈ A.carrier, g⁻¹ * z * g ∈ A.carrier := by
    intro g hg z hz
    exact hnormal g (hC ▸ hg) z hz
  have hi := pel_identityComponent_normal_intersection_infinite G H hnormal x hx hxG hnoncentral
  have hI : (g1_inter C A).carrier = H ⊓ g1_identityComponentSubgroup G := by
    ext g
    change (g ∈ C.carrier ∧ g ∈ H) ↔ (g ∈ H ∧ g ∈ g1_identityComponent G)
    have hc : g ∈ C.carrier ↔ g ∈ g1_identityComponent G := by rw [← hC]; rfl
    rw [hc, and_comm]
  have hiC : ((g1_inter C A).carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)).Infinite := by
    rw [hI]
    exact hi
  have hcontain := pel_normal_contains_of_simple_tangent C A hnC hiC
  have hconn : @IsConnected _ (g1_zariski k n) (C.carrier : Set _) := by
    rw [hC]
    exact (@isConnected_connectedComponentIn_iff _ (g1_zariski k n) _ _).mpr G.carrier.one_mem
  have hCC : g1_identityComponent C = (C.carrier : Set _) := by
    apply Set.Subset.antisymm (@connectedComponentIn_subset _ (g1_zariski k n) _ _)
    exact hconn.isPreconnected.subset_connectedComponentIn C.carrier.one_mem Set.Subset.rfl
  rw [hCC, hC] at hcontain
  exact hcontain

#print axioms pel_almost_simple_identityComponent_containment
end HodgeLean.Foundations.Program.GeneralTypeIII
