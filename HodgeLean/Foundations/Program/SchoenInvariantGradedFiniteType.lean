import HodgeLean.Foundations.Program.SchoenFixedDegreeZeroEquiv
import HodgeLean.Foundations.Program.SchoenInvariantFiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-group invariants have finite type over their actual degree zero when the ambient degree zero is fixed. -/
theorem s2_fixedGradedRing_finiteType {A G : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [IsNoetherianRing (𝒜 0)]
    [Algebra.FiniteType (𝒜 0) A] [Group G] [Finite G] [MulSemiringAction G A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (hzero : ∀ g : G, ∀ a ∈ 𝒜 0, g • a = a) :
    letI := s2_fixedRingGrading 𝒜 G hgrade
    Algebra.FiniteType (s2_subringGradedPiece 𝒜 (FixedPoints.subring A G) 0)
      (FixedPoints.subring A G) := by
  letI := s2_fixedRingGrading 𝒜 G hgrade
  letI : SMulCommClass G (𝒜 0) A := ⟨fun g c a => by
    change g • ((c : A) * a) = (c : A) * (g • a)
    rw [smul_mul', hzero g c.val c.property]⟩
  have hi := s2_fixedAlgebra_finiteType (𝒜 0) A G
  let ℬ := s2_subringGradedPiece 𝒜 (FixedPoints.subring A G)
  have ht : ((algebraMap (ℬ 0) (FixedPoints.subring A G)).comp
      (s2_fixedDegreeZeroEquiv 𝒜 hgrade hzero).toRingHom).FiniteType := by
    change (algebraMap (𝒜 0) (FixedPoints.subalgebra (𝒜 0) A G)).FiniteType
    exact hi
  exact RingHom.FiniteType.of_comp_finiteType ht

end HodgeLean.Foundations.Program
