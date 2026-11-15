import HodgeLean.Foundations.Program.SchoenInvariantFiniteType
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.FiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A ring action preserving graded pieces commutes with homogeneous decomposition. -/
theorem s2_smul_decompose {A : Type} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (G : Type) [Group G] [MulSemiringAction G A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    (g : G) (a : A) (n : ℕ) :
    g • (DirectSum.decompose 𝒜 a n : A) = (DirectSum.decompose 𝒜 (g • a) n : A) := by
  let f : 𝒜 →+*ᵍ 𝒜 :=
    { MulSemiringAction.toRingHom G A g with map_mem := fun {n} {a} ha => hgrade g n a ha }
  exact f.map_directSumDecompose

/-- Every homogeneous component of a fixed element is fixed for a grading-preserving action. -/
theorem s2_fixedRing_decompose_mem {A : Type} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (G : Type) [Group G] [MulSemiringAction G A]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    {a : A} (ha : a ∈ FixedPoints.subring A G) (n : ℕ) :
    (DirectSum.decompose 𝒜 a n : A) ∈ FixedPoints.subring A G := by
  intro g
  rw [s2_smul_decompose 𝒜 G hgrade, ha g]

end HodgeLean.Foundations.Program
