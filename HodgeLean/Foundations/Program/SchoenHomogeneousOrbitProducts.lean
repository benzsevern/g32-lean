import HodgeLean.Foundations.Program.SchoenGradedInvariants
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The product of all finite-group translates of a ring element is invariant. -/
theorem s2_orbitProduct_fixed {A G : Type} [CommRing A] [Group G] [Fintype G]
    [MulSemiringAction G A] (a : A) :
    (∏ g : G, g • a) ∈ FixedPoints.subring A G := by
  intro g
  exact Finset.smul_prod_perm a g

/-- Orbit products of degree-n elements have degree equal to the group order times n. -/
theorem s2_orbitProduct_homogeneous {A G : Type} [CommRing A] [Group G] [Fintype G]
    [MulSemiringAction G A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgrade : ∀ g : G, ∀ n, ∀ a ∈ 𝒜 n, g • a ∈ 𝒜 n)
    {a : A} {n : ℕ} (ha : a ∈ 𝒜 n) :
    (∏ g : G, g • a) ∈ 𝒜 (Fintype.card G * n) := by
  have h := SetLike.prod_mem_graded 𝒜 (fun _ : G => n) (fun g : G => g • a)
    (F := Finset.univ) (fun g _ => hgrade g n a ha)
  simpa using h

/-- A finite orbit product avoids a prime if each of its translated factors does. -/
theorem s2_orbitProduct_notMem_prime {A G : Type} [CommRing A] [Group G] [Fintype G]
    [MulSemiringAction G A] (P : Ideal A) [P.IsPrime] (a : A)
    (ha : ∀ g : G, g • a ∉ P) : (∏ g : G, g • a) ∉ P := by
  exact P.primeCompl.prod_mem (fun g _ => ha g)

end HodgeLean.Foundations.Program
