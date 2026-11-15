import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.BigOperators.Pi

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Sum-zero invariance identifies all coordinate operators on a vector. -/
theorem s4_equal_coordinate_operators {K V I A : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    [AddCommGroup A] (oneA : A)
    (ρ : Multiplicative (I → A) →* Module.End K V) (z : V)
    (hz : ∀ v : I → A, (∑ i, v i) = 0 → ρ (.ofAdd v) z = z) (i j : I) :
    ρ (.ofAdd (Pi.single i oneA)) z = ρ (.ofAdd (Pi.single j oneA)) z := by
  let d : I → A := Pi.single i oneA - Pi.single j oneA
  have hd : (∑ k, d k) = 0 := by
    simp only [d, Pi.sub_apply, Finset.sum_sub_distrib]
    simp
  have ht : Multiplicative.ofAdd (Pi.single i oneA) =
      Multiplicative.ofAdd (Pi.single j oneA) * Multiplicative.ofAdd d := by
    change Pi.single i oneA = Pi.single j oneA + d
    dsimp only [d]
    abel
  rw [ht, map_mul, Module.End.mul_apply, hz d hd]

/-- An eigenvalue at one coordinate is the eigenvalue at every coordinate on a sum-zero fixed vector. -/
theorem s4_equal_coordinate_eigenvalues {K V I A : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    [AddCommGroup A] (oneA : A)
    (ρ : Multiplicative (I → A) →* Module.End K V) (z : V)
    (hz : ∀ v : I → A, (∑ i, v i) = 0 → ρ (.ofAdd v) z = z)
    (j : I) (c : K) (hj : ρ (.ofAdd (Pi.single j oneA)) z = c • z) (i : I) :
    ρ (.ofAdd (Pi.single i oneA)) z = c • z :=
  (s4_equal_coordinate_operators oneA ρ z hz i j).trans hj

end HodgeLean.Foundations.Program
