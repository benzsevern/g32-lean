import HodgeLean.Foundations.Representation.OrderedKunnethDefs
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! Finite Fourier projectors and the actual sum-zero fixed submodule.
HC no distance; AV milestone no distance. -/
noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.OrderedKunneth.StageTwo

/-- The finite Fourier averaging operator, with inverse character in the coefficient.
Source: Serre, Linear Representations of Finite Groups, §2.6, character projectors. -/
def fourierProjector {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (m : ℕ) (ζ : K) (A : Module.End K V) (a : Fin m) : Module.End K V :=
  (m : K)⁻¹ • ∑ j : Fin m, ((ζ ^ j.val)⁻¹ ^ a.val) • A ^ j.val

example : fourierProjector 2 (-1 : ℚ) (-(LinearMap.id : Module.End ℚ ℚ)) 1 3 = 3 := by
  norm_num [fourierProjector, Fin.sum_univ_two]

/-- Coordinate generator operators of the actual finite product-group representation.
Source: Serre, Linear Representations of Finite Groups, §1.2. -/
def coordinateOperators {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [DecidableEq I] (m : ℕ)
    (ρ : Representation K (Multiplicative (I → ZMod m)) V) : I → Module.End K V :=
  fun i => ρ (Multiplicative.ofAdd (Pi.single i 1))

example : coordinateOperators 2
    (1 : Representation ℚ (Multiplicative (Fin 1 → ZMod 2)) ℚ) 0 3 = 3 := rfl

/-- Fixed vectors for all actual sum-zero group elements, as an intersection of kernels.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2. -/
def sumZeroFixed {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (m : ℕ)
    (ρ : Representation K (Multiplicative (I → ZMod m)) V) : Submodule K V :=
  ⨅ v : {v : I → ZMod m // ∑ i, v i = 0},
    LinearMap.ker (ρ (Multiplicative.ofAdd v.val) - LinearMap.id)

example : (3 : ℚ) ∈ sumZeroFixed 6
    (1 : Representation ℚ (Multiplicative (Fin 2 → ZMod 6)) ℚ) := by
  simp [sumZeroFixed]

end HodgeLean.Foundations.OrderedKunneth.StageTwo
