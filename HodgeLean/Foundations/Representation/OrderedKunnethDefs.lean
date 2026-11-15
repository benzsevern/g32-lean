import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Data.ZMod.Basic

/-! First-stage character and binary product interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
open scoped BigOperators TensorProduct DirectSum
namespace HodgeLean.Foundations.OrderedKunneth

/-- Evaluation of a finite additive weight on a tuple.
Source: Schoen (1988), Hodge classes on self-products of a variety with an automorphism, Lemmas 1.1–1.2, pp. 5–6. -/
def weightPairing {I : Type*} [Fintype I] (m : ℕ) (a v : I → ZMod m) : ZMod m :=
  ∑ i, a i * v i

example : weightPairing 6 (fun _ : Fin 2 => 1) (fun i => if i = 0 then 1 else -1) = 0 := by
  norm_num [weightPairing, Fin.sum_univ_two]

/-- The simultaneous eigenspace for a family of operators and specified eigenvalues.
Source: Mathlib, LinearAlgebra/Eigenspace/Basic.lean, Module.End.mem_eigenspace_iff; Submodule.mem_iInf. -/
def characterSummand {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (χ : I → K) : Submodule K V :=
  ⨅ i, Module.End.eigenspace (A i) (χ i)

example : (1 : ℚ) ∈ characterSummand (fun _ : Fin 2 => -(LinearMap.id : Module.End ℚ ℚ)) (fun _ => -1) := by
  simp [characterSummand]

end HodgeLean.Foundations.OrderedKunneth
