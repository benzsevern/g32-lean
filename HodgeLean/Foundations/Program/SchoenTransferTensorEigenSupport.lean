import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section
open scoped TensorProduct BigOperators
namespace HodgeLean.Foundations.Program

/-- A diagonal operator scales each coordinate of a vector by its diagonal entry. -/
theorem s4_diagonal_basis_coordinate {K V B : Type*} [Field K]
    [AddCommGroup V] [Module K V] (b : Module.Basis B K V)
    (F : Module.End K V) (c : B → K) (hF : ∀ i, F (b i) = c i • b i) (z : V) (i : B) :
    b.repr (F z) i = c i * b.repr z i := by
  classical
  have he : (b.coord i).comp F = c i • b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, hF, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hj : j = i
    · subst j; simp only [ite_true, smul_eq_mul]
    · simp only [hj, ite_false, smul_zero]
  exact LinearMap.congr_fun he z

/-- The operator acting at one tensor coordinate. -/
def s4_tensorCoordinate {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq I] (A : Module.End K V) (i : I) :
    Module.End K (⨂[K] j : I, V) :=
  PiTensorProduct.map (Function.update (fun _ : I => LinearMap.id) i A)

/-- A tensor basis diagonalizes every coordinate operator simultaneously. -/
theorem s4_tensorCoordinate_basis {K V I B : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I]
    (b : Module.Basis B K V) (A : Module.End K V) (c : B → K)
    (hA : ∀ j, A (b j) = c j • b j) (i : I) (p : I → B) :
    s4_tensorCoordinate A i ((Basis.piTensorProduct (fun _ : I => b)) p) =
      c (p i) • (Basis.piTensorProduct (fun _ : I => b)) p := by
  classical
  simp only [s4_tensorCoordinate, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
  have he : (fun j => Function.update (fun _ : I => (LinearMap.id : Module.End K V)) i A j
      (b (p j))) = Function.update (fun j => b (p j)) i (c (p i) • b (p i)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp only [Function.update_self, hA]
    · simp only [Function.update_of_ne hj, LinearMap.id_apply]
  rw [he, (PiTensorProduct.tprod K).map_update_smul]
  rw [Function.update_eq_self]

/-- Equal coordinate eigenvalues force tensor support inside the corresponding eigenspace. -/
theorem s4_tensor_eigen_support {K V I B : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype I] [DecidableEq I] [Fintype B]
    (b : Module.Basis B K V) (A : Module.End K V) (c : B → K)
    (hA : ∀ j, A (b j) = c j • b j) (μ : K)
    (z : ⨂[K] i : I, V) (hz : ∀ i, s4_tensorCoordinate A i z = μ • z) :
    z ∈ LinearMap.range (PiTensorProduct.map (fun _ : I => (Module.End.eigenspace A μ).subtype)) := by
  classical
  let T := Basis.piTensorProduct (fun _ : I => b)
  rw [PiTensorProduct.map_range_eq_span_tprod]
  rw [← T.sum_repr z]
  apply Submodule.sum_mem
  intro p hp
  by_cases hc : T.repr z p = 0
  · rw [hc, zero_smul]; exact Submodule.zero_mem _
  · have he (i : I) : c (p i) = μ := by
      have hcoord := s4_diagonal_basis_coordinate T (s4_tensorCoordinate A i)
        (fun q => c (q i)) (s4_tensorCoordinate_basis b A c hA i) z p
      rw [hz i, map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
      exact (mul_right_cancel₀ hc hcoord.symm)
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨fun i => ⟨b (p i), Module.End.mem_eigenspace_iff.mpr ?_⟩, ?_⟩
    · rw [hA, he]
    · exact (Basis.piTensorProduct_apply (fun _ : I => b) p).symm

end HodgeLean.Foundations.Program
