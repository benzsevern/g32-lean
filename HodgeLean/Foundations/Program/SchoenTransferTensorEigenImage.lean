import HodgeLean.Foundations.Program.SchoenTransferTensorEigenSupport
import HodgeLean.Foundations.Program.SchoenTransferTensorSubspaceLift

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Tensors of eigenvectors have the same eigenvalue at each tensor coordinate. -/
theorem s4_tensor_eigen_image {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (n : ℕ) (A : Module.End K V) (r : K)
    {z : ⨂[K] i : Fin n, V}
    (hz : z ∈ LinearMap.range (PiTensorProduct.map
      (fun _ : Fin n => (Module.End.eigenspace A r).subtype))) (i : Fin n) :
    s4_tensorCoordinate A i z = r • z := by
  classical
  have he : (s4_tensorCoordinate A i).comp (PiTensorProduct.map
      (fun _ : Fin n => (Module.End.eigenspace A r).subtype)) =
      r • PiTensorProduct.map (fun _ : Fin n => (Module.End.eigenspace A r).subtype) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, s4_tensorCoordinate, PiTensorProduct.map_tprod]
    change PiTensorProduct.tprod K
      (fun j => Function.update (fun _ : Fin n => (LinearMap.id : Module.End K V)) i A j (v j : V)) =
        r • PiTensorProduct.tprod K (fun j => (v j : V))
    have hf : (fun j => Function.update (fun _ : Fin n => (LinearMap.id : Module.End K V)) i A j
        ((v j : Module.End.eigenspace A r) : V)) =
        Function.update (fun j => (v j : V)) i (r • (v i : V)) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, Module.End.mem_eigenspace_iff.mp (v i).property]
      · simp only [Function.update_of_ne hj, LinearMap.id_apply]
    rw [hf, (PiTensorProduct.tprod K).map_update_smul, Function.update_eq_self]
  obtain ⟨w, rfl⟩ := hz
  exact LinearMap.congr_fun he w

/-- Exterior tensors in an eigenspace retain that eigenvalue at every coordinate. -/
theorem s4_exterior_tensor_eigen {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (n : ℕ) (A : Module.End K V) (r : K)
    (w : ⋀[K]^n (Module.End.eigenspace A r)) (i : Fin n) :
    s4_tensorCoordinate A i
      (exteriorPower.toTensorPower K V n
        (exteriorPower.map n (Module.End.eigenspace A r).subtype w)) =
      r • exteriorPower.toTensorPower K V n
        (exteriorPower.map n (Module.End.eigenspace A r).subtype w) := by
  apply s4_tensor_eigen_image n A r (i := i)
  refine ⟨exteriorPower.toTensorPower K (Module.End.eigenspace A r) n w, ?_⟩
  exact LinearMap.congr_fun (s4_tensorAlternation_map n (Module.End.eigenspace A r).subtype) w

end HodgeLean.Foundations.Program
