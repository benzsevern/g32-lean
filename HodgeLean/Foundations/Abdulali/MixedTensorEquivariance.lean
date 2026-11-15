import HodgeLean.Foundations.Abdulali.MixedTensorRetraction

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The original-copy inclusion intertwines every endomorphism. -/
theorem mixedCopiesIn_action (r : ℕ) (u : Module.End ℂ V) (x : Fin r → V) :
    m1b_copies (r + 1) u (mixedCopiesIn r x) = mixedCopiesIn r (m1b_copies r u x) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact map_zero u
  · rfl

/-- The distinguished-copy inclusion intertwines every endomorphism. -/
theorem mixedExtraIn_action (r : ℕ) (u : Module.End ℂ V) (x : V) :
    m1b_copies (r + 1) u (mixedExtraIn r x) = mixedExtraIn r (u x) := by
  classical
  ext i
  change u ((Pi.single 0 x : Fin (r + 1) → V) i) =
    (Pi.single 0 (u x) : Fin (r + 1) → V) i
  simp only [Pi.single_apply]
  split_ifs <;> simp only [map_zero]

/-- The mixed embedding intertwines the two tensor blocks and the enlarged action. -/
theorem mixedTensorIn_action (r n d : ℕ) (u : Module.End ℂ V)
    (z : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V)) :
    SchurWeyl.tensorPow (Fin (n + d)) (m1b_copies (r + 1) u)
      (mixedTensorIn r n d z) =
    mixedTensorIn r n d (TensorProduct.map
      (SchurWeyl.tensorPow (Fin n) (m1b_copies r u))
      (SchurWeyl.tensorPow (Fin d) u) z) := by
  have hc : (SchurWeyl.tensorPow (Fin (n + d)) (m1b_copies (r + 1) u)).comp
      (mixedTensorIn r n d) =
    (mixedTensorIn r n d).comp (TensorProduct.map
      (SchurWeyl.tensorPow (Fin n) (m1b_copies r u))
      (SchurWeyl.tensorPow (Fin d) u)) := by
    ext x y
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply, mixedTensorIn, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.map_tmul, PiTensorProduct.map_tprod,
      SchurWeyl.tensorPow_tprod, m1b_tensorPow_append,
      mixedCopiesIn_action, mixedExtraIn_action]
  exact LinearMap.congr_fun hc z

/-- Full orthogonal fixed mixed tensors embed into quadratic products on extra copies. -/
theorem mixedTensorIn_mem_products [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r n d : ℕ)
    (z : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^d V))
    (hz : z ∈ ⨅ g : orthogonalUnits B,
      LinearMap.ker (TensorProduct.map (orthogonalTensorRepresentation B r n g)
        (orthogonalBaseTensorRepresentation B d g) - LinearMap.id)) :
    mixedTensorIn r n d z ∈
      m1b_products (m1b_fixed (m1b_copies (r + 1) '' m1b_isometries B) 2) (n + d) := by
  rw [← m1b_orthogonal_tensors_aux V B hB hs]
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rintro _ ⟨u, ⟨⟨g, rfl⟩, hu⟩, rfl⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hz
  rw [mixedTensorIn_action]
  exact congrArg (mixedTensorIn r n d) (hz ⟨g, hu⟩)

end HodgeLean.Foundations.Abdulali
