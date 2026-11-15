import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An anticommuting operator exchanges opposite eigenspaces. -/
theorem anticommute_eigenspace (I J : Module.End K V)
    (hIJ : I.comp J = -(J.comp I)) (w : K) {x : V}
    (hx : x ∈ Module.End.eigenspace I w) :
    J x ∈ Module.End.eigenspace I (-w) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have h := LinearMap.congr_fun hIJ x
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, hx, map_smul, neg_smul] using h

/-- A nonzero scalar square makes the opposite-eigenspace exchange invertible. -/
def eigenSwap (I J : Module.End K V) (hIJ : I.comp J = -(J.comp I))
    (c : K) (hc : c ≠ 0) (hJ : J.comp J = c • LinearMap.id) (w : K) :
    Module.End.eigenspace I w ≃ₗ[K] Module.End.eigenspace I (-w) where
  toFun x := ⟨J x, anticommute_eigenspace I J hIJ w x.property⟩
  invFun y := ⟨c⁻¹ • J y, by
    apply Submodule.smul_mem
    simpa only [neg_neg] using anticommute_eigenspace I J hIJ (-w) y.property⟩
  map_add' x y := Subtype.ext (map_add J (x : V) (y : V))
  map_smul' a x := Subtype.ext (map_smul J a (x : V))
  left_inv x := by
    apply Subtype.ext
    have h := LinearMap.congr_fun hJ (x : V)
    change c⁻¹ • J (J x) = x
    change J (J (x : V)) = c • (x : V) at h
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv y := by
    apply Subtype.ext
    have h := LinearMap.congr_fun hJ (y : V)
    change J (c⁻¹ • J y) = y
    change J (J (y : V)) = c • (y : V) at h
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The eigenspace equivalence retains the original swapping operator pointwise. -/
theorem eigenSwap_apply (I J : Module.End K V) (hIJ : I.comp J = -(J.comp I))
    (c : K) (hc : c ≠ 0) (hJ : J.comp J = c • LinearMap.id) (w : K)
    (x : Module.End.eigenspace I w) :
    (eigenSwap I J hIJ c hc hJ w x : V) = J x := rfl

#print axioms eigenSwap
end HodgeLean.Foundations.Program.QuaternionGraph
