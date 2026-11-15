import HodgeLean.Foundations.Program.G32ContractionScalar
import HodgeLean.Foundations.Program.G32ContractionGrading

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct

namespace HodgeLean.Foundations.Program

theorem g32c_baseChange_retract_span {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (f : V →ₗ[ℚ] W) (g : W →ₗ[ℚ] V) (P : Submodule ℚ V) (Q : Submodule ℚ W)
    (a : ℚ) (ha : a ≠ 0) (hgf : g ∘ₗ f = a • LinearMap.id)
    (hg : ∀ w ∈ Q, g w ∈ P) (x : ℂ ⊗[ℚ] V)
    (hx : f.baseChange ℂ x ∈ Q.baseChange ℂ) : x ∈ P.baseChange ℂ := by
  have hb := g32c_baseChange_map_mem g Q P hg _ hx
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hgf, LinearMap.baseChange_smul,
    LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply] at hb
  rw [← algebraMap_smul ℂ a] at hb
  exact (Submodule.smul_mem_iff (p := P.baseChange ℂ) (Rat.cast_ne_zero.mpr ha)).mp hb

theorem g32c_exterior_invariant_degree {K V W : Type*} [CommRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (u : Module.End K W) (v : Module.End K V)
    (h : u ∘ₗ f = f ∘ₗ v) (n : ℕ) (x : ExteriorAlgebra K V)
    (hx : ExteriorAlgebra.map v x = x) :
    exteriorPower.map n u (exteriorPower.map n f
      (DirectSum.decompose (fun i : ℕ => ⋀[K]^i V) x n)) =
      exteriorPower.map n f (DirectSum.decompose (fun i : ℕ => ⋀[K]^i V) x n) := by
  have hd := congrArg (fun z => DirectSum.decompose (fun i : ℕ => ⋀[K]^i V) z n) hx
  rw [g32c_decompose_map] at hd
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, h, exteriorPower.map_comp,
    LinearMap.comp_apply, hd]

end HodgeLean.Foundations.Program
