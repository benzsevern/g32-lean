import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program

variable {K V W : Type*} [CommRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem g32c_decompose_map_coe (f : V →ₗ[K] W) (n : ℕ) (x : ExteriorAlgebra K V) :
    (DirectSum.decompose (fun i : ℕ => ⋀[K]^i W) (ExteriorAlgebra.map f x) n : ExteriorAlgebra K W) =
      ExteriorAlgebra.map f (DirectSum.decompose (fun i : ℕ => ⋀[K]^i V) x n : ExteriorAlgebra K V) := by
  induction x using DirectSum.Decomposition.inductionOn (fun i : ℕ => ⋀[K]^i V) with
  | zero =>
      simp only [map_zero, DirectSum.decompose_zero, DFinsupp.zero_apply, ZeroMemClass.coe_zero]
  | add x y hx hy =>
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hx, hy]
  | @homogeneous i x =>
      have hcoe := LinearMap.congr_fun (exteriorPower.subtype_comp_map_eq (n := i) f) x
      have hmap : ExteriorAlgebra.map f x ∈ ⋀[K]^i W :=
        hcoe ▸ (exteriorPower.map i f x).property
      by_cases hi : i = n
      · subst n
        rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i W) hmap, DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i V) x.property]
      · rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i W) hmap hi, DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i V) x.property hi,
          map_zero]

theorem g32c_decompose_map (f : V →ₗ[K] W) (n : ℕ) (x : ExteriorAlgebra K V) :
    DirectSum.decompose (fun i : ℕ => ⋀[K]^i W) (ExteriorAlgebra.map f x) n =
      exteriorPower.map n f (DirectSum.decompose (fun i : ℕ => ⋀[K]^i V) x n) := by
  apply Subtype.ext
  rw [g32c_decompose_map_coe]
  exact (LinearMap.congr_fun (exteriorPower.subtype_comp_map_eq (n := n) f) _).symm

end HodgeLean.Foundations.Program
