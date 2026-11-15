import HodgeLean.Foundations.Program.SchoenCycleC1KummerHelpers

/-! # Generic change of covering coordinate in paired Kummer charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- The distinguished covering coordinate satisfies its Kummer equation. -/
theorem s2e_c1_kummer_root_pow {R : Type*} [CommRing R] (m : ℕ) (c : R) :
    AdjoinRoot.root (X ^ m - C c : R[X]) ^ m =
      algebraMap R (AdjoinRoot (X ^ m - C c : R[X])) c := by
  have h := AdjoinRoot.eval₂_root (X ^ m - C c : R[X])
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
    AdjoinRoot.algebraMap_eq] using h

/-- Multiplying a Kummer coordinate by a unit gives an isomorphism of
root algebras and retains that coordinate explicitly. -/
theorem s2e_c1_kummer_scale_equiv {R : Type*} [CommRing R]
    (m : ℕ) (c : R) (x : Rˣ) :
    ∃ E : AdjoinRoot (X ^ m - C ((x : R) ^ m * c) : R[X]) ≃ₐ[R]
        AdjoinRoot (X ^ m - C c : R[X]),
      E (AdjoinRoot.root _) = algebraMap R _ (x : R) * AdjoinRoot.root _ := by
  let f : R[X] := X ^ m - C ((x : R) ^ m * c)
  let g : R[X] := X ^ m - C c
  let F : AdjoinRoot f →ₐ[R] AdjoinRoot g :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (algebraMap R _ (x : R) * AdjoinRoot.root g) (by
      simp only [f, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      change (algebraMap R _ (x : R) * AdjoinRoot.root g) ^ m =
        algebraMap R _ ((x : R) ^ m * c)
      rw [mul_pow, show AdjoinRoot.root g ^ m = algebraMap R _ c from
        s2e_c1_kummer_root_pow m c, map_mul, map_pow])
  let G : AdjoinRoot g →ₐ[R] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId R _) (algebraMap R _ (↑(x⁻¹) : R) * AdjoinRoot.root f) (by
      simp only [g, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      change (algebraMap R _ (↑(x⁻¹) : R) * AdjoinRoot.root f) ^ m =
        algebraMap R _ c
      rw [mul_pow, show AdjoinRoot.root f ^ m = algebraMap R _ ((x : R) ^ m * c) from
        s2e_c1_kummer_root_pow m _]
      rw [map_mul, map_pow, ← mul_assoc, ← mul_pow, ← map_mul]
      simp only [Units.inv_mul, map_one, one_pow, one_mul])
  have hFG : F.comp G = AlgHom.id R _ := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, F, G, AdjoinRoot.liftAlgHom_root, map_mul,
      AlgHom.commutes, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  have hGF : G.comp F = AlgHom.id R _ := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, F, G, AdjoinRoot.liftAlgHom_root, map_mul,
      AlgHom.commutes, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  refine ⟨AlgEquiv.ofAlgHom F G hFG hGF, ?_⟩
  change F (AdjoinRoot.root f) = _
  dsimp only [F]
  rw [AdjoinRoot.liftAlgHom_root]

end HodgeLean.Foundations.Program
