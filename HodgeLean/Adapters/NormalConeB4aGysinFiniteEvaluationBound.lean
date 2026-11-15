import HodgeLean.Adapters.NormalConeB4aGysinFinitePointBound
import HodgeLean.Adapters.NormalConeB4aGysinTensorPoint
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
namespace HodgeLean.Adapters

/-- Every coordinate of a finite algebra has a continuous norm bound
depending only on the restricted complex evaluation of its base. -/
theorem a3b4a_gysin_finite_evaluation_bound
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T] (t : T) :
    ∃ F : C((B →ₐ[ℂ] ℂ), ℝ), ∀ w : T →ₐ[ℂ] ℂ,
      ‖w t‖ ≤ F (w.comp (IsScalarTower.toAlgHom ℂ B T)) := by
  classical
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite B T)
  let b : s → T := Subtype.val
  have hspan : Submodule.span B (Set.range b) = ⊤ := by
    have hr : Set.range b = (s : Set T) := by
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro ht
        exact ⟨⟨t, ht⟩, rfl⟩
    rw [hr]
    exact hs
  have hrepr (i : s) : ∃ a : s → B, ∑ j, a j • b j = t * b i := by
    apply (Submodule.mem_span_range_iff_exists_fun (R := B) (v := b)).mp
    rw [hspan]
    trivial
  choose a ha using hrepr
  let F : C((B →ₐ[ℂ] ℂ), ℝ) := ⟨fun u => ∑ i : s, ∑ j : s, ‖u (a i j)‖, by
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact (AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply B (a i j)).norm⟩
  refine ⟨F, ?_⟩
  intro w
  let u := w.comp (IsScalarTower.toAlgHom ℂ B T)
  letI : Algebra B ℂ := u.toRingHom.toAlgebra
  let W : T →ₗ[B] ℂ :=
    { toFun := w
      map_add' := w.map_add
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
        rfl }
  have hx : (fun i : s => w (b i)) ≠ 0 := by
    intro hz
    have hb : Set.range b ⊆ LinearMap.ker W := by
      rintro _ ⟨i, rfl⟩
      change w (b i) = 0
      exact congrFun hz i
    have htop : (⊤ : Submodule B T) ≤ LinearMap.ker W := by
      rw [← hspan]
      exact Submodule.span_le.mpr hb
    have h1 := htop (show (1 : T) ∈ (⊤ : Submodule B T) from trivial)
    change w 1 = 0 at h1
    exact one_ne_zero ((map_one w).symm.trans h1)
  apply a3b4a_gysin_coordinate_eigenvalue_bound (fun i : s => w (b i)) hx
    (fun i j => u (a i j)) (w t)
  intro i
  calc
    w t * w (b i) = w (t * b i) := (map_mul w _ _).symm
    _ = w (∑ j, a i j • b j) := congrArg w (ha i).symm
    _ = ∑ j, u (a i j) * w (b j) := by
      simp only [map_sum, Algebra.smul_def, map_mul]
      rfl

end HodgeLean.Adapters
