import HodgeLean.Foundations.Program.SchoenCycleC1FunctionFieldActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1LocalFieldActionHelpers

/-! # Algebra automorphisms of the actual fixed stalk and generic field -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The actual transported stalk pullback of an automorphism fixing a point
is an equivalence over the prescribed complex scalars. -/
theorem s2e_c1_fixed_point_stalk_algEquiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (f : X ⟶ X) [IsIso f.left]
    (p : X.left) (hp : f.left p = p) :
    letI : Algebra ℂ (X.left.presheaf.stalk p) :=
      (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    ∃ τ : X.left.presheaf.stalk p ≃ₐ[ℂ] X.left.presheaf.stalk p,
      τ.toRingHom = s2e_fixed_point_stalkPullback X.left f.left p hp := by
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  let α : X.left.presheaf.stalk p →ₐ[ℂ] X.left.presheaf.stalk p :=
    { toRingHom := s2e_fixed_point_stalkPullback X.left f.left p hp
      commutes' := s2e_fixed_point_stalkPullback_scalars X f p hp }
  have hbij : Function.Bijective α := by
    change Function.Bijective (((X.left.presheaf.stalkCongr (.of_eq hp)).inv ≫
      f.left.stalkMap p).hom)
    exact ConcreteCategory.bijective_of_isIso _
  exact ⟨AlgEquiv.ofBijective α hbij, rfl⟩

/-- Generic rational-function pullback under the actual complex scheme
automorphism is an equivalence over its structural complex scalars. -/
theorem s2e_c1_actual_fieldPullback_algEquiv
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (f : X ⟶ X) [IsIso f.left] :
    letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
    ∃ σ : X.left.functionField ≃ₐ[ℂ] X.left.functionField,
      σ.toRingHom = s2e_step1_fieldPullback X.left f.left := by
  letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
  let e := s2e_c1_fieldPullbackEquiv X.left f.left
  let σ : X.left.functionField ≃ₐ[ℂ] X.left.functionField :=
    { e with
      commutes' := fun c => by
        change s2e_step1_fieldPullback X.left f.left
          (HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) c) =
            HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) c
        exact s2e_fixed_point_stalkPullback_scalars X f (genericPoint X.left)
          (genericPoint_eq_of_isOpenImmersion f.left) c }
  exact ⟨σ, rfl⟩


/-- The prescribed complex scalars agree along the actual local-ring
embedding into rational functions. -/
theorem s2e_c1_actual_stalk_field_scalar_tower
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (p : X.left) :
    letI : Algebra ℂ (X.left.presheaf.stalk p) :=
      (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
    letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
    IsScalarTower ℂ (X.left.presheaf.stalk p) X.left.functionField := by
  letI : Algebra ℂ (X.left.presheaf.stalk p) :=
    (HodgeLean.Foundations.Curves.stalkC p).toAlgebra
  letI := HodgeLean.Foundations.Curves.functionFieldAlgebra X
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (HodgeLean.Foundations.Curves.algebraMap_stalkC p c).symm


/-- Fixed-point stalk pullback of a section is the germ of its actual
pullback on the full inverse-image neighbourhood. -/
theorem s2e_c1_fixed_stalk_pullback_section_germ
    (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hpU : p ∈ U) (s : Γ(X, U)) :
    s2e_fixed_point_stalkPullback X f p hp (X.presheaf.germ U p hpU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) p (by change f p ∈ U; rwa [hp]) (f.app U s) := by
  have hfp : f p ∈ U := by rwa [hp]
  have he : X.presheaf.germ U p hpU ≫ (X.presheaf.stalkCongr (.of_eq hp)).inv =
      X.presheaf.germ U (f p) hfp := by
    rw [TopCat.Presheaf.stalkCongr_inv]
    exact s2e_germ_stalk_transport X U p (f p) hpU hfp hp.symm
  change (X.presheaf.germ U p hpU ≫ (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p) s = _
  rw [← Category.assoc, he, f.germ_stalkMap]
  rfl


end HodgeLean.Foundations.Program
