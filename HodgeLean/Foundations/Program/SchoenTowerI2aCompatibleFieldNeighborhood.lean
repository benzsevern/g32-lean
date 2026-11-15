import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts
import HodgeLean.Foundations.Program.SchoenTowerI2aInitialTowerChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant field point and the specified complex point share an actual
affine neighborhood mapping into the prescribed open chart of the base.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, exists_isAffineOpen_mem_and_subset and IsOpenImmersion.lift. -/
theorem s2v_i2a_affine_field_neighborhood_over_chart
    {K : Type} [Field K] (X B U : Over (Spec ↧ℂ)) [IsIntegral X.left]
    (f : X ⟶ B) (u : U ⟶ B) [IsOpenImmersion u.left]
    (η : Spec ↧K ⟶ X.left) [IsDominant η]
    (x : ComplexPoint X) (p : ComplexPoint U) (hp : Point.map u p = Point.map f x) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (v : V ⟶ X)
      (ηV : Spec ↧K ⟶ V.left) (k : V ⟶ U),
      IsOpenImmersion v.left ∧ x ∈ Set.range (Point.map v) ∧
      ηV ≫ v.left = η ∧ v ≫ f = k ≫ u := by
  let O := f.left ⁻¹ᵁ u.left.opensRange
  have hxO : x.underlying ∈ O := by
    change f.left x.underlying ∈ Set.range u.left
    refine ⟨p.underlying, ?_⟩
    exact congrArg Point.underlying hp
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hxO
  let V := ComplexPoint.openScheme X W
  let v : V ⟶ X := ComplexPoint.openInclusion X W
  let xV := ComplexPoint.asOpenPoint X W x hxW
  haveI : Nonempty W := ⟨⟨x.underlying, hxW⟩⟩
  have hpre := s2v_i2a_dominant_field_preimage η W
  have hηrange : Set.range η ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ η ⁻¹ᵁ W := by rw [hpre]; trivial
    exact ⟨⟨η z, hz⟩, rfl⟩
  have hrange : Set.range (v.left ≫ f.left) ⊆ Set.range u.left := by
    rintro _ ⟨y, rfl⟩
    exact hWO y.property
  let k₀ := IsOpenImmersion.lift u.left (v.left ≫ f.left) hrange
  have hk₀ : k₀ ≫ u.left = v.left ≫ f.left := IsOpenImmersion.lift_fac _ _ _
  let k : V ⟶ U := Over.homMk k₀ (by
    rw [← Over.w u, ← Category.assoc, hk₀, Category.assoc, Over.w f, Over.w v])
  refine ⟨V, hW, v, IsOpenImmersion.lift W.ι η hηrange, k,
    inferInstanceAs (IsOpenImmersion W.ι), ⟨xV, ?_⟩,
    IsOpenImmersion.lift_fac _ _ _, ?_⟩
  · apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X W x hxW
  · apply Over.OverMorphism.ext
    exact hk₀.symm

end HodgeLean.Foundations.Program
