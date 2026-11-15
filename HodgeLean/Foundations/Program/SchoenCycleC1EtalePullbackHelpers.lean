import HodgeLean.Foundations.Program.SchoenCycleC1SliceHelpers

/-! # Etale pullback over a specified neighbourhood -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A map into a neighbourhood where the cover is etale has etale pullback. -/
theorem s2e_c1_pullback_etale_of_neighbourhood {X Y P : Scheme}
    (f : X ⟶ Y) (g : P ⟶ Y) (U : Y.Opens)
    (hg : Set.range g ⊆ U) [Etale (f ∣_ U)] :
    Etale (pullback.snd f g) := by
  let gU : P ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by
    simpa only [Scheme.Opens.range_ι] using hg)
  have hgU : gU ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hfpre : Set.range (pullback.fst f g) ⊆ (f ⁻¹ᵁ U : Set X) := by
    rintro _ ⟨x, rfl⟩
    change f (pullback.fst f g x) ∈ U
    have he := congrArg (fun h : pullback f g ⟶ Y => h x)
      (pullback.condition (f := f) (g := g))
    change f (pullback.fst f g x) = g (pullback.snd f g x) at he
    rw [he]
    exact hg ⟨pullback.snd f g x, rfl⟩
  let j : pullback f g ⟶ (f ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (pullback.fst f g) (by
      simpa only [Scheme.Opens.range_ι] using hfpre)
  have hj : j ≫ (f ⁻¹ᵁ U).ι = pullback.fst f g :=
    IsOpenImmersion.lift_fac _ _ _
  have hsq : j ≫ (f ∣_ U) = pullback.snd f g ≫ gU := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hj, Category.assoc, hgU, pullback.condition]
  have hall : IsPullback (j ≫ (f ⁻¹ᵁ U).ι) (pullback.snd f g) f (gU ≫ U.ι) := by
    rw [hj, hgU]
    exact IsPullback.of_hasPullback f g
  have hpb : IsPullback j (pullback.snd f g) (f ∣_ U) gU :=
    hall.of_right hsq (isPullback_morphismRestrict f U).flip
  exact MorphismProperty.of_isPullback (P := @Etale) hpb inferInstance

/-- Points above every slice point make the finite actual pullback projection
surjective on scheme points. -/
theorem s2e_c1_pullback_surjective_of_slice_points
    (W B P : Over (Spec ↧ℂ)) [LocallyOfFiniteType P.hom]
    (β : W ⟶ B) [IsFinite β.left] (ℓ : P ⟶ B)
    (hlift : ∀ x : ComplexPoint P, ∃ z : ComplexPoint W,
      Point.map β z = Point.map ℓ x) :
    Surjective (pullback.snd β.left ℓ.left) := by
  let T : Over (Spec ↧ℂ) := Over.mk (pullback.snd β.left ℓ.left ≫ P.hom)
  let π : T ⟶ P := Over.homMk (pullback.snd β.left ℓ.left)
  haveI : IsFinite π.left := inferInstanceAs (IsFinite (pullback.snd β.left ℓ.left))
  apply s2e_c11_surjective_of_point_surjective T P π
  intro x
  obtain ⟨z, hz⟩ := hlift x
  have he : z.left ≫ β.left = x.left ≫ ℓ.left := congrArg Over.Hom.left hz
  let t : ComplexPoint T := Over.homMk (pullback.lift z.left x.left he) (by
    change (pullback.lift z.left x.left he) ≫ pullback.snd β.left ℓ.left ≫ P.hom = 𝟙 _
    rw [← Category.assoc, pullback.lift_snd]
    exact Over.w x)
  refine ⟨t, ?_⟩
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

end HodgeLean.Foundations.Program
