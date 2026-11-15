import HodgeLean.Foundations.Program.SchoenSubalgebraProjectivity
import HodgeLean.Foundations.Program.SchoenPowerSubalgebraCharts
import HodgeLean.Foundations.Program.SchoenProjRadicalCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry HomogeneousLocalization CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual chart map of a graded subalgebra respects its original degree-zero coefficient ring. -/
theorem s2_subalgebraChartMap_coefficients {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subalgebra (𝒜 0) A)
    [GradedRing (s2_subringGradedPiece 𝒜 R.toSubring)] (f : R) :
    (Away.map (s2_subringGradedInclusion 𝒜 R.toSubring) f).comp
      ((fromZeroRingHom (s2_subringGradedPiece 𝒜 R.toSubring) (Submonoid.powers f)).comp
        (s2_subalgebraDegreeZeroEquiv 𝒜 R).toRingHom) =
    fromZeroRingHom 𝒜 (Submonoid.powers (f : A)) := by
  apply RingHom.ext
  intro c
  exact s2_away_map_fromZero 𝒜 R.toSubring f (s2_subalgebraDegreeZeroEquiv 𝒜 R c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual radical-controlled Proj map of a graded subalgebra preserves the ambient degree-zero base. -/
theorem s2_subalgebraProjMap_toSpecZero {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subalgebra (𝒜 0) A)
    [GradedRing (s2_subringGradedPiece 𝒜 R.toSubring)]
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (s2_subringGradedPiece 𝒜 R.toSubring)).toIdeal.map
        (s2_subringGradedInclusion 𝒜 R.toSubring).toRingHom).radical) :
    S2RadicalProj.map (s2_subringGradedPiece 𝒜 R.toSubring) 𝒜
      (s2_subringGradedInclusion 𝒜 R.toSubring) hf ≫
      Proj.toSpecZero (s2_subringGradedPiece 𝒜 R.toSubring) ≫
      Spec.map (CommRingCat.ofHom (s2_subalgebraDegreeZeroEquiv 𝒜 R).toRingHom) =
    Proj.toSpecZero 𝒜 := by
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  let q := S2RadicalProj.map ℬ 𝒜 (s2_subringGradedInclusion 𝒜 R.toSubring) hf
  apply Scheme.Cover.hom_ext ((Proj.affineOpenCover ℬ).openCover.pullback₁ q)
  intro c
  have H := (S2RadicalProj.away_isPullback ℬ 𝒜
    (s2_subringGradedInclusion 𝒜 R.toSubring) hf
    c.1.property c.2.val c.2.property).flip
  apply (cancel_epi H.isoPullback.hom).mp
  change H.isoPullback.hom ≫ pullback.fst _ _ ≫ _ =
    H.isoPullback.hom ≫ pullback.fst _ _ ≫ _
  simp only [← Category.assoc, H.isoPullback_hom_fst]
  rw [S2RadicalProj.awayι_comp_map ℬ 𝒜
    (s2_subringGradedInclusion 𝒜 R.toSubring) hf c.1.property c.2.val c.2.property]
  dsimp only [ℬ]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact s2_subalgebraChartMap_coefficients 𝒜 R c.2.val

end HodgeLean.Foundations.Program
