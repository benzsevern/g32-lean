import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse
import HodgeLean.Foundations.Program.SchoenCycleOpenImmersionEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Local regular-section recovery through a scheme immersion

The open factor of an immersion transports section lifts from its closed factor.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.TubularEuler

theorem immersion_local_evaluation_lifts {J : Type}
    (X Y : Over (Spec ↧ℂ)) (e : X ⟶ Y) [IsImmersion e.left]
    (V : X.left.Opens) (s : J → Γ(X.left, V)) (p : ComplexPoint X)
    (hp : p ∈ Point.overOpen V) :
    ∃ (U : Y.left.Opens), Point.map e p ∈ Point.overOpen U ∧
      ∃ r : J → Γ(Y.left, U), ∀ q : ComplexPoint X,
        Point.map e q ∈ Point.overOpen U → ∀ j,
          Point.evaluate U (r j) (Point.map e q) = Point.evaluate V (s j) q := by
  let Z := openScheme Y e.left.coborderRange
  let j : Z ⟶ Y := openInclusion Y e.left.coborderRange
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion e.left.coborderRange.ι)
  let i : X ⟶ Z := Over.homMk e.left.liftCoborder (by
    change e.left.liftCoborder ≫ (e.left.coborderRange.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι]
    exact Over.w e)
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion e.left.liftCoborder)
  have hij : i ≫ j = e := by
    apply Over.OverMorphism.ext
    exact e.left.liftCoborder_ι
  have hmap (q : ComplexPoint X) : Point.map j (Point.map i q) = Point.map e q := by
    rw [← Point.map_comp_apply, hij]
  obtain ⟨W, _, hWV, hpW, r, hr⟩ :=
    i.left.exists_affine_local_section_lifts V s p.underlying hp
  let U := j.left ''ᵁ W
  have hmem (q : ComplexPoint X) :
      Point.map e q ∈ Point.overOpen U ↔ Point.map i q ∈ Point.overOpen W := by
    rw [← hmap q, Point.mem_overOpen_map_iff]
    change (Point.map i q).underlying ∈ j.left ⁻¹ᵁ (j.left ''ᵁ W) ↔ _
    rw [j.left.preimage_image_eq]
    rfl
  refine ⟨U, (hmem p).mpr hpW, (fun k => (j.left.appIso W).inv (r k)), ?_⟩
  intro q hq k
  have hqW := (hmem q).mp hq
  rw [← hmap q, s2e_evaluate_openImmersion_appIso, Point.evaluate_map, hr k]
  exact (Point.evaluate_res hWV (s k) q hqW).symm

end HodgeLean.Foundations.TubularEuler
