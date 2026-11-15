import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteLineSmooth
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLinePatch
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOpenPoints

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open ComplexAlgHom Set Topology
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A locally injective finite flat projective-line coordinate gives smoothness at a nonisolated complex point. -/
theorem s0_finite_flat_projective_line_smooth_at
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFinitePresentation X.hom]
    (q : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))
    [IsFinite q.left] [Flat q.left]
    (z : ComplexPoint X) [Filter.NeBot (𝓝[≠] z)]
    (N : Set (ComplexPoint X)) (hN : IsOpen N) (hz : z ∈ N)
    (hi : Set.InjOn (Point.map q) N) : z.underlying ∈ X.hom.smoothLocus := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  obtain ⟨i, y, hy⟩ := (s0_complex_projective_cover 1).exists_eq (q.left z.underlying)
  let U : Over (Spec ↧ℂ) := Over.mk ((s0_complex_projective_cover 1).f i ≫ A.hom)
  let u : U ⟶ A := Over.homMk ((s0_complex_projective_cover 1).f i) rfl
  letI : IsOpenImmersion u.left := inferInstanceAs
    (IsOpenImmersion ((s0_complex_projective_cover 1).f i))
  let V : Over (Spec ↧ℂ) := Over.mk (pullback.fst q.left u.left ≫ X.hom)
  let v : V ⟶ X := Over.homMk (pullback.fst q.left u.left) rfl
  letI : IsOpenImmersion v.left := inferInstanceAs
    (IsOpenImmersion (pullback.fst q.left u.left))
  let r : V ⟶ U := Over.homMk (pullback.snd q.left u.left) (by
    change pullback.snd q.left u.left ≫ (u.left ≫ A.hom) = _
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Over.w q]
    rfl)
  have hrv : v ≫ q = r ≫ u := Over.OverMorphism.ext pullback.condition
  have hzv : z.underlying ∈ Set.range v.left := by
    change z.underlying ∈ Set.range (pullback.fst q.left u.left)
    erw [IsOpenImmersion.range_pullbackFst u.left q.left]
    exact ⟨y, hy⟩
  obtain ⟨w, hw⟩ := s0_open_immersion_lift_complex_point v z hzv
  letI : Nonempty V.left := ⟨w.underlying⟩
  letI : IsIntegral V.left := isIntegral_of_isOpenImmersion v.left
  letI : LocallyOfFinitePresentation V.hom := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst q.left u.left ≫ X.hom))
  let E : U ≅ Over.mk (affineSpecStructureMap (complexPolynomialRing 1)) :=
    s0_projective_line_patch_iso i
  let t := r ≫ E.hom
  letI : IsFinite t.left := inferInstanceAs
    (IsFinite (pullback.snd q.left u.left ≫ E.hom.left))
  letI : Flat t.left := inferInstanceAs
    (Flat (pullback.snd q.left u.left ≫ E.hom.left))
  have hv := s0_open_immersion_complex_embedding v
  letI : Filter.NeBot (𝓝[≠] (Point.map v w)) := by rw [hw]; infer_instance
  letI : Filter.NeBot (𝓝[≠] w) := s0_punctured_neBot_of_open_embedding hv w
  have hinj : Set.InjOn (Point.map t) (Point.map v ⁻¹' N) := by
    intro a ha b hb hab
    have hrab : Point.map r a = Point.map r b := (Point.isoMapHomeomorph E).injective hab
    apply hv.injective
    apply hi ha hb
    change Point.map (v ≫ q) a = Point.map (v ≫ q) b
    rw [hrv]
    change Point.map u (Point.map r a) = Point.map u (Point.map r b)
    rw [hrab]
  have hs := s0_finite_flat_line_smooth_at V t w (Point.map v ⁻¹' N)
    (hN.preimage hv.continuous) (by change Point.map v w ∈ N; rw [hw]; exact hz) hinj
  change w.underlying ∈ (v.left ≫ X.hom).smoothLocus at hs
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at hs
  change (Point.map v w).underlying ∈ X.hom.smoothLocus at hs
  rwa [hw] at hs

#print axioms s0_finite_flat_projective_line_smooth_at
end HodgeLean.Foundations.Program
