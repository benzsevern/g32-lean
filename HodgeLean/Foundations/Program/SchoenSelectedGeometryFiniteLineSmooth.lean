import HodgeLean.Foundations.Program.SchoenSelectedGeometryFiniteAffinePresentation

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint ComplexAlgHom Set Topology
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite flat affine-line morphism locally injective on complex points has smooth source at the marked point. -/
theorem s0_finite_flat_line_smooth_at
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFinitePresentation X.hom]
    (q : X ⟶ Over.mk (affineSpecStructureMap (complexPolynomialRing 1)))
    [IsFinite q.left] [Flat q.left]
    (z : ComplexPoint X) [Filter.NeBot (𝓝[≠] z)]
    (N : Set (ComplexPoint X)) (hN : IsOpen N) (hz : z ∈ N)
    (hi : Set.InjOn (Point.map q) N) : z.underlying ∈ X.hom.smoothLocus := by
  obtain ⟨S, hS, hd, ha, hpa, ht, hfin, hflat, hpres, e, he⟩ :=
    s0_finite_flat_line_affine_presentation X q
  letI := hS
  letI := hd
  letI := ha
  letI := hpa
  letI := ht
  letI := hfin
  letI := hflat
  letI := hpres
  letI := s0_affine_spec_finite_presentation S
  let H := (Point.isoMapHomeomorph e).trans (affineSpecHomeomorph S)
  let φ := IsScalarTower.toAlgHom ℂ (complexPolynomialRing 1) S
  have hcoord (v : S →ₐ[ℂ] ℂ) :
      affineSpecEquiv (complexPolynomialRing 1) (Point.map q (H.symm v)) = v.comp φ := by
    change affineSpecEquiv (complexPolynomialRing 1)
      (Point.map (e.inv ≫ q) ((affineSpecEquiv S).symm v)) = _
    have heq : e.inv ≫ q = Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (specMap_comp_affineSpecStructureMap φ) := Over.OverMorphism.ext he
    rw [heq]
    exact (affineSpecEquiv_affineSpecComplexPointMap φ _).trans
      (congrArg (fun w : S →ₐ[ℂ] ℂ ↦ w.comp φ) ((affineSpecEquiv S).apply_symm_apply v))
  letI : Filter.NeBot (𝓝[≠] (H z)) := by
    have hm : Filter.NeBot (Filter.map H (𝓝[≠] z)) := inferInstance
    rwa [H.map_punctured_nhds_eq] at hm
  have hlocal : Set.InjOn (fun v : S →ₐ[ℂ] ℂ ↦ v.comp φ) (H.symm ⁻¹' N) := by
    intro u hu v hv huv
    apply H.symm.injective
    apply hi hu hv
    apply (affineSpecEquiv (complexPolynomialRing 1)).injective
    rw [hcoord, hcoord]
    exact huv
  have hs := s0_finite_flat_line_spec_smooth_at S (H z) (H.symm ⁻¹' N)
    (hN.preimage H.symm.continuous) (by simpa only [Set.mem_preimage, H.symm_apply_apply] using hz)
    hlocal
  have hs' : e.hom.left z.underlying ∈ (affineSpecStructureMap S).smoothLocus := by
    have hH : (affineSpecEquiv S).symm (H z) = Point.map e.hom z :=
      (affineSpecEquiv S).symm_apply_apply _
    rw [hH] at hs
    exact hs
  have hpre := Scheme.Hom.preimage_smoothLocus_eq e.hom.left (affineSpecStructureMap S)
  have hz' : z.underlying ∈ (e.hom.left ≫ affineSpecStructureMap S).smoothLocus := by
    rw [← hpre]
    exact hs'
  have hew : e.hom.left ≫ affineSpecStructureMap S = X.hom := Over.w e.hom
  simpa only [hew] using hz'

#print axioms s0_finite_flat_line_smooth_at
end HodgeLean.Foundations.Program
