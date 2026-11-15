import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension
import HodgeLean.Adapters.ExpHolomorphicProofs

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.Point Filter Topology Set
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_affine_global_evaluation_analytic (n : ℕ)
    (s : Γ(complexAffineSpace (Fin n), ⊤)) (v : Fin n → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv (Fin n)).symm w)) v := by
  simp only [evaluate_affineSpaceEquiv_symm_top]
  induction affineGlobalPolynomial s using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin n → ℂ ↦ a) v)
  | add p q hp hq => simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa only [map_mul, MvPolynomial.eval_X, Pi.mul_def, ContinuousLinearMap.proj_apply] using
        hp.mul ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt v)

#print axioms s0_affine_global_evaluation_analytic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_affine_basicOpen_evaluation_analytic (n : ℕ)
    (f : Γ(complexAffineSpace (Fin n), ⊤))
    (t : Γ(complexAffineSpace (Fin n), (complexAffineSpace (Fin n)).basicOpen f))
    (v : Fin n → ℂ)
    (hv : (affineSpaceEquiv (Fin n)).symm v ∈
      overOpen ((complexAffineSpace (Fin n)).basicOpen f)) :
    AnalyticAt ℂ (fun w : Fin n → ℂ ↦
      evaluate ((complexAffineSpace (Fin n)).basicOpen f) t
        ((affineSpaceEquiv (Fin n)).symm w)) v := by
  obtain ⟨k, a, h⟩ := exists_evaluate_basicOpen_eq_div
    (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
    (isAffineOpen_top (complexAffineSpace (Fin n))) f t
  have ha := s0_affine_global_evaluation_analytic n a v
  have hf := s0_affine_global_evaluation_analytic n f v
  have hne := (mem_overOpen_basicOpen_iff_evaluate_ne_zero
    (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) (U := ⊤) f _ trivial).mp hv
  apply (ha.div (hf.pow k) (pow_ne_zero k hne)).congr
  filter_upwards [(isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hv] with w hw
  exact (h _ hw).symm

#print axioms s0_affine_basicOpen_evaluation_analytic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_affine_local_evaluation_analytic (n : ℕ)
    (U : (complexAffineSpace (Fin n)).Opens) (s : Γ(complexAffineSpace (Fin n), U))
    (v : Fin n → ℂ) (hv : (affineSpaceEquiv (Fin n)).symm v ∈ overOpen U) :
    AnalyticAt ℂ (fun w : Fin n → ℂ ↦ evaluate U s ((affineSpaceEquiv (Fin n)).symm w)) v := by
  obtain ⟨f, hfU, hvf⟩ :=
    (isAffineOpen_top (complexAffineSpace (Fin n))).exists_basicOpen_le
      ⟨((affineSpaceEquiv (Fin n)).symm v).underlying, hv⟩ trivial
  let t := (complexAffineSpace (Fin n)).presheaf.map (homOfLE hfU).op s
  apply (s0_affine_basicOpen_evaluation_analytic n f t v hvf).congr
  filter_upwards [(isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hvf] with w hw
  exact (evaluate_res (X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
    hfU s ((affineSpaceEquiv (Fin n)).symm w) hw).symm

#print axioms s0_affine_local_evaluation_analytic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_affine_coordinate_inverse_holomorphic (n d : ℕ)
    [SmoothOfRelativeDimension d (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)] :
    letI : SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)).hom :=
      inferInstanceAs (SmoothOfRelativeDimension d (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      (affineSpaceEquiv (Fin n)).symm := by
  letI : SmoothOfRelativeDimension d (Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)).hom :=
    inferInstanceAs (SmoothOfRelativeDimension d (complexAffineSpace (Fin n) ↘ Spec ↧ℂ))
  let X := Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)
  intro v
  rw [contMDiffAt_iff]
  refine ⟨(continuous_affineSpaceEquiv_symm (Fin n)).continuousAt, ?_⟩
  let z : ComplexPoint X := (affineSpaceEquiv (Fin n)).symm v
  have hchart : chartAt (Fin d → ℂ) ((affineSpaceEquiv (Fin n)).symm v) =
      localChart X d z := rfl
  have hz := mem_localChart_source X d z
  have hevent : ∀ᶠ w in 𝓝 v,
      (affineSpaceEquiv (Fin n)).symm w ∈ (localChart X d z).source :=
    (continuous_affineSpaceEquiv_symm (Fin n)).continuousAt
      ((localChart X d z).open_source.mem_nhds hz)
  have ha : AnalyticAt ℂ (fun w ↦ localChart X d z ((affineSpaceEquiv (Fin n)).symm w)) v := by
    apply AnalyticAt.pi
    intro i
    let D := localEtaleCoordinates X d z
    have hU : z ∈ overOpen D.ambientCoordinateOpen := by
      simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using
        mem_coordinateNeighborhood_of_mem_localChart_source X d z z hz
    apply (s0_affine_local_evaluation_analytic n D.ambientCoordinateOpen
      (D.ambientCoordinateSection i) v hU).congr
    filter_upwards [hevent] with w hw
    exact (localChart_apply_component_eq_evaluate X d z _ hw i).symm
  simpa [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, hchart] using ha.contDiffAt.contDiffWithinAt

#print axioms s0_affine_coordinate_inverse_holomorphic

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_affine_coordinate_spec_point (n : ℕ) (v : Fin n → ℂ) :
    ((affineSpaceEquiv (Fin n)).symm v).left ≫ (AffineSpace.SpecIso (Fin n) ↧ℂ).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval v)) := by
  let p := (affineSpecEquiv (ComplexAlgHom.complexPolynomialRing n)).symm (MvPolynomial.aeval v)
  have hp : polynomialSpecToAffineSpacePointMap p = (affineSpaceEquiv (Fin n)).symm v := by
    apply (affineSpaceEquiv (Fin n)).injective
    rw [affineSpaceEquiv_polynomialSpecToAffineSpacePointMap, Equiv.apply_symm_apply]
    simp [p, ComplexAlgHom.mvPolynomialAlgHomHomeomorph, ComplexAlgHom.mvPolynomialAlgHomEquiv]
  have h := congrArg (fun z : ComplexPoint
    (Over.mk (complexAffineSpace (Fin n) ↘ Spec ↧ℂ)) ↦ z.left) hp
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom) ≫
    (AffineSpace.SpecIso (Fin n) ↧ℂ).inv = ((affineSpaceEquiv (Fin n)).symm v).left at h
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

#print axioms s0_affine_coordinate_spec_point

end HodgeLean.Foundations.Program
