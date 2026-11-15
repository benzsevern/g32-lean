import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CurveParameterHelpers

/-! # Empty-degree coordinate transport

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000

/-- Polynomial affine space in zero variables has an etale section over the base.
Source: Hartshorne, Algebraic Geometry, II.2.
HC no distance; AV milestone no distance.
-/
theorem affine_zero_base_section : ∃ f : Spec ↧ℂ ⟶ (affine 0).left,
    Etale f ∧ f ≫ (affine 0).hom = 𝟙 _ := by
  let e := MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)
  let f := Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)
  haveI : Etale f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.Etale.of_bijective e.bijective)
  refine ⟨f, inferInstance, ?_⟩
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have hc : CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin 0) ℂ)) ≫
      CommRingCat.ofHom e.toRingEquiv.toRingHom = 𝟙 _ := by
    ext c
    exact e.commutes c
  rw [hc, Spec.map_id]

/-- Empty ordered tuples have the required coordinate transport without any coordinate equations.
Source: Milne, Jacobian Varieties, §3, empty effective divisor.
HC no distance; AV milestone no distance.
-/
theorem curve_transport_zero
    (C B : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [SmoothOfRelativeDimension 0 B.hom]
    (γ : g3_power C 0 ⟶ B) (z : Fin 0 → ComplexPoint C) :
    ∃ (U : C.left.Opens) (t : U.toScheme ⟶ (affine 1).left)
      (u : Fin 0 → (Spec ↧ℂ ⟶ U.toScheme))
      (V : B.left.Opens)
      (v : Spec ↧ℂ ⟶ V.toScheme) (c : V.toScheme ⟶ (affine 0).left),
      IsAffineOpen U ∧ Etale t ∧ Etale c ∧
      t ≫ (affine 1).hom = U.ι ≫ C.hom ∧
      c ≫ (affine 0).hom = V.ι ≫ B.hom ∧
      (∀ i, u i ≫ U.ι = (z i).left) ∧
      v ≫ V.ι = (s2_lift 0 z ≫ γ).left ∧
      (∀ i j, u i ≫ t = u j ≫ t ↔ z i = z j) ∧
      ∀ (y : Fin 0 → ComplexPoint C) (uy : Fin 0 → (Spec ↧ℂ ⟶ U.toScheme))
        (w : Spec ↧ℂ ⟶ V.toScheme),
        (∀ i, uy i ≫ U.ι = (y i).left) →
        w ≫ V.ι = (s2_lift 0 y ≫ γ).left →
        ∀ j : Fin 0,
          (Scheme.ΓSpecIso ↧ℂ).hom
            ((w ≫ c).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 0) ℂ)).inv
              (MvPolynomial.X j))) =
          MvPolynomial.eval (fun i => (Scheme.ΓSpecIso ↧ℂ).hom
            ((uy i ≫ t).appTop ((Scheme.ΓSpecIso ↧(MvPolynomial (Fin 1) ℂ)).inv
              (MvPolynomial.X (0 : Fin 1)))))
            (MvPolynomial.esymm (Fin 0) ℂ (j.val+1)) := by
  obtain ⟨U, t, u, hU, ht, hbase, hu, hsep⟩ := finite_curve_parameters C 0 z
  obtain ⟨f, hf, hfb⟩ := affine_zero_base_section
  letI := ht
  letI := hf
  letI : Etale B.hom := (Etale.iff_smoothOfRelativeDimension_zero (f := B.hom)).mpr inferInstance
  let V : B.left.Opens := ⊤
  let x : ComplexPoint B := s2_lift 0 z ≫ γ
  let v := ComplexPoint.liftToOpen B V x (by trivial)
  refine ⟨U, t, u, V, v, V.ι ≫ B.hom ≫ f, hU, ht, inferInstance,
    hbase, ?_, hu, ?_, hsep, ?_⟩
  · rw [Category.assoc, Category.assoc, hfb, Category.comp_id]
  · exact ComplexPoint.liftToOpen_fac B V x (by trivial)
  · intro y uy w hy hw j
    exact Fin.elim0 j

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
