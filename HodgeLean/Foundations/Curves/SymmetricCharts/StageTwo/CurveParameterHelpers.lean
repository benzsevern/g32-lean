import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoordinateHelpers
import HodgeLean.Foundations.Program.SchoenTowerI2aFiniteCurveSupport
import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! # A common curve parameter for finite ordered support

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] overSpecAlgebra

/-- A common affine curve neighborhood has an etale parameter reflecting all equalities in a finite family.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem finite_curve_parameters (C : Over (Spec ↧ℂ)) [IsIntegral C.left]
    [Smooth C.hom] [IsProjective C.hom] [SmoothOfRelativeDimension 1 C.hom]
    (n : ℕ) (z : Fin n → ComplexPoint C) :
    ∃ (U : C.left.Opens) (t : U.toScheme ⟶ (affine 1).left)
      (u : Fin n → (Spec ↧ℂ ⟶ U.toScheme)),
      IsAffineOpen U ∧ Etale t ∧ t ≫ (affine 1).hom = U.ι ≫ C.hom ∧
      (∀ i, u i ≫ U.ι = (z i).left) ∧
      ∀ i j, u i ≫ t = u j ≫ t ↔ z i = z j := by
  classical
  obtain ⟨p₀⟩ := s2t_nonempty_complexPoints C
  let S := insert p₀ (Finset.univ.image z)
  let si (i : Fin n) : S := ⟨z i, Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  letI : Nonempty S := ⟨⟨p₀, Finset.mem_insert_self _ _⟩⟩
  obtain ⟨A, hA, a, y, s, ha, hy, hs, hsep, hI⟩ :=
    s2v_i2a_finite_curve_point_parameters C (SmoothOfRelativeDimension.dim_eq C.hom 1)
      (fun q : S => q.val) Subtype.val_injective
  letI := hA
  letI := ha
  letI := overSpecAlgebra A ⊤
  let G : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Γ(A.left, ⊤) :=
    MvPolynomial.aeval (fun _ => s)
  have hG : G.toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hs
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hs
  let f : A ⟶ affine 1 := s2e_section_defined_affine_map A _ G
  have hf : f.left = A.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom G.toRingHom) := rfl
  haveI : Etale f.left := by
    haveI : Etale (Spec.map (CommRingCat.ofHom G.toRingHom)) :=
      HasRingHomProperty.Spec_iff.mpr hG
    rw [hf]
    infer_instance
  have hval (q : S) :
      ComplexPoint.affineSpecEquiv (MvPolynomial (Fin 1) ℂ) (Point.map f (y q))
        (MvPolynomial.X (0 : Fin 1)) = Point.evaluate ⊤ s (y q) := by
    have H := s2e_spec_coordinate_evaluation A _ f (CommRingCat.ofHom G.toRingHom)
      hf (y q) (MvPolynomial.X (0 : Fin 1))
    change _ = Point.evaluate ⊤ (G (MvPolynomial.X (0 : Fin 1))) (y q) at H
    simpa only [G, MvPolynomial.aeval_X] using H
  let U := a.left.opensRange
  let e := IsOpenImmersion.isoOfRangeEq a.left U.ι (by
    rw [Scheme.Opens.range_ι]
    rfl)
  have he : e.hom ≫ U.ι = a.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hei : e.inv ≫ a.left = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  refine ⟨U, e.inv ≫ f.left, (fun i => (y (si i)).left ≫ e.hom),
    isAffineOpen_opensRange a.left, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, Over.w f, ← Over.w a, ← Category.assoc, hei]
  · intro i
    rw [Category.assoc, he]
    exact congrArg (fun q : ComplexPoint C => q.left) (hy (si i))
  · intro i j
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    constructor
    · intro hij
      have H : Point.map f (y (si i)) = Point.map f (y (si j)) :=
        Over.OverMorphism.ext hij
      have Hv := congrArg (fun q : ComplexPoint (affine 1) =>
        ComplexPoint.affineSpecEquiv (MvPolynomial (Fin 1) ℂ) q (MvPolynomial.X (0 : Fin 1))) H
      rw [hval, hval] at Hv
      exact congrArg Subtype.val (hsep Hv)
    · intro hij
      have H : si i = si j := Subtype.ext hij
      rw [H]

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
