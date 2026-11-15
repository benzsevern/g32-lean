import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveFibers

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

theorem s0_irreducible_of_open_cover_common_point
    {X I : Type*} [TopologicalSpace X] (U : I → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hirr : ∀ i, IsIrreducible (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (p : X) (hp : ∀ i, p ∈ U i) :
    IrreducibleSpace X := by
  rw [irreducibleSpace_def]
  refine ⟨⟨p, mem_univ p⟩, ?_⟩
  intro A B hA hB hAn hBn
  obtain ⟨x, _, hx⟩ := hAn
  obtain ⟨y, _, hy⟩ := hBn
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨j, hyj⟩ := hcover y
  obtain ⟨z, _, hzA, hzj⟩ := (hirr i).isPreirreducible A (U j) hA (hopen j)
    ⟨x, hxi, hx⟩ ⟨p, hp i, hp j⟩
  obtain ⟨w, _, hwA, hwB⟩ := (hirr j).isPreirreducible A B hA hB
    ⟨z, hzj, hzA⟩ ⟨y, hyj, hy⟩
  exact ⟨w, mem_univ w, hwA, hwB⟩

#print axioms s0_irreducible_of_open_cover_common_point

/-- The standard projective affine charts after base change to the complex numbers.
Source: Hartshorne, Algebraic Geometry, II.2.5, standard projective affine charts. -/
def s0_complex_projective_cover (n : ℕ) :
    (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).OpenCover :=
  Scheme.Pullback.openCoverOfRight
    (Proj.affineOpenCoverOfIrrelevantLESpan (UniversalGrading.{0} n)
      (MvPolynomial.X : Fin (n + 1) → UniversalRing.{0} n)
      (fun i ↦ MvPolynomial.isHomogeneous_X _ i) (fun _ ↦ zero_lt_one)
      (irrelevant_le_span_coordinates n)).openCover
    (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading.{0} n)))

#print axioms s0_complex_projective_cover

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_complex_projective_patch_integral (n : ℕ) (i : Fin (n + 1)) :
    IsIntegral ((s0_complex_projective_cover n).X i) := by
  letI : Algebra (ULift.{0} ℤ) ℂ :=
    ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom).toAlgebra
  let e : (s0_complex_projective_cover n).X i ≅
      pullback (terminal.from (Spec ↧ℂ))
        (terminal.from (Spec ↧(HomogeneousLocalization.Away
          (UniversalGrading.{0} n) (MvPolynomial.X i)))) :=
    pullback.congrHom rfl (Subsingleton.elim _ _)
  haveI := s0_projective_chart_fiber_integral ℂ i
  exact IsIntegral.of_isIso e.inv

#print axioms s0_complex_projective_patch_integral

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_complex_projective_cover_common_point (n : ℕ) :
    ∃ q : ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ),
      ∀ i : Fin (n + 1), q ∈ Set.range ((s0_complex_projective_cover n).f i) := by
  let v : CoordinateSpace n := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro h
    have h0 : (1 : ℂ) = 0 := congrFun h (0 : Fin (n + 1))
    exact one_ne_zero h0
  let p : Spec ↧ℂ := (⟨⊥, inferInstance⟩ : PrimeSpectrum ℂ)
  refine ⟨vectorToProjectiveSpace v hv p, ?_⟩
  intro i
  have hi : v i ≠ 0 := one_ne_zero
  let a := Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi))
  let b : Spec ↧ℂ ⟶ (s0_complex_projective_cover n).X i :=
    pullback.lift (𝟙 _) a (Subsingleton.elim _ _)
  have he : a ≫ Proj.awayι (UniversalGrading.{0} n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X _ i) zero_lt_one = chartIntegralProj v hv :=
    (chartIntegralProj_eq_chartIntegralProjAt v hv i hi).symm
  have hb : b ≫ (s0_complex_projective_cover n).f i = vectorToProjectiveSpace v hv := by
    apply pullback.hom_ext
    · simp only [s0_complex_projective_cover, Scheme.Pullback.openCoverOfRight_f]
      rw [Category.assoc (obj := Scheme.{0})]
      simp only [pullback.map, pullback.lift_fst, Category.comp_id,
        b, vectorToProjectiveSpace]
    · simp only [s0_complex_projective_cover, Scheme.Pullback.openCoverOfRight_f]
      rw [Category.assoc (obj := Scheme.{0})]
      simp only [pullback.map, pullback.lift_snd, Category.comp_id,
        b, vectorToProjectiveSpace, pullback.lift_snd_assoc,
        Proj.affineOpenCoverOfIrrelevantLESpan, Scheme.AffineOpenCover.openCover]
      exact he
  exact ⟨b p, congrArg (fun f : Spec ↧ℂ ⟶ ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) ↦ f p) hb⟩

#print axioms s0_complex_projective_cover_common_point

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_complex_projective_integral (n : ℕ) :
    IsIntegral (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) := by
  let V := s0_complex_projective_cover n
  letI (i : Fin (n + 1)) : IsIntegral (V.X i) := s0_complex_projective_patch_integral n i
  letI : IsReduced (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) :=
    IsReduced.of_openCover _ V
  obtain ⟨q, hq⟩ := s0_complex_projective_cover_common_point n
  have hiri (i : Fin (n + 1)) : IsIrreducible (Set.range (V.f i)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (V.X i)).image (V.f i) (V.f i).continuous.continuousOn
  letI : IrreducibleSpace (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)) :=
    s0_irreducible_of_open_cover_common_point (fun i ↦ Set.range (V.f i))
      (fun i ↦ (V.f i).opensRange.2) hiri
      (fun x ↦ by obtain ⟨i, y, hy⟩ := V.exists_eq x; exact ⟨i, y, hy⟩) q hq
  exact isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms s0_complex_projective_integral

end HodgeLean.Foundations.Program
