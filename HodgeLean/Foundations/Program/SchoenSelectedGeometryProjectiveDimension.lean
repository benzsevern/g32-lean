import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveIntegral

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] specializationOrder in
theorem s0_krull_dimension_bound_of_open_cover
    {X : Type*} [TopologicalSpace X] [T0Space X] [QuasiSober X]
    {I : Type*} (Y : I → Type*) [∀ i, TopologicalSpace (Y i)]
    [∀ i, T0Space (Y i)] [∀ i, QuasiSober (Y i)]
    (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hc : ∀ x, ∃ i y, f i y = x) (n : ℕ)
    (hd : ∀ i, topologicalKrullDim (Y i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim_eq_krullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hc x
  rw [(hf i).coheight_eq (f i)]
  exact (Order.coheight_le_krullDim y).trans (by
    simpa only [topologicalKrullDim_eq_krullDim] using hd i)

#print axioms s0_krull_dimension_bound_of_open_cover

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_complex_projective_patch_krull_dimension (n : ℕ) (i : Fin (n + 1)) :
    topologicalKrullDim ((s0_complex_projective_cover n).X i) = n := by
  letI : Algebra (ULift.{0} ℤ) ℂ :=
    ((Int.castRingHom ℂ).comp (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom).toAlgebra
  let e : (s0_complex_projective_cover n).X i ≅
      pullback (terminal.from (Spec ↧ℂ))
        (terminal.from (Spec ↧(HomogeneousLocalization.Away
          (UniversalGrading.{0} n) (MvPolynomial.X i)))) :=
    pullback.congrHom rfl (Subsingleton.elim _ _)
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (s0_projective_chart_fiber_iso ℂ i).hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial {j : Fin (n + 1) // j ≠ i} ℂ)) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add]
  congr 1
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

#print axioms s0_complex_projective_patch_krull_dimension

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_complex_projective_krull_dimension (n : ℕ) :
    topologicalKrullDim (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) : Scheme.{0}) = n := by
  let V := s0_complex_projective_cover n
  apply le_antisymm
  · apply s0_krull_dimension_bound_of_open_cover (fun i ↦ V.X i) (fun i ↦ V.f i)
      (fun i ↦ (V.f i).isOpenEmbedding)
      (fun x ↦ V.exists_eq x) n
    intro i
    exact (s0_complex_projective_patch_krull_dimension n i).le
  · rw [← s0_complex_projective_patch_krull_dimension n (0 : Fin (n + 1))]
    exact (V.f (0 : Fin (n + 1))).isOpenEmbedding.isInducing.topologicalKrullDim_le

#print axioms s0_complex_projective_krull_dimension

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_complex_projective_dimension (n : ℕ) :
    letI := s0_complex_projective_integral n
    TopologicalSpace.dim (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ) : Scheme.{0}) = n := by
  letI := s0_complex_projective_integral n
  unfold TopologicalSpace.dim
  rw [s0_complex_projective_krull_dimension]
  simp

#print axioms s0_complex_projective_dimension

/-- The identity embedding gives the projective presentation of projective space.
Source: Hartshorne, Algebraic Geometry, II.4, definition of a projective morphism. -/
theorem s0_projective_space_projective (n : ℕ) (S : Scheme.{0}) :
    IsProjective (ProjectiveSpace.toBase (Fin (n + 1)) S) := by
  exact ⟨⟨{ ambientDimension := n
            immersion := 𝟙 _
            immersion_toBase := Category.id_comp _ }⟩⟩

#print axioms s0_projective_space_projective

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s0_complex_projective_relative_dimension (n : ℕ) :
    SmoothOfRelativeDimension n (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) := by
  letI := s0_complex_projective_integral n
  letI := s0_projective_space_smooth n (Spec ↧ℂ)
  have h : SmoothOfRelativeDimension
      (TopologicalSpace.dim (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)))
      (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)) := inferInstance
  rwa [s0_complex_projective_dimension] at h

#print axioms s0_complex_projective_relative_dimension

end HodgeLean.Foundations.Program
