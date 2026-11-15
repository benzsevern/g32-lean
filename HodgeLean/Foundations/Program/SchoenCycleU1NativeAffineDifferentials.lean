import HodgeLean.Foundations.Program.SchoenCycleU1NativeStalkJets

/-! # Nonzero native coordinate derivatives on actual affine sections -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Point Filter Topology
namespace HodgeLean.Foundations.Program

/-- The infinitesimal component of a native section jet is its actual derivative.
Source: Hartshorne, Algebraic Geometry, II.8, coordinate tangent vectors. -/
theorem s2e_u1_nativeSectionJet_snd
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hp : p.underlying ∈ U) (s : Γ(Z.left, U)) :
    (s2e_u1_nativeSectionJet Z p U hp s).snd =
      deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 := by
  change (s2e_u1_analyticGermJet (s2e_u1_analyticGerm _
    ((s2e_u1_nativeCurve_regular_sections Z p U hp).2 s))).snd = _
  rw [s2e_u1_analyticGermJet_representative]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]

/-- The actual native stalk jet is nonstationary, witnessed by its defining
regular coordinate with derivative one.
Source: HodgeConjecture, `localChart`, and Hartshorne, Algebraic Geometry, II.8. -/
theorem s2e_u1_nativeStalkJet_nonstationary
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z) :
    ∃ s : Z.left.presheaf.stalk p.underlying, (s2e_u1_nativeStalkJet Z p s).snd ≠ 0 := by
  let U := (localEtaleCoordinates Z 1 p).ambientCoordinateOpen
  let s := (localEtaleCoordinates Z 1 p).ambientCoordinateSection 0
  have hp : p.underlying ∈ U := by
    have h := mem_coordinateNeighborhood_of_mem_localChart_source Z 1 p p
      (mem_localChart_source Z 1 p)
    simpa only [U, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      overOpen, Set.mem_setOf_eq] using h
  refine ⟨(Z.left.presheaf.germ U p.underlying hp).hom s, ?_⟩
  rw [s2e_u1_nativeStalkJet_germ, s2e_u1_nativeSectionJet_snd]
  rw [s2e_u1_nativeCurve_coordinate_derivative]
  exact one_ne_zero

/-- Any affine neighbourhood of a native smooth curve point has a regular
section with nonzero derivative along the native coordinate curve.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, affine local rings and tangent vectors. -/
theorem s2e_u1_affine_section_native_derivative_ne_zero
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hU : IsAffineOpen U) (hp : p.underlying ∈ U) :
    ∃ s : Γ(Z.left, U),
      deriv (fun t => Point.evaluate U s (s2e_u1_nativeCurve Z p t)) 0 ≠ 0 := by
  obtain ⟨s, hs⟩ := s2e_u1_stalk_jet_detected_on_affine Z.left U hU
    ⟨p.underlying, hp⟩ (s2e_u1_nativeStalkJet Z p)
    (s2e_u1_nativeStalkJet_nonstationary Z p)
  rw [s2e_u1_nativeStalkJet_germ, s2e_u1_nativeSectionJet_snd] at hs
  exact ⟨s, hs⟩

end HodgeLean.Foundations.Program
