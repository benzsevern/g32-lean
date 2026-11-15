import HodgeLean.Foundations.Program.G32Native.PairedC3AffineGenerators
import HodgeLean.Foundations.Program.G32Native.PairedC3AugmentedCotangentBasis
import HodgeLean.Foundations.Program.SchoenCycleCotangentEtaleCoordinates
import HodgeLean.Foundations.Program.SchoenCycleAffineCoordinateRestriction
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! # Prescribed slice equations on an actual étale affine neighbourhood -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A prescribed cotangent basis whose selected germs generate a slice
ideal supplies étale affine coordinates generating that same ideal sheaf.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; EGA IV, 17.11.1. -/
theorem paired_c3_etale_slice_equations
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (I : X.left.IdealSheafData)
    (x : ComplexPoint X) :
    let A := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∀ (c : Fin n → A) (hc : ∀ j, c j ∈ IsLocalRing.maximalIdeal A)
      (b : Module.Basis (Fin n) (IsLocalRing.ResidueField A)
        (IsLocalRing.maximalIdeal A).Cotangent),
      (∀ j, b j = (IsLocalRing.maximalIdeal A).toCotangent ⟨c j, hc j⟩) →
      ∀ (k : ℕ) (sel : Fin k → Fin n),
      I.stalkIdeal x.underlying = Ideal.span (Set.range (c ∘ sel)) →
      ∃ (U : X.left.affineOpens) (hxU : x.underlying ∈ U.1),
        letI := s2e_step1_sectionAlgebra X U.1
        ∃ F : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, U.1),
          F.toRingHom.Etale ∧
          I.ideal U = Ideal.span (Set.range (fun j => F (MvPolynomial.X (sel j)))) ∧
          ∀ j, (X.left.presheaf.germ U.1 x.underlying hxU).hom
            (F (MvPolynomial.X j)) = c j := by
  dsimp only
  let A := X.left.presheaf.stalk x.underlying
  letI : Algebra ℂ A := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  intro c hc b hb k sel hgen
  let bC := pairedC3AugmentedCotangentBasis (s2e_complex_point_augmentation X x) b
  obtain ⟨D, hD⟩ := s2e_localEtaleCoordinates_of_cotangent_basis X n x c hc bC
    (fun j => (pairedC3AugmentedCotangentBasis_apply _ b j).trans (hb j))
  let U : X.left.affineOpens := ⟨D.neighborhood, D.isAffine⟩
  letI := s2e_step1_sectionAlgebra X U.1
  let z : Fin n → Γ(X.left, U.1) := fun j => D.coordinateAlgHom (MvPolynomial.X j)
  have he : (I.ideal U).map (X.left.presheaf.germ U.1 x.underlying D.mem).hom =
      (Ideal.span (Set.range (z ∘ sel))).map
        (X.left.presheaf.germ U.1 x.underlying D.mem).hom := by
    rw [← I.stalkIdeal_eq_map_germ U D.mem, hgen, Ideal.map_span, ← Set.range_comp]
    congr 1
    exact congrArg Set.range (funext (fun j => (hD (sel j)).symm))
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth n X.hom
  letI : IsNoetherianRing Γ(X.left, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨V, hVU, hxV, hEq⟩ := s2e_affine_ideals_equal_near_point X.left U x.underlying
    D.mem (I.ideal U) (Ideal.span (Set.range (z ∘ sel)))
    (Ideal.fg_of_isNoetherianRing _) (Ideal.fg_of_isNoetherianRing _) he
  let res := X.left.presheaf.map (homOfLE (X := X.left.Opens) hVU).op
  letI := s2e_step1_sectionAlgebra X V.1
  let ρ := s2e_sectionRestrictionAlgHom X U.1 V.1 hVU
  let F := ρ.comp D.coordinateAlgHom
  have hF : F.toRingHom.Etale := RingHom.Etale.stableUnderComposition _ _ D.etale
    (s2e_affine_section_restriction_etale X U V hVU)
  refine ⟨V, hxV, F, hF, ?_, ?_⟩
  · have h := (I.map_ideal hVU).symm.trans hEq
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  · intro j
    change (res ≫ X.left.presheaf.germ V.1 x.underlying hxV).hom (z j) = c j
    rw [X.left.presheaf.germ_res]
    exact hD j

#print axioms paired_c3_etale_slice_equations
end HodgeLean.Foundations.Program.G32Native
