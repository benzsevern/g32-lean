import HodgeLean.Foundations.Program.SchoenCycleCurveJets
import HodgeLean.Foundations.Program.SchoenCycleParameterJetAlgebra
import HodgeLean.Foundations.Curves.CurvePoints
import HodgeLean.Foundations.Curves.CurveDivisorClassesLemmas

/-! # Finite coordinate expansions in actual smooth curve stalks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Evaluation at an actual complex point preserves the scalar functions in its stalk.
Source: Mathlib, AlgebraicGeometry.SpecToEquivOfLocalRing;
Hartshorne, Algebraic Geometry, II.2, local morphisms over the base field. -/
theorem s2e_complex_point_stalk_constants
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (p : ComplexPoint X) (c : ℂ) :
    p.stalkHom.hom (HodgeLean.Foundations.Curves.stalkC p.underlying c) = c := by
  have hfac : Spec.map p.stalkHom ≫ X.left.fromSpecStalk p.underlying = p.left :=
    (SpecToEquivOfLocalRing X.left ↧ℂ).symm_apply_apply p.left
  have hid : CommRingCat.ofHom (HodgeLean.Foundations.Curves.stalkC p.underlying) ≫
      p.stalkHom = 𝟙 (CommRingCat.of ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id,
      ← HodgeLean.Foundations.Curves.fromSpecStalk_comp_hom' p.underlying,
      ← Category.assoc, hfac, Over.w p]
    rfl
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f.hom c) hid

/-- Every actual complex point of the smooth projective curve has a single stalk
parameter giving finite scalar expansions to all orders.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10, parameter expansions. -/
theorem s2e_smooth_curve_stalk_jet_expansions
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    ∃ t : X.left.presheaf.stalk p.underlying,
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) = Ideal.span {t} ∧
      ∀ (N : ℕ) (r : X.left.presheaf.stalk p.underlying), ∃ c : Fin N → ℂ,
        r - ∑ i : Fin N, HodgeLean.Foundations.Curves.stalkC p.underlying (c i) *
          t ^ (i : ℕ) ∈ Ideal.span {t ^ N} := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  let φ : R →ₐ[ℂ] ℂ :=
    { toRingHom := p.stalkHom.hom
      commutes' := fun c => by
        change p.stalkHom.hom (HodgeLean.Foundations.Curves.stalkC p.underlying c) = c
        exact s2e_complex_point_stalk_constants X p c }
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion (p.left ≫ X.hom) := by
    rw [Over.w p]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion p.left := IsClosedImmersion.of_comp p.left X.hom
  have hP : IsClosed ({p.underlying} : Set X.left) := by
    change IsClosed {p.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using p.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  have hcoh := HodgeLean.Foundations.Curves.coheight_eq_one_of_isClosed X p.underlying hP
  letI : IsDiscreteValuationRing R := HodgeLean.Foundations.Curves.isDVR_stalk (X := X) hcoh
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal R)).principal
  refine ⟨t, ht, ?_⟩
  intro N r
  simpa only [RingHom.algebraMap_toAlgebra] using s2e_local_parameter_jet_expansion R φ t ht N r

/-- The stalk at each actual complex point of the smooth projective curve is a DVR.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeLean.Foundations.Curves.isDVR_stalk. -/
theorem s2e_smooth_curve_point_stalk_dvr
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    IsDiscreteValuationRing (X.left.presheaf.stalk p.underlying) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsClosedImmersion (p.left ≫ X.hom) := by
    rw [Over.w p]
    change IsClosedImmersion (𝟙 (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion p.left := IsClosedImmersion.of_comp p.left X.hom
  have hP : IsClosed ({p.underlying} : Set X.left) := by
    change IsClosed {p.left (IsLocalRing.closedPoint ℂ)}
    simpa only [Set.image_singleton] using p.left.isClosedMap {IsLocalRing.closedPoint ℂ}
      (IsLocalRing.isClosed_singleton_closedPoint ℂ)
  exact HodgeLean.Foundations.Curves.isDVR_stalk (X := X)
    (HodgeLean.Foundations.Curves.coheight_eq_one_of_isClosed X p.underlying hP)

/-- Actual smooth curve stalks have unique scalar expansions of finite jets in
one uniformizer, with no restriction on the multiplicity to be retained.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10, parameter expansions. -/
theorem s2e_smooth_curve_stalk_unique_jet_expansions
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    ∃ t : X.left.presheaf.stalk p.underlying, Irreducible t ∧
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) = Ideal.span {t} ∧
      ∀ (N : ℕ) (r : X.left.presheaf.stalk p.underlying), ∃! c : Fin N → ℂ,
        r - ∑ i : Fin N, HodgeLean.Foundations.Curves.stalkC p.underlying (c i) *
          t ^ (i : ℕ) ∈ Ideal.span {t ^ N} := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  let φ : R →ₐ[ℂ] ℂ :=
    { toRingHom := p.stalkHom.hom
      commutes' := fun c => by
        change p.stalkHom.hom (HodgeLean.Foundations.Curves.stalkC p.underlying c) = c
        exact s2e_complex_point_stalk_constants X p c }
  letI : IsDiscreteValuationRing R := s2e_smooth_curve_point_stalk_dvr X p
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal R)).principal
  have hirr : Irreducible t := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
  have hreg : Function.Injective (fun x : R => t * x) := by
    intro x y h
    exact mul_left_cancel₀ hirr.ne_zero h
  refine ⟨t, hirr, ht, ?_⟩
  intro N r
  simpa only [RingHom.algebraMap_toAlgebra] using
    s2e_local_parameter_jet_expansion_unique R φ t ht hreg N r

/-- All finite infinitesimal neighbourhoods in an actual smooth curve stalk have
polynomial parameter coordinates over ℂ.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10, parameter expansions. -/
theorem s2e_smooth_curve_stalk_finite_jet_coordinates
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] (p : ComplexPoint X) :
    let R := X.left.presheaf.stalk p.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    ∃ t : R, Irreducible t ∧ IsLocalRing.maximalIdeal R = Ideal.span {t} ∧
      ∀ N : ℕ, Nonempty ((Polynomial ℂ ⧸ Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)})
        ≃ₐ[ℂ] (R ⧸ Ideal.span {t ^ N})) := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  let φ : R →ₐ[ℂ] ℂ :=
    { toRingHom := p.stalkHom.hom
      commutes' := fun c => by
        change p.stalkHom.hom (HodgeLean.Foundations.Curves.stalkC p.underlying c) = c
        exact s2e_complex_point_stalk_constants X p c }
  obtain ⟨t, hirr, ht, _⟩ := s2e_smooth_curve_stalk_unique_jet_expansions X p
  have hreg : Function.Injective (fun x : R => t * x) := by
    intro x y h
    exact mul_left_cancel₀ hirr.ne_zero h
  exact ⟨t, hirr, ht, fun N => ⟨s2e_parameter_jet_algEquiv R φ t ht hreg N⟩⟩

end HodgeLean.Foundations.Program
