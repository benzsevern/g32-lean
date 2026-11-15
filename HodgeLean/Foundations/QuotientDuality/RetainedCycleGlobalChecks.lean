import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs
import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeLean.RealDefs.Port.AlgebraicGeometry.Cycle.Component.PointPurity
import HodgeLean.Foundations.Program.CompensationProductChecks

/-! # Global classes and middle-degree retained restriction

A compact intrinsic curve supplies a global orientation and a nonzero supported class.
Its square supplies an integral projective surface and degree-two restriction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves
open scoped CategoryTheory.MonObj
open MonoidalCategory CategoryTheory.CartesianMonoidalCategory
namespace HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalChecks

private abbrev C := E
private abbrev CT := a3b4_an C.hom
private def y : ComplexPoint C := η[C]
private abbrev fullPair := TopPair.ofSubset ((Set.univ : Set CT)ᶜ)
private def w : RelativeHomology ℚ fullPair 2 :=
  (j5c_exists_complexFundamentalClass C 1).choose
private theorem w_local : ∀ z : ComplexPoint C,
    relativeHomologyMap ℚ 2 (supportInclusionPairMap (X := CT)
      (Set.singleton_subset_iff.mpr (Set.mem_univ z))) w = complexLocalOrientation C 1 z :=
  (j5c_exists_complexFundamentalClass C 1).choose_spec
private def α : CohomologyWithSupport ℚ CT Set.univ 2 :=
  relativeCohomologyMap ℚ 2 (supportInclusionPairMap (X := CT)
    (Set.singleton_subset_iff.mpr (Set.mem_univ y))) (analyticPointLocalCoclass C 1 y)
private theorem evaluation : relativeCohomologyEquivDualHomology ℚ fullPair 2 α w = 1 := by
  rw [α, relativeCohomologyEquivDualHomology_relativeCohomologyMap, w_local]
  exact analyticPointLocalCoclass_apply_localClass C 1 y
private theorem α_ne : α ≠ 0 := by
  intro h
  have he := evaluation
  rw [h, map_zero, LinearMap.zero_apply] at he
  exact zero_ne_one he
private def a : Cohomology ℚ CT 2 := forgetSupport ℚ CT Set.univ 2 α
private theorem a_ne : a ≠ 0 := by
  intro h
  exact α_ne ((wholeSupportCohomologyLinearEquiv ℚ CT 2).injective
    (h.trans (map_zero _).symm))

private instance fullProjectionIso : IsIso (relativeHomologyProjection ℚ fullPair 2) := by
  change IsIso (relativeHomologyProjection ℚ (TopPair.ofSubset ((Set.univ : Set CT)ᶜ)) 2)
  rw [Set.compl_univ]
  exact (homologyEmptySubspaceIso ℚ CT 2).isIso_hom
private def c : Homology ℚ CT 2 := (asIso (relativeHomologyProjection ℚ fullPair 2)).inv.hom w
private theorem c_projection : (relativeHomologyProjection ℚ fullPair 2).hom c = w := by
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (asIso (relativeHomologyProjection ℚ fullPair 2))) w
private theorem integral : orientationIntegral CT 2 c a = 1 := by
  change cohomologyEquivDualHomology ℚ CT 2 (forgetSupport ℚ CT Set.univ 2 α) c = 1
  rw [cohomologyEquivDualHomology_forgetSupport, c_projection]
  exact evaluation

/-- The compact cubic has a global fundamental class and supported integration value one;
reversing the global orientation changes that value.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and section 3.3.
HC no distance; AV milestone no distance. -/
private theorem check_global_supported_integration :
    (∀ z : ComplexPoint C, relativeHomologyMap ℚ 2
      (supportInclusionPairMap (X := CT)
        (Set.singleton_subset_iff.mpr (Set.mem_univ z)))
        ((relativeHomologyProjection ℚ fullPair 2).hom c) = complexLocalOrientation C 1 z) ∧
    α ≠ 0 ∧ a ≠ 0 ∧ orientationIntegral CT 2 c a = 1 ∧
    orientationIntegral CT 2 (-c) a ≠ 1 := by
  refine ⟨?_, α_ne, a_ne, integral, ?_⟩
  · rw [c_projection]
    exact w_local
  · change cohomologyEquivDualHomology ℚ CT 2 a (-c) ≠ 1
    rw [map_neg]
    change -(orientationIntegral CT 2 c a) ≠ 1
    rw [integral]
    norm_num
example := check_global_supported_integration

private abbrev intrinsicCurve := intrinsicComponent C (genericPoint C.left)
private instance intrinsicSurjective : Surjective (cycleComponentι C.left (genericPoint C.left)) := by
  constructor
  rw [← Set.range_eq_univ, range_cycleComponentι, genericPoint_closure]
private instance intrinsicIso : IsIso (cycleComponentι C.left (genericPoint C.left)) :=
  isIso_of_isClosedImmersion_of_surjective _
private instance intrinsicOverIso : IsIso (intrinsicComponentInclusion C (genericPoint C.left)) := by
  letI : IsIso ((Over.forget (Spec ↧ℂ)).map
      (intrinsicComponentInclusion C (genericPoint C.left))) := by
    change IsIso (cycleComponentι C.left (genericPoint C.left))
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (Spec ↧ℂ))
private def intrinsicInclusion : a3b4_an intrinsicCurve.hom ⟶ CT :=
  TopCat.ofHom (Point.continuousMap (intrinsicComponentInclusion C (genericPoint C.left)))
private def intrinsicInverse : CT ⟶ a3b4_an intrinsicCurve.hom :=
  TopCat.ofHom (Point.continuousMap
    (asIso (intrinsicComponentInclusion C (genericPoint C.left))).inv)
private theorem intrinsic_inverse_inclusion : intrinsicInverse ≫ intrinsicInclusion = 𝟙 CT := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change Point.map ((asIso (intrinsicComponentInclusion C (genericPoint C.left))).inv ≫
    (asIso (intrinsicComponentInclusion C (genericPoint C.left))).hom) z = z
  rw [Iso.inv_hom_id]
  rfl
private def intrinsicFundamental : Homology ℚ (a3b4_an intrinsicCurve.hom) 2 :=
  homologyMap ℚ 2 intrinsicInverse c
private def intrinsicSupported :
    CohomologyWithSupport ℚ (a3b4_an intrinsicCurve.hom) Set.univ 2 :=
  (wholeSupportCohomologyLinearEquiv ℚ (a3b4_an intrinsicCurve.hom) 2).symm
    (s2e_pullback ℚ (intrinsicComponentInclusion C (genericPoint C.left)) 2 a)
private theorem intrinsic_integral :
    orientationIntegral (a3b4_an intrinsicCurve.hom) 2 intrinsicFundamental
      (forgetSupport ℚ (a3b4_an intrinsicCurve.hom) Set.univ 2 intrinsicSupported) = 1 := by
  change cohomologyEquivDualHomology ℚ (a3b4_an intrinsicCurve.hom) 2
    ((wholeSupportCohomologyLinearEquiv ℚ (a3b4_an intrinsicCurve.hom) 2) intrinsicSupported)
      intrinsicFundamental = 1
  rw [intrinsicSupported, LinearEquiv.apply_symm_apply]
  change cohomologyEquivDualHomology ℚ (a3b4_an intrinsicCurve.hom) 2
    (cohomologyMap ℚ 2 intrinsicInclusion a) (homologyMap ℚ 2 intrinsicInverse c) = 1
  rw [cohomologyEquivDualHomology_cohomologyMap,
    ← LinearMap.comp_apply (homologyMap ℚ 2 intrinsicInclusion) (homologyMap ℚ 2 intrinsicInverse),
    ← homologyMap_comp, intrinsic_inverse_inclusion, homologyMap_id, LinearMap.id_apply]
  exact integral

/-- Global integration on an actual reduced intrinsic component uses the transported
fundamental class and a nonzero supported class; its orientation reversal is rejected.
Source: Hatcher, section 3.3; Hartshorne, II.3, reduced induced components.
HC no distance; AV milestone no distance. -/
theorem check_intrinsic_global_supported_integration :
    intrinsicFundamental ≠ 0 ∧ intrinsicSupported ≠ 0 ∧
    orientationIntegral (a3b4_an intrinsicCurve.hom) 2 intrinsicFundamental
      (forgetSupport ℚ (a3b4_an intrinsicCurve.hom) Set.univ 2 intrinsicSupported) = 1 ∧
    orientationIntegral (a3b4_an intrinsicCurve.hom) 2 (-intrinsicFundamental)
      (forgetSupport ℚ (a3b4_an intrinsicCurve.hom) Set.univ 2 intrinsicSupported) ≠ 1 := by
  refine ⟨?_, ?_, intrinsic_integral, ?_⟩
  · intro h
    have he := intrinsic_integral
    change cohomologyEquivDualHomology ℚ _ 2 _ intrinsicFundamental = 1 at he
    rw [h, map_zero] at he
    exact zero_ne_one he
  · intro h
    have he := intrinsic_integral
    rw [h, map_zero, map_zero] at he
    exact zero_ne_one he
  · change cohomologyEquivDualHomology ℚ _ 2 _ (-intrinsicFundamental) ≠ 1
    rw [map_neg]
    change -(orientationIntegral _ 2 intrinsicFundamental _) ≠ 1
    rw [intrinsic_integral]
    norm_num
example := check_intrinsic_global_supported_integration

private abbrev surface := C ⊗ C
private abbrev ST := a3b4_an surface.hom
private def projection : surface ⟶ C := fst C C
private def diagonal : C ⟶ surface := lift (𝟙 C) (𝟙 C)
private theorem diagonal_projection : diagonal ≫ projection = 𝟙 C := by
  simp only [diagonal, projection, lift_fst]
private def b : Cohomology ℚ ST 2 := s2e_pullback ℚ projection 2 a
private theorem b_ne : b ≠ 0 := by
  intro h
  have he := congrArg (s2e_pullback ℚ diagonal 2) h
  have hcomp : s2e_pullback ℚ diagonal 2 (s2e_pullback ℚ projection 2 a) = a := by
    unfold s2e_pullback
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    change cohomologyMap ℚ 2 (TopCat.ofHom (Point.continuousMap (diagonal ≫ projection))) a = a
    rw [diagonal_projection]
    exact LinearMap.congr_fun (cohomologyMap_id ℚ CT 2) a
  exact a_ne (hcomp.symm.trans (he.trans (map_zero _)))
private def β : CohomologyWithSupport ℚ ST Set.univ 2 :=
  (wholeSupportCohomologyLinearEquiv ℚ ST 2).symm b
private theorem β_ne : β ≠ 0 := by
  intro h
  apply b_ne
  have he := congrArg (wholeSupportCohomologyLinearEquiv ℚ ST 2) h
  simpa only [β, LinearEquiv.apply_symm_apply, map_zero] using he
private def tower : surface ⟶ surface := retainedCycleModification
  (fun _ : Fin 2 => surface) (Iso.refl surface) (Iso.refl surface)
  (fun _ : Fin 1 => 𝟙 surface)
private theorem tower_eq : tower = 𝟙 surface := by
  simp only [tower, retainedCycleModification, s2e_towerTotalMap,
    Iso.refl_inv, Category.id_comp]
  rfl

private def V : TopologicalSpace.Opens (ComplexPoint surface) := ⊤
private def j : TopCat.of V ⟶ ST := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
private def r : ST ⟶ TopCat.of V := TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ _⟩, by fun_prop⟩
private theorem restriction_ne : cohomologyWithSupportMap ℚ 2 j Set.univ β ≠ 0 := by
  intro h
  have he := congrArg (cohomologyWithSupportMap ℚ 2 r Set.univ) h
  have hi : cohomologyWithSupportMap ℚ 2 r Set.univ
      (cohomologyWithSupportMap ℚ 2 j Set.univ β) = β := by
    let J : TopPair.ofSubset ((Set.univ : Set (TopCat.of V))ᶜ) ⟶
        TopPair.ofSubset ((Set.univ : Set ST)ᶜ) := preimageSupportPairMap j Set.univ
    let R : TopPair.ofSubset ((Set.univ : Set ST)ᶜ) ⟶
        TopPair.ofSubset ((Set.univ : Set (TopCat.of V))ᶜ) := preimageSupportPairMap r Set.univ
    change relativeCohomologyMap ℚ 2 R (relativeCohomologyMap ℚ 2 J β) = β
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
    change relativeCohomologyMap ℚ 2 (𝟙 (TopPair.ofSubset ((Set.univ : Set ST)ᶜ))) β = β
    rw [relativeCohomologyMap_id, LinearMap.id_apply]
  exact β_ne (hi.symm.trans (he.trans (map_zero _)))

/-- The cubic product tower has dimension two and nonzero degree-two supported restriction.
Its specified local transport satisfies the restriction square; zero transport fails.
Source: Hartshorne, II.3.20; Hatcher, section 3.1, naturality for maps of pairs.
HC no distance; AV milestone no distance. -/
theorem check_even_middle_retained_transport :
    TopologicalSpace.dim surface.left = 2 * (1 : ℕ) ∧
    tower = 𝟙 surface ∧
    ∃ hV : IsHomeomorph (retainedOpenMap tower V),
      let XU := TopCat.of (Point.map tower ⁻¹' (V : Set (ComplexPoint surface)))
      let jX : XU ⟶ ST := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      (cohomologyWithSupportMap ℚ (2 * 1) j Set.univ).comp
          (LinearMap.id : CohomologyWithSupport ℚ ST Set.univ (2 * 1) →ₗ[ℚ]
            CohomologyWithSupport ℚ ST Set.univ (2 * 1)) =
        (retainedLocalTransport tower Set.univ Set.univ
          (by intro _ _; trivial) V hV (2 * 1)).comp
          (cohomologyWithSupportMap ℚ (2 * 1) jX Set.univ) ∧
      cohomologyWithSupportMap ℚ (2 * 1) j Set.univ β ≠ 0 := by
  refine ⟨?_, tower_eq, ?_⟩
  · exact cp_cubic_surface_dim
  · rw [tower_eq]
    let hV : IsHomeomorph (retainedOpenMap (𝟙 surface) V) := IsHomeomorph.id
    refine ⟨hV, ?_, restriction_ne⟩
    dsimp only
    rw [LinearMap.comp_id]
    unfold retainedLocalTransport supportHomeomorphTransfer enlargeSupport cohomologyWithSupportMap
    dsimp only
    rw [LinearMap.comp_assoc, ← relativeCohomologyMap_comp, ← relativeCohomologyMap_comp]
    congr 1
    ext z
    · exact (z.2 trivial).elim
    · exact congrArg Subtype.val ((hV.homeomorph (retainedOpenMap (𝟙 surface) V)).apply_symm_apply z).symm
example := check_even_middle_retained_transport

#print axioms w_local
#print axioms evaluation
#print axioms α_ne
#print axioms a_ne
#print axioms c_projection
#print axioms integral
#print axioms check_global_supported_integration
#print axioms intrinsic_inverse_inclusion
#print axioms intrinsic_integral
#print axioms check_intrinsic_global_supported_integration
#print axioms diagonal_projection
#print axioms b_ne
#print axioms β_ne
#print axioms tower_eq
#print axioms restriction_ne
#print axioms check_even_middle_retained_transport

end HodgeLean.Foundations.QuotientDuality.RetainedCycleGlobalChecks
