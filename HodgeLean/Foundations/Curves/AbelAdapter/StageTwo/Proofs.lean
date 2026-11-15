import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.Checks
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.IntegralAbelNaturality
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.SchemeFormReconstruction
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.InvariantSchemeForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.CoverDifferential
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.ThetaCoverValues
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelInvariantDifferential

/-! # Integral, translation and differential interfaces for the Abel adapter

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program HodgeLean.Foundations.IntegralHomology
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- Integral singular homology comparison for the actual algebraic Abel map.
Source: Birkenhake–Lange, §11.4; Forster, §21; Hatcher, §2.1.
HC no distance; AV milestone no distance. -/
theorem integralAbelSquare_aux
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [ChartedSpace E (ComplexPoint X)] [IsManifold 𝓘(ℂ, E) ω (ComplexPoint X)]
    [ConnectedSpace (ComplexPoint X)] (h : Module.finrank ℂ E = 1)
    (p : ComplexPoint X) (j : X ⟶ model h)
    (hj : ∀ x, Point.map j x = modelAbel h p x) :
    ∃ eC : IntegralHomology.Lattice (TopCat.of (ComplexPoint X)) ≃ₗ[ℤ] b3_periodLattice E (ComplexPoint X),
    ∃ eJ : IntegralHomology.Lattice (TopCat.of (ComplexPoint (model h))) ≃ₗ[ℤ]
        abelianPeriodLattice (model (C := ComplexPoint X) h),
      (∀ c : b3_SmoothLoop E (ComplexPoint X), eC (loopClass c) = b3_latticePeriod _ _ c) ∧
      (∀ l : abelianPeriodLattice (model (C := ComplexPoint X) h),
        eJ (Submodule.Quotient.mk ((ZChains _).homologyπ 1
          (((ZChains _).sc 1).moduleCatCyclesIso.inv
            (loopCycle ℤ (abelianLatticeLoop (model h) l))))) = l) ∧
      (∀ a, eJ (mapLattice (pointMap j) a) = modelPeriod h (eC a)) := by
  letI : IsCommMonObj (model (C := ComplexPoint X) h) :=
    HodgeLean.Foundations.isCommMonObj_of_complexSelfProductIntegral _
      (HodgeLean.Foundations.complexSelfProductIntegral_of_isIntegral _)
  refine ⟨curvePeriodEquiv h p, abelianIntegralPeriodEquiv (model h),
    curvePeriodEquiv_loop h p, abelianIntegralPeriod_loop (model h), ?_⟩
  intro a
  exact integralAbel_period_natural X h p j hj a

example := integralAbelSquare_example

/-- Scheme translation and centering retain the pointwise equations.
Source: Mumford, Abelian Varieties, §1; Birkenhake–Lange, §11.4.
HC no distance; AV milestone no distance. -/
theorem translationPoint_aux {X A : Over (Spec ↧ℂ)} [GrpObj A] [IsProper A.hom]
    (f : X ⟶ A) (p : ComplexPoint X) :
    (∀ a x : ComplexPoint A, Point.map (translation A a).hom x = x * a) ∧
      Point.map (centered f p) p = 1 ∧
      centered f p ≫ (translation A (Point.map f p)).hom = f := by
  have ht (a x : ComplexPoint A) : Point.map (translation A a).hom x = x * a := by
    change x ≫ (CategoryTheory.CartesianMonoidalCategory.lift (𝟙 A)
      (CategoryTheory.SemiCartesianMonoidalCategory.toUnit A ≫ a) ≫ MonObj.mul) =
        CategoryTheory.CartesianMonoidalCategory.lift x a ≫ MonObj.mul
    rw [← Category.assoc, CategoryTheory.CartesianMonoidalCategory.comp_lift]
    congr 1
    ext <;> simp
  refine ⟨ht, ?_, ?_⟩
  · rw [centered, Point.map_comp_apply, ht, mul_inv_cancel]
  · change (f ≫ (translation A (Point.map f p)).inv) ≫
        (translation A (Point.map f p)).hom = f
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

example := translationPoint_example

/-- Actual translations preserve the specified rational degree-one pullback.
Source: Hatcher, Theorem 2.10; ccm8_translation_pullback.
HC no distance; AV milestone no distance. -/
theorem translationH1_aux (A : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] (a : ComplexPoint A) :
    homPullback (translation A a).hom 1 = LinearMap.id := by
  apply LinearMap.ext
  intro c
  exact ccm8_translation_pullback A a 1 c

example := translationH1_example

/-- The centered factorization yields the literal contravariant H¹ square.
Source: Birkenhake–Lange, §11.4; spec_homPullback_comp.
HC no distance; AV milestone no distance. -/
theorem factorH1_aux {X J A : Over (Spec ↧ℂ)} [GrpObj A]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (f : X ⟶ A) (p : ComplexPoint X) (j : X ⟶ J) (π : J ⟶ A)
    (hπ : j ≫ π = centered f p) :
    homPullback f 1 = (homPullback j 1).comp (homPullback π 1) ∧
      (Function.Injective (homPullback f 1) → Function.Injective (homPullback π 1)) := by
  have hc : homPullback (centered f p) 1 = homPullback f 1 := by
    rw [centered, spec_homPullback_comp, translationH1_aux, LinearMap.comp_id]
  have hs : homPullback f 1 = (homPullback j 1).comp (homPullback π 1) := by
    rw [← hc, ← hπ, spec_homPullback_comp]
  refine ⟨hs, ?_⟩
  intro hf x y hxy
  apply hf
  rw [hs]
  exact congrArg (homPullback j 1) hxy


example := factorH1_example

/-- Construct the scheme-form coordinate comparison using literal tangent values.
Source: Griffiths–Harris, chapter 0 §2; Forster, §9.
HC no distance; AV milestone no distance. -/
theorem schemeCoordinates_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ φ : GlobalHolomorphicForm X 1 ≃+
        b3_HolForm (Fin (TopologicalSpace.dim X.left) → ℂ) (ComplexPoint X),
      ∀ θ, (φ θ).val = schemeForm X θ := by
  let φ := AddEquiv.ofBijective (schemeFormHolHom X)
    ⟨schemeFormHolHom_injective X, schemeFormHolHom_surjective X⟩
  exact ⟨φ, fun _ ↦ rfl⟩

example := schemeCoordinates_example

/-- Invariant covectors on the retained theta model differentiate the selected Abel map.
Source: Birkenhake–Lange, §11.4; Forster, §21.
HC no distance; AV milestone no distance. -/
theorem invariantDifferential_aux
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (h : Module.finrank ℂ E = 1) (p : C) :
    letI := b3_periodLattice_finite (C := C) h
    letI := b3_periodLattice_free (E := E) (C := C)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
    ∃ ψ : b3_HolForm E C ≃+ GlobalHolomorphicForm (model (C := C) h) 1,
      (∀ (θ : b3_HolForm E C) (z v : b3Rest2_VJ E C),
        globalOneFormCovector (model h) _ (ψ θ)
          (theta h (b3Rest2_covHom z))
          (mfderiv 𝓘(ℂ, b3Rest2_VJ E C)
            𝓘(ℂ, Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
            (theta h ∘ b3Rest2_covHom) z v) = periodCovector h θ v) ∧
      (∀ θ, b3_pullback E (Fin (TopologicalSpace.dim (model (C := C) h).left) → ℂ)
        (modelAbel h p) (schemeForm (model h) (ψ θ)) = θ.val) := by
  letI := b3_periodLattice_finite (C := C) h
  letI := b3_periodLattice_free (E := E) (C := C)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := C) h)
  refine ⟨thetaSchemeFormEquiv h, thetaSchemeFormEquiv_cover h, ?_⟩
  intro θ
  rw [thetaSchemeFormEquiv_values]
  exact (thetaAnalyticForm_abel h p θ).trans
    (abelJacobi_invariant_pullback h p (analyticAbel h p)
      (b3_exists_abelJacobi (C := C) h p).choose_spec θ)

example := invariantDifferential_example

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
