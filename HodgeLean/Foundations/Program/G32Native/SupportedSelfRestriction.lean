import HodgeLean.Foundations.BundleThom.ImmersionDefs

/-! # Supported self-restriction on the retained immersion

The oriented tubular comparison is an explicit geometric input. The supported
class and the analytic dual conormal belong to the same immersion.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular Bundle TopologicalSpace
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.BundleThom

private theorem relativeToAbsolute_naturality
    {A B : TopPair} (f : A ⟶ B) (n : ℕ) (u : RelativeCohomology ℚ B n) :
    relativeCohomologyToAbsolute ℚ A n (relativeCohomologyMap ℚ n f u) =
      cohomologyMap ℚ n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute ℚ B n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun a => HomologicalComplex.homologyMap a n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact ConcreteCategory.congr_hom hhom u

/-- Self-restriction of the supplied normalized class equals the independent normal Euler.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6; Fulton,
Intersection Theory, §6.3, Corollary 6.3, algebraic analogue. -/
theorem g32w12_supported_selfRestriction_eq_bundleEuler
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (V : Scheme) (v : V ⟶ W.left) [IsOpenImmersion v]
    (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
    [SmoothOfRelativeDimension k Q.hom]
    [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
    [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]
    (hcomparison :
      letI (x : ComplexPoint Q) := i1_normalFibreTopology j x
      letI := i1_normalTotalTopology j k
      let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
      letI := N.fiberBundle
      letI := N.vectorBundle
      ∃ (U : Opens (TotalSpace (Fin k → ℂ) (i1_normalFibre j)))
        (T : Opens (ComplexPoint (Over.mk (v ≫ W.hom)))) (h : U ≃ₜ T),
        (∀ x : ComplexPoint Q, zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ U) ∧
        (∀ (x : ComplexPoint Q) (hx : zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ U),
          (h ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hx⟩).1 =
            Point.map (i1_smoothLift ι v j hj) x) ∧
        ∃ hs : ∀ z : U,
          i1_tubularAmbientMap v j k U T h z ∈
            a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ z.1.2 = 0,
          relativeCohomologyMap ℚ (2 * k)
            (i1_neighbourhoodPairMap k (i1_normalFibre j) U
              (X := TopCat.of (ComplexPoint W))
              (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ))
              (i1_tubularAmbientMap v j k U T h)
              (fun z hz hmem => hz ((hs z).mp hmem))) c =
          relativeCohomologyMap ℚ (2 * k)
            (i1_neighbourhoodInclusion k (i1_normalFibre j) U)
            (i1_bundleThom k (i1_normalFibre j))
    ) :
    s2e_normalEuler ι k c =
      i1_normalBundleEuler j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj)) := by
  letI (x : ComplexPoint Q) : TopologicalSpace (i1_normalFibre j x) :=
    i1_normalFibreTopology j x
  letI : TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
    i1_normalTotalTopology j k
  let N := i1_analyticNormal j k (v ≫ W.hom) (Over.w (i1_smoothLift ι v j hj))
  letI := N.fiberBundle
  letI := N.vectorBundle
  obtain ⟨U, T, h, hU, hzero, hs, hclass⟩ :=
    hcomparison
  let z : C(ComplexPoint Q, U) :=
    ⟨fun x => ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hU x⟩,
      (i1_zeroSection k (i1_normalFibre j)).continuous.subtype_mk _⟩
  let f := i1_neighbourhoodPairMap k (i1_normalFibre j) U
    (X := TopCat.of (ComplexPoint W))
    (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ))
    (i1_tubularAmbientMap v j k U T h) (fun a ha hm => ha ((hs a).mp hm))
  have hfac : i1_smoothLift ι v j hj ≫ Over.homMk v rfl = ι := by
    apply Over.OverMorphism.ext
    exact hj
  have hleft : TopCat.ofHom z ≫ TopPair.Hom.fst f =
      TopCat.ofHom (Point.continuousMap ι) := by
    apply ConcreteCategory.hom_ext
    intro x
    change Point.map (Over.homMk v rfl) (h (z x)).1 = Point.map ι x
    change Point.map (Over.homMk v rfl)
      (h ⟨zeroSection (Fin k → ℂ) (i1_normalFibre j) x, hU x⟩).1 = _
    rw [hzero x (hU x)]
    change Point.map (i1_smoothLift ι v j hj ≫ Over.homMk v rfl) x = _
    rw [hfac]
  have hright : TopCat.ofHom z ≫
      TopPair.Hom.fst (i1_neighbourhoodInclusion k (i1_normalFibre j) U) =
      TopCat.ofHom (i1_zeroSection k (i1_normalFibre j)) := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have heq := congrArg (fun a => cohomologyMap ℚ (2 * k) (TopCat.ofHom z)
    (relativeCohomologyToAbsolute ℚ (i1_neighbourhoodPair k (i1_normalFibre j) U)
      (2 * k) a)) hclass
  rw [relativeToAbsolute_naturality f, relativeToAbsolute_naturality] at heq
  change cohomologyMap ℚ (2 * k) (TopCat.ofHom z)
      (cohomologyMap ℚ (2 * k) (TopPair.Hom.fst f)
        (s2e_classToAbsolute W _ k c)) =
    cohomologyMap ℚ (2 * k) (TopCat.ofHom z)
      (cohomologyMap ℚ (2 * k)
        (TopPair.Hom.fst (i1_neighbourhoodInclusion k (i1_normalFibre j) U))
        (forgetSupport ℚ (i1_totalSpace k (i1_normalFibre j))
          (i1_zeroSupport k (i1_normalFibre j)) (2 * k)
          (i1_bundleThom k (i1_normalFibre j)))) at heq
  have hl := LinearMap.congr_fun (cohomologyMap_comp ℚ (2 * k)
    (TopCat.ofHom z) (TopPair.Hom.fst f)) (s2e_classToAbsolute W _ k c)
  have hr := LinearMap.congr_fun (cohomologyMap_comp ℚ (2 * k)
    (TopCat.ofHom z) (TopPair.Hom.fst (i1_neighbourhoodInclusion k (i1_normalFibre j) U)))
    (forgetSupport ℚ (i1_totalSpace k (i1_normalFibre j))
      (i1_zeroSupport k (i1_normalFibre j)) (2 * k)
      (i1_bundleThom k (i1_normalFibre j)))
  rw [hleft] at hl
  rw [hright] at hr
  exact hl.trans (heq.trans hr.symm)

#print axioms g32w12_supported_selfRestriction_eq_bundleEuler

example {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] (ι : Q ⟶ W) (k : ℕ) :
    s2e_normalEuler ι k 0 = 0 := by
  simp only [s2e_normalEuler, map_zero]

end HodgeLean.Foundations.BundleThom
