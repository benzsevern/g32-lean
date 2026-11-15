import HodgeLean.Foundations.Program.G32Native.JointProjectiveTubeTransport

/-! # Projective ambient supplier for the U2 normal calculation

The metric comes from the restricted projector. The general tube theorems retain
their original interfaces and are not used in this assembly.
HC no distance; AV milestone no distance. -/

open HodgeLean.Foundations.TubularEuler HodgeLean.Foundations.BundleThom
open scoped Manifold ContDiff

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace Bundle AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
variable [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]

private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j k

/-- Oriented tubular transport of the supplied normalized immersion class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, tubular neighbourhood
and Thom class; Fulton, Intersection Theory, §6.3, algebraic analogue.
HC no distance; AV milestone no distance. -/
theorem joint_projective_presentation_support_comparison
    (hNormalField : ∀ {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
      [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
      [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
      (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
      {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
      (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
      [SmoothOfRelativeDimension k Q.hom]
      [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)],
    letI : IsClosedImmersion (i1_smoothLift ι v j hj).left := by
      change IsClosedImmersion j
      infer_instance
    letI : SmoothOfRelativeDimension (k + k) (Over.mk (v ≫ W.hom)).hom :=
      ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
    ∀ (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint (Over.mk (v ≫ W.hom)))
      (hz : Point.map (i1_smoothLift ι v j hj) x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift ι v j hj) (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift ι v j hj) (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) (k + k)) (n : ℕ)
    (emb : ComplexPoint (Over.mk (v ≫ W.hom)) → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb),
    Nonempty (RetainedEuclideanNormalField ι k v j hj n emb g))
    (nP : ℕ)
    (e : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (nP+1)) (Spec ↧ℂ)))
    [IsImmersion e.left]
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
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
          (i1_bundleThom k (i1_normalFibre j))  :=
  joint_projective_tubular_support_comparison ι k v j hj hNormalField nP e c hc

/-- Oriented tubular transport of the supplied normalized immersion class.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, tubular neighbourhood
and Thom class; Fulton, Intersection Theory, §6.3, algebraic analogue.
HC no distance; AV milestone no distance. -/
theorem joint_projective_support_comparison
    (hNormalField : ∀ {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
      [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
      [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
      (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
      {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
      (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
      [SmoothOfRelativeDimension k Q.hom]
      [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)],
    letI : IsClosedImmersion (i1_smoothLift ι v j hj).left := by
      change IsClosedImmersion j
      infer_instance
    letI : SmoothOfRelativeDimension (k + k) (Over.mk (v ≫ W.hom)).hom :=
      ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
    ∀ (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint (Over.mk (v ≫ W.hom)))
      (hz : Point.map (i1_smoothLift ι v j hj) x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift ι v j hj) (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift ι v j hj) (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) (k + k)) (n : ℕ)
    (emb : ComplexPoint (Over.mk (v ≫ W.hom)) → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb),
    Nonempty (RetainedEuclideanNormalField ι k v j hj n emb g)) [IsProjective W.hom]
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c) :
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
          (i1_bundleThom k (i1_normalFibre j))  := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := W.hom)
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  let e : W ⟶ Over.mk
      (ProjectiveSpace.toBase (Fin (P.ambientDimension+1)) (Spec ↧ℂ)) :=
    Over.homMk P.immersion P.immersion_toBase
  letI : IsImmersion e.left := inferInstanceAs (IsImmersion P.immersion)
  exact joint_projective_tubular_support_comparison ι k v j hj hNormalField P.ambientDimension e c hc

#print axioms joint_projective_presentation_support_comparison
#print axioms joint_projective_support_comparison
end HodgeLean.Foundations.TubularEuler
