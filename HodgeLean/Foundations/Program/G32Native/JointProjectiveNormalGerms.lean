import HodgeLean.Foundations.Program.G32Native.RetractedNormalCoordinateStep
import HodgeLean.Foundations.Program.G32Native.QuasiProjectiveEmbedding

/-! # Compatible normal germs from a specified projective presentation

All maps are restrictions of the same retracted Euclidean displacement.
HC no distance; AV milestone no distance. -/
open HodgeLean.Foundations.TubularEuler HodgeLean.Foundations.BundleThom
open scoped Manifold ContDiff

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Bundle
open scoped Manifold ContDiff
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom
variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension k Q.hom]
variable [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) := i1_normalTotalTopology j k
local notation "X" => Over.mk (v ≫ W.hom)
local notation "J" => i1_smoothLift ι v j hj
local notation "NT" => TotalSpace (Fin k → ℂ) (i1_normalFibre j)
local notation "zN" => zeroSection (Fin k → ℂ) (i1_normalFibre j)

private local instance liftClosed : IsClosedImmersion (J).left := by
  change IsClosedImmersion j
  infer_instance
private local instance ambientDimension : SmoothOfRelativeDimension (k + k) (X).hom :=
  ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
variable [CompactSpace (ComplexPoint Q)] [T2Space (ComplexPoint Q)]

/-- A specified projective presentation supplies the ambient embedding for normal germs.
The metric is selected from the restricted projector; its top regularity index is analytic.
The retained normal-field construction is the remaining geometric step.
Source: Griffiths–Harris, Principles of Algebraic Geometry, §0.7;
Huybrechts, Complex Geometry, §3.1;
Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24
and Proposition 6.25; `normal_coordinate_patch_of_raw_map`.
HC no distance; AV milestone no distance. -/
theorem joint_projective_normal_coordinate_germs
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
    (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
      (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k)
    (nP : ℕ)
    (e : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (nP+1)) (Spec ↧ℂ)))
    [IsImmersion e.left] :
    ∃ (U : ComplexPoint Q → Opens NT) (m : ∀ x, C(U x, ComplexPoint X)),
      (∀ x, zN x ∈ U x) ∧
      (∀ i x hx, m i ⟨zN x, hx⟩ = Point.map J x) ∧
      (Nonempty (∀ x, NormalCoordinatePatch ι k v j (U x) (m x) x)) ∧
      (∀ i l z hi hl, m i ⟨z, hi⟩ = m l ⟨z, hl⟩) := by
  classical
  letI : LocallyOfFiniteType (X).hom := by
    change LocallyOfFiniteType (v ≫ W.hom)
    infer_instance
  obtain ⟨g⟩ := ambientMetric_of_quasiProjective W v (k+k) nP e
  by_cases hn : Nonempty (ComplexPoint Q)
  · letI := hn
    letI := complexPoint_isRealAnalyticManifold X (k + k)
    letI := ambientMetric_t2Space W v
    letI := ambientMetric_secondCountable W v
    letI : LocallyCompactSpace (ComplexPoint X) :=
      ChartedSpace.locallyCompactSpace (Fin (k + k) → ℂ) (ComplexPoint X)
    letI : IsImmersion ((Over.homMk v rfl : X ⟶ W) ≫ e).left := by
      change IsImmersion (v ≫ e.left)
      infer_instance
    obtain ⟨n, emb, hemb, hinj, himm⟩ :=
      quasiProjectiveEuclideanEmbedding_exists X (k+k) nP
        ((Over.homMk v rfl : X ⟶ W) ≫ e)
    let K : Set (ComplexPoint X) := Set.range (Point.map J)
    have hK : IsCompact K := isCompact_range (Point.continuous_map J)
    have hKN : K.Nonempty := Set.range_nonempty _
    obtain ⟨C, hC, hKC, D, r, hDset, hr, hfix⟩ :=
      analyticEmbedding_retraction_near_compact emb hemb himm hinj K hK hKN
    obtain ⟨N⟩ := hNormalField ι k v j hj hD g n emb hemb
    let add : NT → EuclideanSpace ℝ (Fin n) :=
      fun z => emb (Point.map J z.proj) + N.displacement z
    have hadd : Continuous add :=
      (hemb.continuous.comp ((Point.continuous_map J).comp
        (i1_normalProjection_continuous j k))).add N.displacement.continuous
    let U : Opens NT := ⟨add ⁻¹' D, D.isOpen.preimage hadd⟩
    have hU : ∀ x, zN x ∈ U := by
      intro x
      change emb (Point.map J x) + N.displacement (zN x) ∈ D
      rw [N.zero x, add_zero]
      exact hDset ⟨Point.map J x, ⟨x, rfl⟩, rfl⟩
    let f : NT → ComplexPoint X := fun z => r (add z)
    have hf : ContinuousOn f U := hr.continuousOn.comp hadd.continuousOn (fun _ hz => hz)
    have hz : ∀ x, f (zN x) = Point.map J x := by
      intro x
      change r (emb (Point.map J x) + N.displacement (zN x)) = _
      rw [N.zero x, add_zero]
      exact hfix _ (interior_subset (hKC ⟨x, rfl⟩))
    have hzW : ∀ x, Point.map (Over.homMk v rfl : X ⟶ W) (f (zN x)) = Point.map ι x := by
      intro x
      rw [hz x, ← Point.map_comp_apply]
      exact congrArg (fun F : Q ⟶ W => Point.map F x) (Over.OverMorphism.ext hj)
    have patches : ∀ x, Nonempty (NormalCoordinatePatch ι k v j U
        ⟨fun z => f z.val, hf.domRestrict⟩ x) := by
      intro x
      obtain ⟨b, e, a, hb, he, ha, hxb, hxe, hm, hs, han, ht⟩ :=
        retracted_normal_coordinate_comparison_aux ι k v j hj g n emb hemb himm N
          C hKC D r hr hfix U (fun _ hz => hz) hU x
      exact normal_coordinate_patch_of_raw_map ι k v j U f hf hU hzW x b e a
        hb he ha hxb hxe hm hs han ht
    exact ⟨fun _ => U, fun _ => ⟨fun z => f z.val, hf.domRestrict⟩,
      hU, fun _ x _ => hz x, ⟨fun x => Classical.choice (patches x)⟩,
      fun _ _ _ _ _ => rfl⟩
  · letI : IsEmpty (ComplexPoint Q) := not_nonempty_iff.mp hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim,
      ⟨isEmptyElim⟩, isEmptyElim⟩

#print axioms joint_projective_normal_coordinate_germs
end HodgeLean.Foundations.TubularEuler
