import HodgeLean.Foundations.Program.G32Native.RetractedManifoldQuotientCoordinates
import HodgeLean.Foundations.Program.G32Native.FlattenedManifoldTangentZero
import HodgeLean.Foundations.Program.G32Native.FlatteningTransverseKernel
import HodgeLean.Foundations.Program.G32Native.RetainedConormalActualTangentKernel
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import HodgeLean.Foundations.Program.G32Native.RetainedHermitianNormalSection
import HodgeLean.Foundations.Program.G32Native.AnalyticEmbeddingCompactRetraction
import HodgeLean.Foundations.TubularEuler.RealAnalyticMetricPrerequisiteHelpers
import HodgeLean.Foundations.TubularEuler.RawNormalCoordinatePatchHelpers
import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationSectionInjectivity
import HodgeLean.Foundations.Program.G32Native.NormalFrameAdditionAnalytic
import HodgeLean.Foundations.Program.G32Native.ComplexRealManifoldRegularity

/-! # Euclidean displacement of the original metric normal vectors

The data are vectors in the embedding space, with their original conormal evaluations.
No ambient-valued normal map or coordinate patch is part of these data.
HC no distance; AV milestone no distance. -/
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
local instance retainedNormalFieldFibreTopology (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
local instance retainedNormalFieldTotalTopology :
    TopologicalSpace (TotalSpace (Fin k → ℂ) (i1_normalFibre j)) := i1_normalTotalTopology j k
local notation "X" => Over.mk (v ≫ W.hom)
local notation "J" => i1_smoothLift ι v j hj
local notation "NT" => TotalSpace (Fin k → ℂ) (i1_normalFibre j)
local notation "zN" => zeroSection (Fin k → ℂ) (i1_normalFibre j)

local instance retainedNormalFieldLiftClosed : IsClosedImmersion (J).left := by
  change IsClosedImmersion j
  infer_instance
local instance retainedNormalFieldAmbientDimension : SmoothOfRelativeDimension (k + k) (X).hom :=
  ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›

/-- A Euclidean normal field obtained by differentiating the ambient embedding
on the metric representatives of the original dual-conormal fibre.
The selected linear frames measure analytic regularity in the original total topology.
Source: Lee, Introduction to Smooth Manifolds, second edition, proof of Theorem 6.24;
Hirsch, Differential Topology, chapter 4, section 5, normal bundles.
HC no distance; AV milestone no distance. -/
structure RetainedEuclideanNormalField (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) where
  displacement : C(NT, EuclideanSpace ℝ (Fin n))
  zero : ∀ x, displacement (zN x) = 0
  frame : ∀ x : ComplexPoint Q,
    Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j))
  frame_linear : ∀ x, (frame x).IsLinear ℂ
  frame_mem : ∀ x, zN x ∈ (frame x).source
  analytic : ∀ (x : ComplexPoint Q)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ)),
    a3b4_IsHolChart Q.hom (b.trans
      ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) →
    ∀ y ∈ b.source, zN y ∈ (frame x).source →
      let P := (frame x).toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      AnalyticAt ℝ (fun q => displacement (P.symm q)) (b y, 0)
  metric_evaluation : ∀ (A : V.Opens) (hA : IsAffineOpen A)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A))
    (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
    ∃ L : i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a (L u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a w = 0) →
        g.coefficient z ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (L u) w = 0) ∧
      ∀ u, displacement ⟨x, u⟩ =
        fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ) z).symm c))
          ((chartAt (Fin (k + k) → ℂ) z) (Point.map J x)) (L u)

theorem retained_euclidean_field_conormal_injective
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) := by
  obtain ⟨L, hL, _, _⟩ := N.metric_evaluation A hA x hx z hz
  change Function.Injective (fun a : i1_conormalFibre j x =>
    retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz a)
  intro a b hab
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).mp
  intro u
  rw [map_sub, ← hL u a, ← hL u b]
  exact sub_eq_zero.mpr (DFunLike.congr_fun hab (L u))

#print axioms retained_euclidean_field_conormal_injective

theorem retained_euclidean_field_conormal_rank
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint X)
    (hz : Point.map J x ∈ (chartAt (Fin (k + k) → ℂ) z).source) :
    Function.Injective (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz)) = k := by
  let D := retainedAffineConormalDifferential X Q J (k + k) A hA x hx z hz
  have hi := retained_euclidean_field_conormal_injective ι k v j hj g n emb N A hA x hx z hz
  refine ⟨hi, ?_⟩
  letI := N.frame_linear x
  have hb : x ∈ (N.frame x).baseSet := (N.frame x).mem_source.mp (N.frame_mem x)
  exact finrank_range_of_injective_of_dual_equiv D hi k
    ((N.frame x).linearEquivAt ℂ x hb)

#print axioms retained_euclidean_field_conormal_rank

theorem retained_euclidean_retracted_model_analytic
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (D : Opens (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → ComplexPoint X)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (k + k) → ℂ) ω r D)
    (U : Opens NT)
    (hUD : ∀ z ∈ U, emb (Point.map J z.proj) + N.displacement z ∈ D)
    (x : ComplexPoint Q) (hU : zN x ∈ U)
    (hfix : r (emb (Point.map J x)) = Point.map J x)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (hb : a3b4_IsHolChart Q.hom (b.trans
      (Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph))
    (hxb : x ∈ b.source)
    (hbInv : ContMDiffOn 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, Fin k → ℂ) ω b.symm b.target)
    (aX : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin k → ℂ)))
    (haX : ContMDiffOn 𝓘(ℂ, Fin (k + k) → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ))
      ω aX aX.source)
    (hxaX : Point.map J x ∈ aX.source) :
    let P := (N.frame x).toOpenPartialHomeomorph.trans
      (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
    AnalyticAt ℝ (fun q => aX (r (emb (Point.map J (P.symm q).proj) +
      N.displacement (P.symm q)))) (b x, 0) := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (X).hom := inferInstanceAs (LocallyOfFiniteType (v ≫ W.hom))
  letI : QuasiCompact (X).hom := inferInstanceAs (QuasiCompact (v ≫ W.hom))
  letI : IsSeparated (X).hom := inferInstanceAs (IsSeparated (v ≫ W.hom))
  let e := N.frame x
  letI := N.frame_linear x
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  have hxe : zN x ∈ e.source := N.frame_mem x
  have hzP : zN x ∈ P.source := by
    refine ⟨hxe, ?_⟩
    change e (zN x) ∈ (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))).source
    rw [linearFrame_zeroSection k (i1_normalFibre j) e x (e.mem_source.mp hxe)]
    exact ⟨hxb, Set.mem_univ _⟩
  have hP0 : P (zN x) = (b x, (0 : Fin k → ℂ)) := by
    change (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ))) (e (zN x)) = _
    rw [linearFrame_zeroSection k (i1_normalFibre j) e x (e.mem_source.mp hxe)]
    rfl
  have hq : (b x, (0 : Fin k → ℂ)) ∈ P.target := hP0 ▸ P.map_source hzP
  have hPinv : P.symm (b x, (0 : Fin k → ℂ)) = zN x := by
    rw [← hP0, P.left_inv hzP]
  have hJ : ContMDiff 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, Fin (k + k) → ℂ) ω (Point.map J) :=
    (HodgeLean.Foundations.Analytic.f4_isHom_iff_contMDiff
      (d := k) (e := k + k) (Point.map J)).mp
        (HodgeLean.Foundations.Analytic.f4_map_isHom J)
  have hbI := hbInv.contMDiffAt (b.open_target.mem_nhds (b.map_source hxb))
  have hJB := hJ.contMDiffAt.comp (b x) hbI
  have hu := (hemb.contMDiffAt.comp (b x)
    (contMDiffAt_real_of_complex hJB)).contDiffAt.analyticAt
  have hδ := N.analytic x b hb x hxb hxe
  have hD : emb (Point.map J x) ∈ D := by
    have h := hUD (zN x) hU
    rwa [N.zero x, add_zero] at h
  have hrAt := hr.contMDiffAt (D.isOpen.mem_nhds hD)
  have haAt := contMDiffAt_real_of_complex
    (haX.contMDiffAt (aX.open_source.mem_nhds hxaX))
  have haAt' : ContMDiffAt 𝓘(ℝ, Fin (k + k) → ℂ)
      𝓘(ℝ, (Fin k → ℂ) × (Fin k → ℂ)) ω aX (r (emb (Point.map J x))) :=
    hfix.symm ▸ haAt
  have hR := (haAt'.comp (emb (Point.map J x)) hrAt).contDiffAt.analyticAt
  apply normal_frame_retracted_coordinates_analyticAt (i1_normalFibre j) e b
    (fun y => emb (Point.map J y)) N.displacement (aX ∘ r) (b x, 0) hq hu hδ
  change AnalyticAt ℝ (aX ∘ r)
    (emb (Point.map J (P.symm (b x, 0)).proj) + N.displacement (P.symm (b x, 0)))
  rw [hPinv, N.zero x, add_zero]
  exact hR

#print axioms retained_euclidean_retracted_model_analytic

theorem retained_euclidean_displacement_tangent_evaluation
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (A : V.Opens) (hA : IsAffineOpen A) (y : ComplexPoint Q)
    (hy : y ∈ Point.overOpen (j ⁻¹ᵁ A)) :
    ∃ L : i1_normalFibre j y →ₗ[ℂ] (Fin (k + k) → ℂ),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) A hA y hy
        (Point.map J y) (mem_chart_source _ _) a (L u) = u a) ∧
      ∀ u, N.displacement ⟨y, u⟩ =
        mfderiv 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          emb (Point.map J y) (L u) := by
  obtain ⟨L, hL, _, hdisp⟩ := N.metric_evaluation A hA y hy
    (Point.map J y) (mem_chart_source _ _)
  refine ⟨L, hL, ?_⟩
  intro u
  rw [mfderiv_self_eq_original_chart_derivative
    (hemb.mdifferentiableAt (by simp) :
      MDifferentiableAt 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        emb (Point.map J y))]
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]
  convert hdisp u using 1 <;> rfl

#print axioms retained_euclidean_displacement_tangent_evaluation
theorem retained_retracted_transverse_at
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (C : Set (ComplexPoint X)) (hC : Set.range (Point.map J) ⊆ interior C)
    (D : Opens (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → ComplexPoint X)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (k + k) → ℂ) ω r D)
    (hfix : ∀ c ∈ C, r (emb c) = c)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (a : OpenPartialHomeomorph (ComplexPoint X) ((Fin k → ℂ) × (Fin k → ℂ)))
    (ha : ContMDiffOn 𝓘(ℂ, Fin (k + k) → ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ)) ω a a.source)
    (haInv : ContMDiffOn 𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ)) 𝓘(ℂ, Fin (k + k) → ℂ) ω a.symm a.target)
    (hmatch : ∀ y ∈ b.source, Point.map J y ∈ a.source ∧ a (Point.map J y) = (b y, 0))
    (y : ComplexPoint Q) (hy : y ∈ b.source)
    (hD : emb (Point.map J y) ∈ D)
    (e : i1_normalFibre j y ≃ₗ[ℂ] (Fin k → ℂ)) :
    ∃ R : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
      HasFDerivAt (fun w : Fin k → ℂ =>
        (a (r (emb (Point.map J y) + N.displacement ⟨y, e.symm w⟩))).2)
        R.toContinuousLinearMap 0 := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (X).hom := inferInstanceAs (LocallyOfFiniteType (v ≫ W.hom))
  letI : QuasiCompact (X).hom := inferInstanceAs (QuasiCompact (v ≫ W.hom))
  letI : IsSeparated (X).hom := inferInstanceAs (IsSeparated (v ≫ W.hom))
  obtain ⟨A, hA, hyA, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := (Point.map J y).underlying) (U := ⊤) (by trivial)
  have hyA' : y ∈ Point.overOpen (j ⁻¹ᵁ A) := hyA
  obtain ⟨hi, hrank⟩ := retained_euclidean_field_conormal_rank ι k v j hj g n emb N
    A hA y hyA' (Point.map J y) (mem_chart_source _ _)
  obtain ⟨L, hL, hdisp⟩ := retained_euclidean_displacement_tangent_evaluation
    ι k v j hj g n emb hemb N A hA y hyA'
  let D0 := retainedAffineConormalDifferential X Q J (k + k) A hA y hyA'
    (Point.map J y) (mem_chart_source _ _)
  let T0 : (Fin (k + k) → ℂ) →ₗ[ℂ] i1_normalFibre j y :=
    ((ContinuousLinearMap.coeLM ℂ).comp D0).flip
  let T := e.toLinearMap.comp T0
  let L0 := L.comp e.symm.toLinearMap
  let ν : (Fin k → ℂ) →L[ℂ] (Fin (k + k) → ℂ) := L0.toContinuousLinearMap
  have hsection : ∀ u, T (ν u) = u := by
    intro u
    change e (T0 (L (e.symm u))) = u
    have ht : T0 (L (e.symm u)) = e.symm u := by
      ext c
      exact hL (e.symm u) c
    rw [ht, e.apply_symm_apply]
  have hJ := (HodgeLean.Foundations.Analytic.f4_isHom_iff_contMDiff (d := k) (e := k + k) (Point.map J)).mp
    (HodgeLean.Foundations.Analytic.f4_map_isHom J)
  let S : (Fin k → ℂ) →L[ℂ] (Fin (k + k) → ℂ) :=
    mfderiv 𝓘(ℂ, Fin k → ℂ) 𝓘(ℂ, Fin (k + k) → ℂ) (Point.map J) y
  have hScoord : S = fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Q J k (k + k) y)
      ((chartAt (Fin k → ℂ) y) y) := by
    exact mfderiv_self_eq_original_chart_derivative (hJ.mdifferentiableAt (by simp))
  have hker0 : T0.ker = S.toLinearMap.range := by
    rw [hScoord]
    exact retained_conormal_kernel_eq_actual_tangent_range X Q J k k A hA y hyA' hi hrank
  have hSi : Function.Injective S := by
    rw [hScoord]
    obtain ⟨P, hP⟩ := ComplexPoint.exists_leftInverse_fderiv_inclusionInComplexCharts X Q J k (k + k) y
    intro u w huw
    have hh := congrArg P huw
    change (P.comp _) u = (P.comp _) w at hh
    change P.comp (fderiv ℂ (ComplexPoint.inclusionInComplexCharts X Q J k (k + k) y)
      ((chartAt (Fin k → ℂ) y) y)) = ContinuousLinearMap.id ℂ (Fin k → ℂ) at hP
    rw [hP] at hh
    exact hh
  have hareg : a.MDifferentiable 𝓘(ℂ, Fin (k + k) → ℂ)
      𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ)) :=
    ⟨ha.mdifferentiableOn (by simp), haInv.mdifferentiableOn (by simp)⟩
  let F := hareg.mfderiv (hmatch y hy).1
  have hFa : HasMFDerivAt 𝓘(ℂ, Fin (k + k) → ℂ)
      𝓘(ℂ, (Fin k → ℂ) × (Fin k → ℂ)) a (Point.map J y) F.toContinuousLinearMap :=
    (hareg.mdifferentiableAt (hmatch y hy).1).hasMFDerivAt
  let B0 := (ContinuousLinearMap.snd ℂ (Fin k → ℂ) (Fin k → ℂ)).comp F.toContinuousLinearMap
  have hsurj : Function.Surjective B0 := by
    intro u
    refine ⟨F.symm (0, u), ?_⟩
    change (F (F.symm (0, u))).2 = u
    rw [F.apply_symm_apply]
  have hzero : B0.comp S = 0 := by
    apply flattened_manifold_tangent_transverse_zero (Point.map J) a y S F.toContinuousLinearMap
      (hJ.mdifferentiableAt (by simp)).hasMFDerivAt hFa
    filter_upwards [b.open_source.mem_nhds hy] with z hz
    exact congrArg Prod.snd (hmatch z hz).2
  have hkerB : B0.toLinearMap.ker = S.toLinearMap.range :=
    transverse_kernel_eq_of_dimension S.toLinearMap B0.toLinearMap hSi hsurj
      (congrArg ContinuousLinearMap.toLinearMap hzero) (by simp only [Module.finrank_pi, Fintype.card_fin])
  have hkerT : T.ker = T0.ker := by
    ext u
    change e (T0 u) = 0 ↔ T0 u = 0
    exact e.map_eq_zero_iff
  obtain ⟨R, hR⟩ := retracted_manifold_quotient_coordinates emb r a C (Point.map J y)
    (hC ⟨y, rfl⟩) hfix (hemb.mdifferentiableAt (by simp))
    ((hr.contMDiffAt (D.isOpen.mem_nhds hD)).mdifferentiableAt (by simp))
    F.toContinuousLinearMap hFa T ν hsection (hkerB.trans (hker0.symm.trans hkerT.symm)) hsurj
  refine ⟨R, ?_⟩
  convert hR using 1
  funext u
  rw [hdisp]
  rfl

#print axioms retained_retracted_transverse_at
end HodgeLean.Foundations.TubularEuler
