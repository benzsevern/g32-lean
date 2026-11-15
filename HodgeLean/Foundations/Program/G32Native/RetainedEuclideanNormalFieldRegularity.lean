import HodgeLean.Foundations.Program.G32Native.RetainedNormalFrameSource
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldPack
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricFamily
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanMetricSection
import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldData
import HodgeLean.Foundations.Program.G32Native.RetainedConormalAffineIndependence
import HodgeLean.Foundations.Program.G32Native.RetainedAnalyticQuotientRegularity

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
attribute [local instance] retainedNormalFieldFibreTopology retainedNormalFieldTotalTopology
  retainedNormalFieldLiftClosed retainedNormalFieldAmbientDimension
local notation "X" => Over.mk (v ≫ W.hom)
local notation "J" => i1_smoothLift ι v j hj
local notation "NT" => TotalSpace (Fin k → ℂ) (i1_normalFibre j)
local notation "zN" => zeroSection (Fin k → ℂ) (i1_normalFibre j)


theorem retained_euclidean_displacement_continuous
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (L : ∀ x : ComplexPoint Q, i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ))
    (hL : ∀ (B : V.Opens) (hB : IsAffineOpen B) (x : ComplexPoint Q)
      (hxB : x ∈ Point.overOpen (j ⁻¹ᵁ B)),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a (L x u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map J x)
          ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L x u) w = 0))
    (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) //
          x ∈ Point.overOpen U}) :
    Continuous (fun p : NT =>
      fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ)
        (Point.map J p.proj)).symm c))
        ((chartAt (Fin (k + k) → ℂ) (Point.map J p.proj)) (Point.map J p.proj))
        (L p.proj p.2)) := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (X).hom := inferInstanceAs (LocallyOfFiniteType (v ≫ W.hom))
  letI : QuasiCompact (X).hom := inferInstanceAs (QuasiCompact (v ≫ W.hom))
  letI : IsSeparated (X).hom := inferInstanceAs (IsSeparated (v ≫ W.hom))
  let δ : NT → EuclideanSpace ℝ (Fin n) := fun p =>
    fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ)
      (Point.map J p.proj)).symm c))
      ((chartAt (Fin (k + k) → ℂ) (Point.map J p.proj)) (Point.map J p.proj))
      (L p.proj p.2)
  let e := fun x : ComplexPoint Q =>
    i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1
  have hreg (x : ComplexPoint Q) := retained_analytic_quotient_regularity_aux
    X Q J k k g L hL (frames x).1 (frames x).2.1 n emb hemb
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : p ∈ (e p.proj).source :=
    (retained_normalFrame_mem_source (k := k) (j := j) (frames p.proj).1
      (frames p.proj).2.1 p).mpr (frames p.proj).2.2
  exact (hreg p.proj).1.continuousAt ((e p.proj).open_source.mem_nhds hp)

#print axioms retained_euclidean_displacement_continuous

theorem retained_euclidean_displacement_analytic
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (L : ∀ x : ComplexPoint Q, i1_normalFibre j x →ₗ[ℂ] (Fin (k + k) → ℂ))
    (hL : ∀ (B : V.Opens) (hB : IsAffineOpen B) (x : ComplexPoint Q)
      (hxB : x ∈ Point.overOpen (j ⁻¹ᵁ B)),
      (∀ u a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a (L x u) = u a) ∧
      (∀ u w, (∀ a, retainedAffineConormalDifferential X Q J (k + k) B hB x hxB
        (Point.map J x) (mem_chart_source _ _) a w = 0) →
        g.coefficient (Point.map J x)
          ((chartAt (Fin (k + k) → ℂ) (Point.map J x)) (Point.map J x)) (L x u) w = 0))
    (frames : ∀ x : ComplexPoint Q, Σ U : Q.left.Opens,
      {E : (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j) ≅
        SheafOfModules.free.{0} (R := U.toScheme.ringCatSheaf) (Fin k) //
          x ∈ Point.overOpen U}) :
    ∀ (x : ComplexPoint Q)
    (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ)),
    a3b4_IsHolChart Q.hom (b.trans
      ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) →
    ∀ y ∈ b.source, zN y ∈ (i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1).source →
      let P := (i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1).toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
      AnalyticAt ℝ (fun q => (fun p : NT =>
      fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ)
        (Point.map J p.proj)).symm c))
        ((chartAt (Fin (k + k) → ℂ) (Point.map J p.proj)) (Point.map J p.proj))
        (L p.proj p.2)) (P.symm q)) (b y, 0) := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (X).hom := inferInstanceAs (LocallyOfFiniteType (v ≫ W.hom))
  letI : QuasiCompact (X).hom := inferInstanceAs (QuasiCompact (v ≫ W.hom))
  letI : IsSeparated (X).hom := inferInstanceAs (IsSeparated (v ≫ W.hom))
  let δ : NT → EuclideanSpace ℝ (Fin n) := fun p =>
    fderiv ℝ (fun c => emb ((chartAt (Fin (k + k) → ℂ)
      (Point.map J p.proj)).symm c))
      ((chartAt (Fin (k + k) → ℂ) (Point.map J p.proj)) (Point.map J p.proj))
      (L p.proj p.2)
  let e := fun x : ComplexPoint Q =>
    i1_normalFrameTrivialization j k (frames x).1 (frames x).2.1
  have hreg (x : ComplexPoint Q) := retained_analytic_quotient_regularity_aux
    X Q J k k g L hL (frames x).1 (frames x).2.1 n emb hemb
  intro x b hb y hy hye
  exact (hreg x).2 b hb y hy hye

#print axioms retained_euclidean_displacement_analytic
end HodgeLean.Foundations.TubularEuler
