import HodgeLean.Foundations.Program.G32Native.RetainedEuclideanNormalFieldData
import HodgeLean.Foundations.Program.G32Native.AmbientOpenMatchedCharts

/-! # Coordinate comparison for Euclidean addition followed by a retraction

This statement constructs no tube and asserts no overlap equality.
It tests the specified composite in holomorphic flattening coordinates.
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

/-- The retracted original normal displacement has analytic flattening coordinates
and an invertible complex transverse differential on the zero section.
The retraction identity is needed on a neighbourhood in the ambient manifold,
so its derivative is the identity on every ambient tangent direction.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 4.5,
Theorem 6.24 and Proposition 6.25; Hirsch, Differential Topology, chapter 4,
section 5. Analytic regularity uses the analytic inverse function theorem.
HC no distance; AV milestone no distance. -/
theorem retracted_normal_coordinate_comparison_aux
    (g : ChartHermitianMetric (ComplexPoint X) (k + k)) (n : ℕ)
    (emb : ComplexPoint X → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb)
    (himm : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) emb x))
    (N : RetainedEuclideanNormalField ι k v j hj n emb g)
    (C : Set (ComplexPoint X)) (hC : Set.range (Point.map J) ⊆ interior C)
    (D : Opens (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → ComplexPoint X)
    (hr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (k + k) → ℂ) ω r D)
    (hfix : ∀ c ∈ C, r (emb c) = c)
    (U : Opens NT)
    (hUD : ∀ z ∈ U, emb (Point.map J z.proj) + N.displacement z ∈ D)
    (hU : ∀ y, zN y ∈ U)
    (x : ComplexPoint Q) :
    let f : NT → ComplexPoint X := fun z => r (emb (Point.map J z.proj) + N.displacement z)
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin k → ℂ))
    (e : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) (i1_normalFibre j)))
    (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin k → ℂ) × (Fin k → ℂ))),
    (a3b4_IsHolChart Q.hom (b.trans
      ((Homeomorph.prodUnique (Fin k → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph))) ∧
    (e.IsLinear ℂ) ∧
    (a3b4_IsHolChart W.hom a) ∧
    (x ∈ b.source) ∧
    (zeroSection (Fin k → ℂ) (i1_normalFibre j) x ∈ e.source) ∧
    (∀ y ∈ b.source, Point.map ι y ∈ a.source ∧
      a (Point.map ι y) = (b y, (0 : Fin k → ℂ))) ∧
    (∀ y ∈ a.source,
      y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔ (a y).2 = 0) ∧
    (let P := e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)));
      AnalyticAt ℝ (fun q => a (Point.map
        (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (f (P.symm q)))) (b x, 0)) ∧
    (let P := e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)));
      let g := fun q => Point.map
        (Over.homMk v rfl : Over.mk (v ≫ W.hom) ⟶ W) (f (P.symm q));
      ∀ q, (q, (0 : Fin k → ℂ)) ∈ P.target →
        P.symm (q, 0) ∈ U → g (q, 0) ∈ a.source →
        ∃ A : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ),
          HasFDerivAt (fun w : Fin k → ℂ => (a (g (q, w))).2)
            A.toContinuousLinearMap 0) := by
  obtain ⟨b, a, hb, ha, hxb, _, hmatch, hsupp, hbInv, aX, haX, haXInv,
    hsource, heval, hmatchX⟩ := ambient_open_matched_holomorphic_charts ι k v j hj x
  let e := N.frame x
  letI := N.frame_linear x
  let P := e.toOpenPartialHomeomorph.trans
    (b.prod (OpenPartialHomeomorph.refl (Fin k → ℂ)))
  refine ⟨b, e, a, hb, N.frame_linear x, ha, hxb, N.frame_mem x, hmatch, hsupp, ?_, ?_⟩
  · have hxfix := hfix (Point.map J x) (interior_subset (hC ⟨x, rfl⟩))
    have han := retained_euclidean_retracted_model_analytic ι k v j hj g n emb hemb N
      D r hr U hUD x (hU x) hxfix b hb hxb hbInv aX haX (hmatchX x hxb).1
    dsimp only
    simp only [heval]
    exact han
  · dsimp only
    intro q hq hqU _
    obtain ⟨y, hyE, hyb, hyq, hinv⟩ :=
      normal_frame_model_inverse_fibre (K := ℂ) (i1_normalFibre j) e b q hq
    have hDy : emb (Point.map J y) ∈ D := by
      have h := hUD (P.symm (q, 0)) hqU
      rw [hinv 0, map_zero] at h
      change emb (Point.map J y) + N.displacement (zN y) ∈ D at h
      rwa [N.zero y, add_zero] at h
    obtain ⟨R, hR⟩ := retained_retracted_transverse_at ι k v j hj g n emb hemb N C hC
      D r hr hfix b aX haX haXInv hmatchX y hyb hDy (e.linearEquivAt ℂ y hyE)
    refine ⟨R, ?_⟩
    simp only [hinv, heval]
    exact hR

#print axioms retracted_normal_coordinate_comparison_aux
end HodgeLean.Foundations.TubularEuler
