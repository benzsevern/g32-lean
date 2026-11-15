import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedPrefixChecks
import HodgeLean.Foundations.Program.G32Native.JointSelectedPositiveData
import HodgeLean.Foundations.Program.G32Native.JointSelectedBasis
import HodgeLean.Foundations.Program.G32Native.JointProjectiveSelfRestriction
import HodgeLean.Foundations.Program.G32Native.PairedBlowupRegularityStep
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData

open HodgeLean.Foundations.TubularEuler HodgeLean.Foundations.BundleThom
open scoped Manifold ContDiff

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations
open scoped BigOperators TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
namespace ResidueSelected
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3
  G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7
  G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11
  G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15
  G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19
  G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27
  G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22
  G32JointBase.inst23 G32JointBase.inst24 G32JointComponent.hQ
  G32JointPositiveData.integralW G32JointPositiveData.projectiveW

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The remaining normal-field and paired numerical inputs on the selected covers.
Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
structure G32RemainingGeometricInputs {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) where
  /-- The original analytic displacement on the dual conormal.
  Source: Lee, Introduction to Smooth Manifolds, second edition, Theorem 6.24. -/
  retained_euclidean_normal_field : ∀ {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
      [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
      [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
      (inc : Q ⟶ W) [IsClosedImmersion inc.left] (k : ℕ)
      {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
      (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = inc.left)
      [SmoothOfRelativeDimension k Q.hom]
      [SmoothOfRelativeDimension (k + k) (v ≫ W.hom)],
    letI : IsClosedImmersion (i1_smoothLift inc v j hj).left := by
      change IsClosedImmersion j
      infer_instance
    letI : SmoothOfRelativeDimension (k + k) (Over.mk (v ≫ W.hom)).hom :=
      ‹SmoothOfRelativeDimension (k + k) (v ≫ W.hom)›
    ∀ (hD : ∀ (A : V.Opens) (hA : IsAffineOpen A) (x : ComplexPoint Q)
      (hx : x ∈ Point.overOpen (j ⁻¹ᵁ A)) (z : ComplexPoint (Over.mk (v ≫ W.hom)))
      (hz : Point.map (i1_smoothLift inc v j hj) x ∈ (chartAt (Fin (k + k) → ℂ) z).source),
      Function.Injective (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift inc v j hj) (k + k) A hA x hx z hz) ∧
      Module.finrank ℂ (LinearMap.range
        (retainedAffineConormalDifferential (Over.mk (v ≫ W.hom)) Q (i1_smoothLift inc v j hj) (k + k) A hA x hx z hz)) = k)
    (g : ChartHermitianMetric (ComplexPoint (Over.mk (v ≫ W.hom))) (k + k)) (n : ℕ)
    (emb : ComplexPoint (Over.mk (v ≫ W.hom)) → EuclideanSpace ℝ (Fin n))
    (hemb : ContMDiff 𝓘(ℝ, Fin (k + k) → ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω emb),
    Nonempty (RetainedEuclideanNormalField inc k v j hj n emb g)
  /-- Numerical nonvanishing on the very component retained by the joint construction.
  Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
  paired_self_intersection :
    ∀ (t : b6t_polydisc c) (S : g32p_Supplier)
      (hA : g32p_Admissible (Classical.choose (g32y_cover_spec D t hg B)).aut S)
      (hNe : g32p_exponents S ≠ []),
      let R := Classical.choose (jointSelectedPrefix_spec D t hg B S hA)
      let P := jointSelectedOrientedPositiveData (@g32l4_paired_blowup_regularity_aux) R hNe
      ∃ degree : Cohomology ℚ (TopCat.of (ComplexPoint P.C.Q)) (2 * R.P.k) →ₗ[ℚ] ℚ,
        degree (s2e_normalEuler P.C.ι R.P.k P.c) ≠ 0

#print axioms G32RemainingGeometricInputs
end ResidueSelected
end HodgeLean.Foundations.Program
