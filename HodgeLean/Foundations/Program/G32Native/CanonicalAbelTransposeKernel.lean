import HodgeLean.Foundations.Program.G32Native.AbelTransposeKernelDimension
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelTangentVanishing
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelCovectorJets
import HodgeLean.Foundations.Program.G32Native.CanonicalFormJetKernel

/-! # The retained homogeneous line is the actual transpose kernel -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Multiplicity orders identify the entire transpose kernel with the original homogeneous form line. -/
theorem canonical_abel_transpose_kernel_aux (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hFa : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hFe : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i)) :
    LinearMap.ker ((canonicalAbelDifferential G F x).dualMap.comp
      (Module.Dual.eval ℂ (Fin (G.k + 1) → ℂ))) =
      (g32n_homogeneousLine G.k G.eQ x).submodule := by
  let A := canonicalAbelDifferential G F x
  let T := A.dualMap.comp (Module.Dual.eval ℂ (Fin (G.k + 1) → ℂ))
  let L := g32n_homogeneousLine G.k G.eQ x
  have hvan (a : Fin (G.k + 1) → ℂ) : a ∈ LinearMap.ker T ↔ ∀ v, A v a = 0 := by
    change T a = 0 ↔ ∀ v, A v a = 0
    constructor
    · intro h v
      exact congrArg (fun f : Module.Dual ℂ (Fin (G.k + G.k) → ℂ) => f v) h
    · intro h
      apply LinearMap.ext
      intro v
      exact h v
  have hle : LinearMap.ker T ≤ L.submodule := by
    intro a ha
    have horders := canonical_abel_covector_orders_aux G p F x hFa hFe a ((hvan a).mp ha)
    have hθ : canonicalCoefficientForm G L.rep ≠ 0 :=
      (canonicalCoefficientForm G).map_ne_zero_iff.mpr L.rep_nonzero
    obtain ⟨c, hc⟩ := canonical_form_proportional_of_local_orders G
      (canonicalCoefficientForm G L.rep) (canonicalCoefficientForm G a) hθ horders
    have he : a = c • L.rep := (canonicalCoefficientForm G).injective
      (hc.trans ((canonicalCoefficientForm G).map_smul c L.rep).symm)
    rw [L.submodule_eq, he]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  let D := fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) x)
    (localChart G.Q G.k x x)
  have hleft : Function.LeftInverse
      (closedImmersionDerivativeProjection G.W G.Q G.ι G.k (G.k + G.k) x) D := by
    intro v
    exact congrArg (fun M : (Fin G.k → ℂ) →L[ℂ] (Fin G.k → ℂ) => M v)
      (closedImmersionDerivativeProjection_leftInverse G.W G.Q G.ι G.k (G.k + G.k) x)
  exact linear_transpose_kernel_eq_line_of_le G.k A D.toLinearMap hleft.injective
    (canonical_abel_tangent_vanishes G p F x hFa hFe) L hle

#print axioms canonical_abel_transpose_kernel_aux
end HodgeLean.Foundations.Program.G32Native
