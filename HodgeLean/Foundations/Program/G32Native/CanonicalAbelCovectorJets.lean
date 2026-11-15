import HodgeLean.Foundations.Program.G32Native.CanonicalAbelBlockCovectors
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelMarkedDivisor
import HodgeLean.Foundations.Program.G32Native.CanonicalDivisorBlockOrders
import HodgeLean.Foundations.Program.SchoenCycleFiniteBlockPartition
import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms
import HodgeLean.Foundations.Program.G32Native.AbelCollisionTraceJets

/-! # The original Abel covector kernel and canonical multiplicity orders -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual Abel covector vanishes only if its original form has every canonical multiplicity. -/
theorem canonical_abel_covector_orders_aux (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hFa : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hFe : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i))
    (a : Fin (G.k + 1) → ℂ) :
    (∀ v, canonicalAbelDifferential G F x v a = 0) →
      ∀ q : ComplexPoint G.Z,
        meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
          (canonicalCoefficientForm G (g32n_homogeneousLine G.k G.eQ x).rep) q) 0 ≤
        meromorphicOrderAt (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
          (canonicalCoefficientForm G a) q) 0 := by
  intro hzero
  let θ := canonicalCoefficientForm G (g32n_homogeneousLine G.k G.eQ x).rep
  have hθ : θ ≠ 0 := (canonicalCoefficientForm G).map_ne_zero_iff.mpr
    (g32n_homogeneousLine G.k G.eQ x).rep_nonzero
  obtain ⟨z, hdiv, hz⟩ := canonical_abel_marked_divisor_tuple G x
  obtain ⟨b, m, hm, ι, q, hq, hzq⟩ := s2e_finite_tuple_block_partition (2 * G.k) z
  have hzip (j : Fin b) (i : Fin (m j)) :
      Point.map (g3_proj G.Z (2 * G.k) (ι ⟨j, i⟩)) (s2_lift (2 * G.k) z) = q j := by
    change s2_lift (2 * G.k) z ≫ g3_proj G.Z (2 * G.k) (ι ⟨j, i⟩) = q j
    rw [s2_check_lift_proj]
    exact hzq j i
  apply (canonical_divisor_block_orders G θ (canonicalCoefficientForm G a) hθ z hdiv
    b m ι q hq hzq).mpr
  exact canonical_abel_covector_block_orders G p F x hFa hFe
    (s2_lift (2 * G.k) z) hz b m hm ι q hq hzip a hzero

#print axioms canonical_abel_covector_orders_aux
end HodgeLean.Foundations.Program.G32Native
