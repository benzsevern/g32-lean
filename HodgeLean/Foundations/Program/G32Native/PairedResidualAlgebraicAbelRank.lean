import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeAbelRank
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelLocalLift

/-! # Submersive covering lifts of the actual algebraic Abel map -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped TensorProduct BigOperators Topology Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)
/-- The actual algebraic Abel map has a native analytic covering lift with
surjective derivative at every enumerated effective divisor of sufficiently large degree.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_algebraic_abel_submersive_lift
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (a : B ⟶ model (C := ComplexPoint Z) hOne) (p : ComplexPoint Z)
    (hsum : ∀ u, (theta (C := ComplexPoint Z) hOne).symm (Point.map a (Point.map γ u)) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z n i) u))
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ q, 0 ≤ D q)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 < b4c_deg D)
    (x : ComplexPoint (g3_power Z n))
    (ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n)
    (hx : ∀ i l, Point.map (g3_proj Z n (ι ⟨i, l⟩)) x = i.1)
    :
    letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
    letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
    ∃ g : (Fin n → ℂ) → b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z),
      AnalyticAt ℂ g (localChart B n (Point.map γ x) (Point.map γ x)) ∧
      Function.Surjective (fderiv ℂ g
        (localChart B n (Point.map γ x) (Point.map γ x))) ∧
      ∀ᶠ w in 𝓝 (Point.map γ x),
        b3Rest2_covHom (g (localChart B n (Point.map γ x) w)) =
          (theta (C := ComplexPoint Z) hOne).symm (Point.map a w) := by
  letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
  have hlift : ∃ g : (Fin n → ℂ) → b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z),
      AnalyticAt ℂ g (localChart B n (Point.map γ x) (Point.map γ x)) ∧
      ∀ᶠ w in 𝓝 (Point.map γ x),
        b3Rest2_covHom (g (localChart B n (Point.map γ x) w)) =
          (theta (C := ComplexPoint Z) hOne).symm (Point.map a w) :=
    residual_algebraic_abel_local_lift Z B n a (Point.map γ x)
  obtain ⟨g, hg, hgc⟩ := hlift
  refine ⟨g, hg, ?_, hgc⟩
  exact residual_native_abel_lift_rank Z B n γ hγ hquot
    (fun w => (theta (C := ComplexPoint Z) hOne).symm (Point.map a w))
    p hsum D hD hd x ι hx g hg hgc

#print axioms residual_algebraic_abel_submersive_lift
end HodgeLean.Foundations.Program.G32Native
