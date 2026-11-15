import HodgeLean.Foundations.Program.G32Native.PairedResidualIndexedMonicLift
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelLiftKernel
import HodgeLean.Foundations.Program.G32Native.PairedResidualDerivativeComposition

/-! # Rank of the original native-chart Abel covering lift -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
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
variable [Module.Finite ℤ (b3_periodLattice (Fin 1 → ℂ) (ComplexPoint Z))]
  [DiscreteTopology (b2_latticeMap (b3_periodLattice (Fin 1 → ℂ) (ComplexPoint Z))
    (b3_periodF (Fin 1 → ℂ) (ComplexPoint Z))).range]

/-- Every original native-chart covering lift of the supplied Abel sum has
surjective derivative above the canonical divisor degree.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_native_abel_lift_rank
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (s : ComplexPoint B → b3_Jacobian (Fin 1 → ℂ) (ComplexPoint Z)) (p : ComplexPoint Z)
    (hsum : ∀ u, s (Point.map γ u) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z n i) u))
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ q, 0 ≤ D q)
    (hd : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 < b4c_deg D)
    (x : ComplexPoint (g3_power Z n))
    (ι : (Σ i : D.support, Fin (Int.toNat (D i.1))) ≃ Fin n)
    (hx : ∀ i l, Point.map (g3_proj Z n (ι ⟨i, l⟩)) x = i.1)
    (g : (Fin n → ℂ) → b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z))
    (hg : AnalyticAt ℂ g (localChart B n (Point.map γ x) (Point.map γ x)))
    (hgc : ∀ᶠ w in 𝓝 (Point.map γ x),
      b3Rest2_covHom (g (localChart B n (Point.map γ x) w)) = s w) :
    Function.Surjective (fderiv ℂ g (localChart B n (Point.map γ x) (Point.map γ x))) := by
  classical
  have hm (i : D.support) : 0 < Int.toNat (D i.1) := by
    have hi := Finsupp.mem_support_iff.mp i.property
    have hp := hD i.1
    omega
  have hq : Function.Injective (fun i : D.support => (i.1 : ComplexPoint Z)) := Subtype.val_injective
  have hlift : ∃ T : ((Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ) → (Fin n → ℂ),
      T 0 = localChart B n (Point.map γ x) (Point.map γ x) ∧
      AnalyticAt ℂ T 0 ∧ AnalyticAt ℂ (g ∘ T) 0 ∧
      ∀ᶠ z in 𝓝 (0 : (Σ i : D.support, Fin (Int.toNat (D i.1))) → ℂ),
        b3Rest2_covHom ((g ∘ T) (collisionBlockCoefficients
          (fun i : D.support => Int.toNat (D i.1)) z)) =
          ∑ t : Σ i : D.support, Fin (Int.toNat (D i.1)),
            analyticAbel hOne p (b3A_disc t.1.1 (b4cov_lineEquiv hOne 1) (z t)) := by
    exact residual_monic_torus_lift_indexed_from_native Z B n γ hγ hquot
      (b3_periodF (Fin 1 → ℂ) (ComplexPoint Z)) s (analyticAbel hOne p) hsum x
      (fun i : D.support => Int.toNat (D i.1)) hm ι (fun i : D.support => i.1) hq hx g hg hgc
  obtain ⟨T, hT0, hTa, hga, he⟩ := hlift
  have hsurj : Function.Surjective (fderiv ℂ (g ∘ T) 0) :=
    residual_abel_lift_differential_surjective (E := Fin 1 → ℂ) (C := ComplexPoint Z)
      hOne p D (g ∘ T) hga.differentiableAt he hD hd
  have hgd : DifferentiableAt ℂ g (T 0) := hT0.symm ▸ hg.differentiableAt
  have hr := residual_surjective_fderiv_of_composition g T 0 hgd hTa.differentiableAt hsurj
  simpa only [hT0] using hr

#print axioms residual_native_abel_lift_rank
end HodgeLean.Foundations.Program.G32Native
