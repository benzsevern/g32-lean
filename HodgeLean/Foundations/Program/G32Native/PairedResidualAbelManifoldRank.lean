import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelPointRank
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeTorusRank

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
/-- The original algebraic Abel morphism, in its specified theta realization,
has surjective manifold differential at every complex point in high degree.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.6. -/
theorem residual_algebraic_abel_mfderiv_surjective
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hpoint : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (a : B ⟶ model (C := ComplexPoint Z) hOne) (p : ComplexPoint Z)
    (hsum : ∀ u, (theta (C := ComplexPoint Z) hOne).symm (Point.map a (Point.map γ u)) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z n i) u))
    (hd : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 < (n : ℤ))
    (b : ComplexPoint B) :
    letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
    letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
    letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
    Function.Surjective (mfderiv 𝓘(ℂ, Fin n → ℂ)
      𝓘(ℂ, b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z))
      (fun w => (theta (C := ComplexPoint Z) hOne).symm (Point.map a w)) b) := by
  letI := b3_periodLattice_finite (C := ComplexPoint Z) hOne
  letI := b3_periodLattice_free (E := Fin 1 → ℂ) (C := ComplexPoint Z)
  letI := b2_latticeMap_discrete _ (b3_isWeightOne (C := ComplexPoint Z) hOne)
  have hlift : ∃ g : (Fin n → ℂ) → b3Rest2_VJ (Fin 1 → ℂ) (ComplexPoint Z),
      AnalyticAt ℂ g (localChart B n b b) ∧
      Function.Surjective (fderiv ℂ g (localChart B n b b)) ∧
      ∀ᶠ w in 𝓝 b, b3Rest2_covHom (g (localChart B n b w)) =
        (theta (C := ComplexPoint Z) hOne).symm (Point.map a w) :=
    residual_algebraic_abel_submersive_at_point Z B n γ hγ hpoint hquot a p hsum hd b
  obtain ⟨g, hg, hr, he⟩ := hlift
  exact residual_native_cover_mfderiv_surjective B n
    (b3_periodF (Fin 1 → ℂ) (ComplexPoint Z))
    (fun w => (theta (C := ComplexPoint Z) hOne).symm (Point.map a w))
    (residual_algebraic_abel_holomorphic Z B n a) b g hg he hr

#print axioms residual_algebraic_abel_mfderiv_surjective
end HodgeLean.Foundations.Program.G32Native
