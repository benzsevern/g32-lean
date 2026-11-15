import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelFibreIso
import HodgeLean.Foundations.Program.G32Native.PairedResidualSystemAlgebraic

/-! # Constructing the full projective system in its actual Abel fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)

include hy hW hgenus hd hγ hsurj hquot
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- Construct the full-system morphism and identify its actual Abel fibre,
retaining its divisor-point formula and its projection to the quotient.
The full-space membership equivalence is essential here.
Source: Forster, Lectures on Riemann Surfaces, §21; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.3(ii) and proof of Lemma 2.4. -/
theorem paired_c3_full_system_abel_fibre
    (hr : 0 < r) (p : ComplexPoint Z)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (v : W) (hv : v ≠ 0) :
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B,
      IsClosedImmersion ℓ.left ∧
      (Point.map ℓ = fun R => residualProjectiveSystemPoint hOne y hy W
        (fun q => (hW q.val).mp q.property) hgenus γ id (ep.symm R)) ∧
      ∃ e : (ProjectiveSpace (Fin (d + 1)) (Spec ↧ℂ)) ≅
          pullback a.left (Point.map (ℓ ≫ a) (ep (Projectivization.mk ℂ v hv))).left,
        e.hom ≫ pullback.fst _ _ = ℓ.left ∧
        e.hom ≫ pullback.snd _ _ = ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ) := by
  obtain ⟨ℓ, hℓ⟩ := residual_system_divisor_morphism Z B k r y hy W
    (fun q => (hW q.val).mp q.property) hgenus γ hγ d hd
  refine ⟨ℓ, ?_, hℓ, ?_⟩
  · exact residual_system_closedImmersion Z B k r d y hy W
      (fun q => (hW q.val).mp q.property) hgenus hd γ hγ hsurj hquot ℓ hℓ
  · exact residual_system_abel_fibre_iso Z B k r d y hy W hW hgenus hd γ
      hγ hsurj hquot ℓ hℓ hr p a ha v hv

#print axioms paired_c3_full_system_abel_fibre
end HodgeLean.Foundations.Program.G32Native
