import HodgeLean.Foundations.Program.SchoenCycleU1
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.G32PropFourSixDefs

/-! # Zero-pair canonical slice on retained native data

Native consumer: SchoenTransferJ2NativeInput.lean:398–412 (U01–U02).
The finite étale cover is an input; the curve, part and symmetric quotient stay fixed.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators ContDiff Manifold
namespace HodgeLean.Foundations.Program

/-- The zero-pair native prefix supplies its relative dimension and canonical divisor slice. -/
theorem g32n_zeroPairCanonicalSlice
    (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (S : g32p_Supplier) (P : g32p_Part J aut S)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (h : ℕ) (hselected : h + 1 = 2 * P.k)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (hgenus : 2 * P.k + 2 =
      2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
        (g32p_exponents S).length)
    (hr : r = 0) (β₀ : W₀ ⟶ B₀) (hEtale : Etale β₀.left) :
    Etale β₀.left ∧
    ∃ hZ : SmoothOfRelativeDimension 1 Z.hom,
      let := hZ
      let PP : Over (Spec ↧ℂ) := Over.mk
        (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
      ∃ (ℓ : PP ⟶ B₀), IsClosedImmersion ℓ.left ∧
        (∀ b : ComplexPoint B₀, b ∈ Set.range (Point.map ℓ) ↔
          ∃ z : Fin (h + 1) → ComplexPoint Z,
            Point.map γ (s2_lift (h + 1) z) = b ∧
            ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
              b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
                (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
                  ∑ t, Finsupp.single (z t) (1 : ℤ)) := by
  have hlength : (g32p_exponents S).length = 2 * r := by
    have he := Fintype.card_congr σ
    simpa only [Fintype.card_fin] using he.symm
  obtain ⟨hZ, hd, hg⟩ := s2e_chain_unramified_native_genus Z hdimZ eZ P.k r hr
    (by simpa only [hlength] using hgenus)
  let := hZ
  refine ⟨hEtale, hZ, ?_⟩
  revert hγ hγinv hγsurj
  revert γ
  rw [hselected]
  intro γ inst hγsurj hγinv hγ
  obtain ⟨ℓ, hℓ⟩ := s2e_canonicalProjective_algebraize Z B₀ (2 * P.k) P.k γ hγinv hg hd
  exact ⟨ℓ,
    s2e_chain_canonical_immersion Z B₀ P.k γ hγsurj hγinv hγ hg hd ℓ hℓ,
    s2e_chain_canonical_range_exact Z B₀ P.k γ hγsurj hγinv hγ hg hd ℓ hℓ⟩

end HodgeLean.Foundations.Program
