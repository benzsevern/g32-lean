import HodgeLean.Foundations.Program.SchoenCycleCanonicalDivisors

/-! # Actual canonical tuples along projective differential lines -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The specified canonical quotient point map supplies nearby exact divisor
tuples for a differential line; no tuple or infinitesimal divisor premise is added.
Source: ACGH, Geometry of Algebraic Curves I, Chapter I, canonical divisors;
HodgeLean, `s2e_canonicalQuotientPoint_eq`. -/
theorem s2e_u1_canonical_line_divisor_tuples
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B)
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hg : (N : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (θ δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) (b : ℂ → ComplexPoint B)
    (hline : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : θ + t • δ ≠ 0,
      b t = s2e_canonicalQuotientPoint Z B N γ hg
        (Projectivization.mk ℂ (θ + t • δ) h)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∃ x : Fin N → ComplexPoint Z,
      (θ + t • δ) ≠ 0 ∧
      b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ) (θ + t • δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) =
        ∑ i, Finsupp.single (x i) (1 : ℤ) ∧
      b t = Point.map γ (s2_lift N x) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  filter_upwards [hline] with t ht
  obtain ⟨hne, hb⟩ := ht
  have heff := s2e_holomorphic_divisor_effective (Module.finrank_fin_fun (n := 1) ℂ) _ hne
  have hdegree := (s2e_holomorphic_divisor_degree
    (Module.finrank_fin_fun (n := 1) ℂ) (θ + t • δ) hne).trans hg.symm
  obtain ⟨x, hx⟩ := s2e_effectiveDivisor_exists_tuple _ heff hdegree
  exact ⟨x, hne, hx, hb.trans (s2e_canonicalQuotientPoint_eq Z B N γ hγ hg _ hne x hx)⟩

end HodgeLean.Foundations.Program
