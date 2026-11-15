import HodgeLean.Foundations.Program.SchoenCycleFormalModelSmoothNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleMixedQuotientFormalCoordinates
import HodgeLean.Foundations.Program.SchoenCycleMixedCoefficientCotangentRepresentatives
import HodgeLean.Foundations.Program.SchoenCycleFiniteBlockPartition
import HodgeLean.Foundations.Program.SchoenCycleAdicRenameEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every actual retained complex tuple maps into an actual standard smooth quotient neighbourhood of the divisor length.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.6.1 and 17.11.1. -/
theorem s2e_retained_quotient_standardSmooth_neighbourhood
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) :
    ∃ (W : B.left.Opens) (_ : IsAffineOpen W) (_ : γ.left x.underlying ∈ W),
      letI := s2e_step1_sectionAlgebra B W
      Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(B.left, W) := by
  letI : LocallyOfFiniteType B.hom := s2e_finite_surjective_locallyOfFiniteType (g3_power Z n) B γ
  letI : Algebra ℂ (B.left.presheaf.stalk (γ.left x.underlying)) :=
    (HodgeLean.Foundations.Curves.stalkC (γ.left x.underlying)).toAlgebra
  obtain ⟨b, m, _, ι, p, hp, hx⟩ := s2e_finite_tuple_block_partition n
    (fun i => Point.map (g3_proj Z n i) x)
  obtain ⟨E⟩ := s2e_mixed_quotient_formal_coordinates_at_point Z B n γ hγ hquot x b m ι p hp hx
  obtain ⟨c, hc, D, hD, _⟩ :=
    s2e_mixed_coefficient_cotangent_representatives Z B n γ hγ hquot x b m ι p hp hx 2
  have hbFin (i : Fin n) : (D.reindex ι) i =
      (IsLocalRing.maximalIdeal (B.left.presheaf.stalk (γ.left x.underlying))).toCotangent
        ⟨c (ι.symm i), hc (ι.symm i)⟩ := by
    rw [Module.Basis.reindex_apply]
    exact hD (ι.symm i)
  exact s2e_standardSmooth_neighbourhood_of_formal_model B n (Point.map γ x)
    (E.trans (s2e_adic_rename_equiv (R := ℂ) ι))
    (c ∘ ι.symm) (fun i => hc (ι.symm i)) (D.reindex ι) hbFin

#print axioms s2e_retained_quotient_standardSmooth_neighbourhood
end HodgeLean.Foundations.Program
