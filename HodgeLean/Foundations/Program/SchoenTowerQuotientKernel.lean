import HodgeLean.Foundations.Program.SchoenTowerQuotientKernelProofs

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The specified categorical symmetric quotient is scheme-theoretically dominant.
Source: SGA 1, Exposé V, §1, universal property and scheme-theoretic image. -/
theorem s2t_quotient_kernel (C P : Over (Spec ↧ℂ)) (h : ℕ)
    (π : g3_power C h ⟶ P)
    (hinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f) :
    IsSchemeTheoreticallyDominant π.left :=
  ⟨s2t_quotient_kernel_aux C P h π hinv hquot⟩

/-- Every map after a morphism with trivial scheme kernel retains its exact kernel.
Source: Mathlib, Scheme.Hom.ker_comp and Scheme.IdealSheafData.map_bot. -/
theorem s2t_kernel_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f.ker = ⊥) : (f ≫ g).ker = g.ker := s2t_kernel_comp_aux f g hf

example {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f.ker = ⊥) : (f ≫ g).ker = g.ker := s2t_kernel_comp f g hf

example (C P : Over (Spec ↧ℂ)) (h : ℕ)
    (π : g3_power C h ⟶ P)
    (hinv : ∀ σ, s2_permute C h σ ≫ π = π)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C h ⟶ T),
      (∀ σ, s2_permute C h σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f) :
    IsSchemeTheoreticallyDominant π.left :=
  s2t_quotient_kernel C P h π hinv hquot

end HodgeLean.Foundations.Program
