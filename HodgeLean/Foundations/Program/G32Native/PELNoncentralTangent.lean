import HodgeLean.Foundations.Program.G32Native.PELIsometryTangent

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations

/-- A skew-centralizer direction that fails to commute detects an actual
noncommuting point in the connected isometry group. -/
theorem pel_noncentral_of_tangent {n : ℕ}
    (Ω : Matrix (Fin n) (Fin n) ℂ) (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (j : Matrix.GeneralLinearGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (hskew : X.transpose * Ω + Ω * X = 0)
    (hcomm : ∀ T ∈ S, X * T = T * X)
    (hne : X * (j : Matrix (Fin n) (Fin n) ℂ) ≠ (j : Matrix (Fin n) (Fin n) ℂ) * X) :
    ∃ g ∈ g1_identityComponent (pelIsometryGroup Ω S), ¬ Commute j g := by
  by_contra! h
  apply hne
  apply sub_eq_zero.mp
  ext a b
  have hX := (lie_pelGenericGroup Ω S X).mpr ⟨hskew, hcomm⟩
  have hv := g1_mem_lieOfSet_iff.mp hX
  have hf : g1_commEquation (j : Matrix (Fin n) (Fin n) ℂ) a b ∈
      g1_vanishingIdealSet (pelGenericGroup Ω S) := by
    apply g1_mem_vanishingIdealSet_iff.mpr
    intro g hg
    rw [g1_eval_commEquation]
    have he : (g : Matrix (Fin n) (Fin n) ℂ) * j =
        (j : Matrix (Fin n) (Fin n) ℂ) * g := by
      exact congrArg Units.val (h g hg).eq.symm
    change ((g : Matrix (Fin n) (Fin n) ℂ) * j -
      (j : Matrix (Fin n) (Fin n) ℂ) * g) a b = 0
    rw [he, sub_self]
    rfl
  have hz := hv _ hf
  rwa [g1_differential_commEquation] at hz

#print axioms pel_noncentral_of_tangent
end HodgeLean.Foundations.Program.GeneralTypeIII
