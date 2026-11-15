import HodgeLean.Foundations.Program.G32Native.PELIsometryGroup
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalLie

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations HodgeLean.Foundations.Abdulali MvPolynomial
variable {n : ℕ}

/-- The tangent of the D-linear isometry group is exactly its skew centralizer.
The reverse inclusion uses actual exponential curves of isometries commuting
with every retained operator, so it tests the entire vanishing ideal.
Source: Borel, Linear Algebraic Groups, second edition, §§3.5, 3.11;
Humphreys, Linear Algebraic Groups, §13.1. -/
theorem lie_pelIsometryGroup (Ω : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ) :
    X ∈ g1_lieAlgebra (pelIsometryGroup Ω S) ↔
      X.transpose * Ω + Ω * X = 0 ∧ ∀ T ∈ S, X * T = T * X := by
  constructor
  · intro hX
    have hv := g1_mem_lieOfSet_iff.mp hX
    constructor
    · have hm := g1_lie_mono (pelIsometryGroup Ω S) (g1_isometryGroup Ω)
        (fun _ hg => hg.1) hX
      rw [g1_lieAlgebra, g1_mem_lieOfSet_iff] at hm
      ext i j
      apply (differential_isometryEquation Ω X i j) ▸ hm _
      exact (show (g1_isometryGroup Ω).equations ≤
        g1_vanishingIdeal (g1_isometryGroup Ω) from by
          intro f hf
          exact g1_mem_vanishingIdealSet_iff.mpr
            (fun g hg => ((g1_isometryGroup Ω).equations_iff g).mp hg f hf))
        (Ideal.subset_span ⟨i, j, rfl⟩)
    · intro T hT
      apply sub_eq_zero.mp
      ext i j
      have hf : g1_commEquation T i j ∈ g1_vanishingIdealSet
          ((pelIsometryGroup Ω S).carrier : Set _) := by
        apply g1_mem_vanishingIdealSet_iff.mpr
        intro g hg
        rw [g1_eval_commEquation]
        change ((g : Matrix (Fin n) (Fin n) ℂ) * T - T * g) i j = 0
        rw [(mem_pelIsometryGroup Ω S g).mp hg |>.2 T hT, sub_self]
        rfl
      have hz := hv _ hf
      rwa [g1_differential_commEquation] at hz
  · rintro ⟨hX, hc⟩
    rw [g1_lieAlgebra, g1_mem_lieOfSet_iff]
    intro f hf
    have hγ : ∀ i j, HasDerivAt (fun s : ℂ => NormedSpace.exp (s • X) i j) (X i j) 0 := by
      intro i j
      simpa using g2k_hasDerivAt_exp_mul X 1 0 i j
    have hd := g2k_hasDerivAt_differential (fun s => NormedSpace.exp (s • X)) X 0
      (by simp) hγ f
    have hz : (fun s : ℂ => eval (fun ij => NormedSpace.exp (s • X) ij.1 ij.2) f) =
        fun _ => 0 := by
      funext s
      have hg : g2k_expGL X s ∈ (pelIsometryGroup Ω S).carrier := by
        rw [mem_pelIsometryGroup, g2k_coe_expGL]
        exact ⟨g2k_exp_isometry X Ω hX s, fun T hT => g2k_exp_commute X T (hc T hT) s⟩
      have hh := g1_mem_vanishingIdealSet_iff.mp hf _ hg
      change eval (fun ij => (g2k_expGL X s : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2) f = 0 at hh
      rw [g2k_coe_expGL] at hh
      exact hh
    rw [hz] at hd
    exact hd.unique (hasDerivAt_const 0 0)

/-- Passing to the Zariski identity component retains exactly the skew
centralizer, without a smoothness hypothesis on the supplied data.
Source: Borel, Linear Algebraic Groups, second edition, §§1.2, 3.5, 3.11. -/
theorem lie_pelGenericGroup (Ω : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ)) (X : Matrix (Fin n) (Fin n) ℂ) :
    X ∈ g1_lieOfSet (pelGenericGroup Ω S) ↔
      X.transpose * Ω + Ω * X = 0 ∧ ∀ T ∈ S, X * T = T * X := by
  rw [pelGenericGroup, g1_lie_identityComponent, lie_pelIsometryGroup]

#print axioms lie_pelIsometryGroup
#print axioms lie_pelGenericGroup
end HodgeLean.Foundations.Program.GeneralTypeIII
