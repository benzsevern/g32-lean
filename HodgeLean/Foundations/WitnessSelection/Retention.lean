import HodgeLean.Foundations.WitnessSelection.InitialCover
import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers

/-! # Retention of normalized supported basis witnesses

The refinement retains the specified tower, rational basis and supported classes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection

/-- Refine support on the selected branch-free slice without replacing the
retained tower, basis, coefficient vectors, normalized class or absolute equation.
The tower length may be zero. The generic-image input comes from the selected
slice and its retained comparison, rather than an arbitrary family of clauses.
Source: Schoen (1988), Theorem 2.0, p. 18; Fulton, §§1.4,19.1–19.2;
SchoenCycleClassDefs.lean:17,26; SchoenCycleTowerHelpers.lean:12. -/
theorem retained_normalized_support
    (r : ℕ) (W : Fin (r + 1) → Over (Spec ↧ℂ))
    (w : ∀ i : Fin r, W i.succ ⟶ W i.castSucc)
    (W₀ B Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth B.hom]
    [IsProjective W₀.hom]
    (e₀ : W 0 ≅ W₀)
    [QuasiCompact (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left]
    (β : W₀ ⟶ B)
    (ι : Q ⟶ W (Fin.last r)) (d : W (Fin.last r) ⟶ W (Fin.last r))
    (κ : W (Fin.last r) ⟶ B)
    (hκ : s2e_towerTotalMap W e₀.hom w (Fin.last r) ≫ β = κ)
    (hd : d ≫ κ = κ)
    (U : B.left.Opens) [Etale (β.left ∣_ U)]
    (hgeneric : κ.left (ι.left (genericPoint Q.left)) ∈ U)
    (m k n : ℕ) (a : Fin n → Fin m → ℚ)
    (K : Submodule ℚ (AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W₀)) (2 * k)))
    (b : Module.Basis (Fin n) ℚ K)
    (α : ∀ j, s2e_supportedClass W₀
      (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
        (s2e_rationalOrbitCycle ι d m (a j))) k)
    (hnormalized : ∀ j, a3b4_IsCycleClass W₀.hom
      (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
        (s2e_rationalOrbitCycle ι d m (a j))) k (α j))
    (habsolute : ∀ j, s2e_classToAbsolute W₀
      (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
        (s2e_rationalOrbitCycle ι d m (a j))) k (α j) = (b j :
          AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * k))) :
    ∃ α' : ∀ j, s2e_supportedClass W₀
      (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
        (s2e_rationalOrbitCycle ι d m (a j))) k,
      α' = α ∧
      (∀ j, a3b4_IsCycleClass W₀.hom
        (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
          (s2e_rationalOrbitCycle ι d m (a j))) k (α' j)) ∧
      (∀ j, s2e_classToAbsolute W₀
        (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
          (s2e_rationalOrbitCycle ι d m (a j))) k (α' j) = (b j :
            AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (2 * k))) ∧
      (∀ j x, x ∈ (a1p_pushforward (s2e_towerTotalMap W e₀.hom w (Fin.last r)).left
        (s2e_rationalOrbitCycle ι d m (a j))).support →
        ∃ V : W₀.left.Opens, x ∈ V ∧ Smooth (V.ι ≫ W₀.hom)) := by
  refine ⟨α, rfl, hnormalized, habsolute, ?_⟩
  intro j
  exact (residual_generic_smooth ι d (s2e_towerTotalMap W e₀.hom w (Fin.last r))
    β κ hκ hd U hgeneric m (a j)).2

end HodgeLean.WitnessSelection
