import HodgeLean.Foundations.Program.PrymParabolicIntersectionIsotypicAlgebra
import HodgeLean.Foundations.Program.PrymParabolicIntersectionIntegralCup
import HodgeLean.Foundations.Program.PrymParabolicIntersectionRestriction

noncomputable section
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem hga_coordCup_eq_cupEval {G : Type} [Group G] [Fintype G]
    {K : Type} [Field K] [StarRing K] {ι : Type} {r : ℕ}
    (g : Fin r → G) (i j : ι) (α β : hg_Edge G r → ι → K) :
    hg6_coordCup g i j α β =
      hga_cupEval K g (fun ε ↦ star (α ε i)) (fun ε ↦ β ε j) := by
  unfold hg6_coordCup hga_cupEval
  rw [hga_orient_evaluation_eq_fundEval]
  rfl

theorem hga_cupEval_intCast {G : Type} [Group G] [Fintype G] {r : ℕ}
    (K : Type) [CommRing K] (g : Fin r → G) (α β : hg2_Edge G r → ℤ) :
    hga_cupEval K g (fun ε ↦ (α ε : K)) (fun ε ↦ (β ε : K)) =
      (hga_cupEval ℤ g α β : K) := by
  unfold hga_cupEval Finsupp.sum
  push_cast
  rfl

theorem hga_cupEval_quadratic_expansion {G : Type} [Group G] [Fintype G] {r : ℕ}
    (K : Type) [CommRing K] (g : Fin r → G) (s : K) (hs : s ^ 2 = -3)
    (α β γ δ : hg2_Edge G r → K) :
    hga_cupEval K g (fun ε ↦ -α ε - s * β ε) (fun ε ↦ -γ ε + s * δ ε) =
      hga_cupEval K g α γ - s * hga_cupEval K g α δ +
        s * hga_cupEval K g β γ + 3 * hga_cupEval K g β δ := by
  unfold hga_cupEval Finsupp.sum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ hτ
  linear_combination -(hg2_orient τ : K) * β (hg2_face2 τ) * δ (hg2_face0 g τ) * hs

theorem hga_integral_cocycle_cast {G : Type} [Group G] {r : ℕ}
    (K : Type) [CommRing K] (g : Fin r → G) (α : hg2_Edge G r → ℤ)
    (hα : hg2_delta1 ℤ ℤ g α = 0) :
    hg2_delta1 K K g (fun ε ↦ (α ε : K)) = 0 := by
  ext τ
  have h := congrFun hα τ
  change α (hg2_face0 g τ) - α (hg2_face1 τ) + α (hg2_face2 τ) = 0 at h
  change (α (hg2_face0 g τ) : K) - (α (hg2_face1 τ) : K) +
    (α (hg2_face2 τ) : K) = 0
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_zero] using
    congrArg (fun n : ℤ ↦ (n : K)) h

theorem hga_cocycle_quadratic_combination {G : Type} [Group G] {r : ℕ}
    (K : Type) [CommRing K] (g : Fin r → G) (s : K)
    (α β : hg2_Edge G r → ℤ)
    (hα : hg2_delta1 ℤ ℤ g α = 0) (hβ : hg2_delta1 ℤ ℤ g β = 0) :
    hg2_delta1 K K g (fun ε ↦ -(α ε : K) + s * (β ε : K)) = 0 := by
  change hg2_delta1 K K g (-(fun ε ↦ (α ε : K)) + s • (fun ε ↦ (β ε : K))) = 0
  rw [map_add, map_neg, map_smul, hga_integral_cocycle_cast K g α hα,
    hga_integral_cocycle_cast K g β hβ]
  simp

theorem hga_intersection_cocycle {C : Type} [TopologicalSpace C]
    (F : hg8_DeltaMap b4b_root C) (V : Set (Fin 10 → ℂ))
    (hV : V ⊆ b6t_polydisc mr_base) (t : V)
    [ChartedSpace ℂ (b63l_parameterFibre mr_base C V hV t)]
    [IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre mr_base C V hV t)]
    (P : b6m_H1 (b63l_parameterFibre mr_base C V hV t) →ₗ[ℤ]
      b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t))
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice ℂ (b63l_parameterFibre mr_base C V hV t)))
    (a : hg2_H1 ℤ b4b_root) :
    ∃ α : hg2_Edge b4b_Group 13 → ℤ, hg2_delta1 ℤ ℤ b4b_root α = 0 ∧
      ∀ z : LinearMap.ker (hg2_bd1 ℤ b4b_root),
        z.1.sum (fun ε n ↦ n * α ε) =
          hga_cellIntersection F V hV t P Q a (Submodule.Quotient.mk z) := by
  obtain ⟨α, hα, he⟩ := hga_cellular_cocycle_of_singular_functional (hga_fibreMap F V hV t)
    ((Q (P (hg9_toFibre F V hV t a))).comp P)
  refine ⟨α, hα, fun z ↦ ?_⟩
  have h := he z
  rw [hga_H1map_fibre] at h
  exact h

theorem hga_integral_combination_evaluation {E : Type} (K : Type) [CommRing K]
    (z : E →₀ ℤ) (α β : E → ℤ) (s : K) :
    z.sum (fun ε n ↦ (n : K) * (-(α ε : K) + s * (β ε : K))) =
      -((z.sum (fun ε n ↦ n * α ε) : ℤ) : K) + s * ((z.sum (fun ε n ↦ n * β ε) : ℤ) : K) := by
  simp only [Finsupp.sum, Int.cast_sum, Int.cast_mul, mul_add, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε hε
  ring

#print axioms hga_integral_combination_evaluation
#print axioms hga_intersection_cocycle
#print axioms hga_cocycle_quadratic_combination
#print axioms hga_integral_cocycle_cast
#print axioms hga_cupEval_quadratic_expansion
#print axioms hga_cupEval_intCast
#print axioms hga_coordCup_eq_cupEval
end HodgeLean.Foundations.Program
