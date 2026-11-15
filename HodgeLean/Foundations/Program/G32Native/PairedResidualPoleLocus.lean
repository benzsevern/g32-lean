import HodgeLean.Foundations.Program.SchoenCycleDifferentialQuotient
import HodgeLean.Foundations.Program.G32Native.PairedResidualDivisorGerms

/-! # The closed locus of the full bounded-pole differential system -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The reduced closed locus of effective adjusted divisors from a specified differential space. -/
def residualPoleSystemLocus (hE : Module.finrank ℂ E = 1)
    (Z B : Over (Spec ↧ℂ)) (k r : ℕ) (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z) (y : Fin (2 * r) → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ)) :
    TopologicalSpace.Closeds B.left :=
  TopologicalSpace.Closeds.closure {b | ∃ q : W, q ≠ 0 ∧ ∃ D : C →₀ ℤ,
    D = b4c_divForm (hE := hE) q.1 + s2e_markedPoleDivisor y ∧
    ∃ (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = ((2 * k : ℕ) : ℤ)),
      b = Point.underlying (s2e_symmetricQuotientEvaluation (2 * k) γ
        ((s2e_divisorSym D hD hd).map e))}

#print axioms residualPoleSystemLocus

/-- The original paired divisor points belong to the full pole-system locus with their multiplicities. -/
theorem residual_paired_point_mem_pole_locus [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (Z B : Over (Spec ↧ℂ)) (k r : ℕ) (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z) (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (F : (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] W) (hF : Function.Injective F)
    (hFg : ∀ v p, HurwitzPrymRR_loc hE (F v).1 p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p)
    (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0) :
    Point.underlying (s2e_projectiveDifferentialQuotientPoint hE w x hres y hy
      horder hout hgenus γ e (Projectivization.mk ℂ v hv)) ∈
        residualPoleSystemLocus hE Z B k r γ e y W := by
  change _ ∈ closure _
  apply subset_closure
  let D := s2e_adjustedDifferentialDivisor hE w y v
  have hq : F v ≠ 0 := fun h => hv (hF (h.trans F.map_zero.symm))
  refine ⟨F v, hq, D, ?_,
    s2e_adjustedDifferentialDivisor_effective hE w x hres y hy horder hout v hv,
    s2e_adjustedDifferentialDivisor_degree hE w x hres y hgenus v hv, ?_⟩
  · have hd := residual_divisor_eq_of_germs hE _ _ (hFg v)
    change b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v) +
      s2e_markedPoleDivisor y = _
    rw [hd]
  · rfl

#print axioms residual_paired_point_mem_pole_locus

end HodgeLean.Foundations.Program.G32Native
