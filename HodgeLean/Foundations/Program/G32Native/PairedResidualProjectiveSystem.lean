import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleDivisors
import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleLocus

/-! # Projective divisors of the full normalized pole system -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The full differential space has an actual projective adjusted-divisor assignment. -/
def residualProjectiveDivisor
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (y : Fin n → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ)) :
    Projectivization ℂ W → (C →₀ ℤ) :=
  Projectivization.lift (fun q => b4c_divForm (hE := hE) q.val.val + s2e_markedPoleDivisor y)
    (by
      intro a b t hab
      have ht : t ≠ 0 := by
        intro ht
        apply a.property
        rw [hab, ht, zero_smul]
      have he : a.val.val = t • b.val.val := congrArg Subtype.val hab
      rw [he, s2e_divForm_const_smul hE _ t ht])

#print axioms residualProjectiveDivisor

/-- Projective representatives give effective divisors throughout a simple-pole space. -/
theorem residualProjectiveDivisor_effective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (y : Fin n → C)
    (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (z : Projectivization ℂ W) : ∀ p, 0 ≤ residualProjectiveDivisor hE y W z p := by
  refine Quotient.inductionOn z ?_
  intro q
  have hq : q.val.val ≠ 0 := fun h => q.property (Subtype.ext h)
  exact residual_normalized_adjusted_divisor_effective hE y hy
    ⟨q.val.val, (hW q.val).1⟩ hq (hW q.val).2.1 (hW q.val).2.2.1 (hW q.val).2.2.2

#print axioms residualProjectiveDivisor_effective

/-- The full projective system has the degree of the supplied symmetric quotient. -/
theorem residualProjectiveDivisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ} (y : Fin (2 * r) → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (z : Projectivization ℂ W) :
    b4c_deg (residualProjectiveDivisor hE y W z) = (2 * k : ℕ) := by
  refine Quotient.inductionOn z ?_
  intro q
  have hq : q.val.val ≠ 0 := fun h => q.property (Subtype.ext h)
  exact residual_normalized_adjusted_divisor_degree hE y
    ⟨q.val.val, (hW q.val).1⟩ hq (hW q.val).2.1 (hW q.val).2.2 hgenus

#print axioms residualProjectiveDivisor_degree

/-- Evaluate the zeros of every full-system parameter in the supplied symmetric quotient. -/
def residualProjectiveSystemPoint
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ} (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    {Z B : Over (Spec ↧ℂ)} (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z) (z : Projectivization ℂ W) : ComplexPoint B :=
  s2e_symmetricQuotientEvaluation (2 * k) γ
    ((s2e_divisorSym (residualProjectiveDivisor hE y W z)
      (residualProjectiveDivisor_effective hE y hy W hW z)
      (residualProjectiveDivisor_degree hE y W
        (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus z)).map e)

#print axioms residualProjectiveSystemPoint

/-- The retained full-system locus is the closure of its actual projective parametrization. -/
theorem residualPoleSystemLocus_eq_projective_image
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ} (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (Z B : Over (Spec ↧ℂ)) (γ : g3_power Z (2 * k) ⟶ B) (e : C → ComplexPoint Z) :
    residualPoleSystemLocus hE Z B k r γ e y W =
      TopologicalSpace.Closeds.closure (Set.range (fun z => Point.underlying
        (residualProjectiveSystemPoint hE y hy W hW hgenus γ e z))) := by
  unfold residualPoleSystemLocus
  apply congrArg TopologicalSpace.Closeds.closure
  ext b
  constructor
  · rintro ⟨q, hq, D, rfl, hD, hd, hb⟩
    exact ⟨Projectivization.mk ℂ q hq, hb.symm⟩
  · rintro ⟨z, rfl⟩
    induction z using Projectivization.ind with
    | h q hq =>
      refine ⟨q, hq, residualProjectiveDivisor hE y W (Projectivization.mk ℂ q hq),
        rfl, residualProjectiveDivisor_effective hE y hy W hW _,
        residualProjectiveDivisor_degree hE y W
          (fun q => ⟨(hW q).1, (hW q).2.2⟩) hgenus _, rfl⟩

#print axioms residualPoleSystemLocus_eq_projective_image

end HodgeLean.Foundations.Program.G32Native
