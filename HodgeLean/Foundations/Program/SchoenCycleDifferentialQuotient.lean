import HodgeLean.Foundations.Program.SchoenCycleDivisorEnumeration
import HodgeLean.Foundations.Program.SchoenCycleDivisorSymmetric
import HodgeLean.Foundations.Program.SchoenCycleSymmetricBranch

/-! # Differential zero tuples in the retained quotient
The actual projective divisor assignment gives points of the specified symmetric quotient.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
/-- Positive multiplicity in an effective divisor places its quotient point
in the support of the actual marked branch ideal. -/
theorem s2e_effectiveDivisor_mem_branch_support
    {C : Type} (Z B : Over (Spec ↧ℂ)) (n : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (n + 1) σ ≫ γ = γ)
    (D : C →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = ((n + 1 : ℕ) : ℤ))
    (e : C → ComplexPoint Z) (p : C) (hp : 0 < D p) :
    Point.underlying (s2e_symmetricQuotientEvaluation (n + 1) γ
      ((s2e_divisorSym D hD hd).map e)) ∈
        (s2c_branchIdeal Z B n γ (e p)).support := by
  apply s2e_symmetricQuotientEvaluation_mem_branch_support Z B n γ hγ
  exact Sym.mem_map.mpr ⟨p, (s2e_divisorSym_mem_iff D hD hd p).mpr hp, rfl⟩

/-- Quotient evaluation of an effective divisor agrees exactly with its tuple presentations. -/
theorem s2e_effectiveDivisor_quotient_eq_iff
    (Z B : Over (Spec ↧ℂ)) (n : ℕ) (γ : HodgeLean.Adapters.g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hd : b4c_deg D = (n : ℤ))
    (b : ComplexPoint B) :
    s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym D hD hd) = b ↔
      ∃ f : Fin n → ComplexPoint Z, Point.map γ (s2_lift n f) = b ∧
        D = ∑ i, Finsupp.single (f i) (1 : ℤ) := by
  constructor
  · intro hb
    obtain ⟨f, hf⟩ := s2e_effectiveDivisor_exists_tuple D hD hd
    have he := s2e_symmetricQuotientEvaluation_eq n γ hγ _ f
      (s2e_divisor_tuple_enumeration D hD hd f hf)
    exact ⟨f, he.symm.trans hb, hf⟩
  · rintro ⟨f, hb, hf⟩
    exact (s2e_symmetricQuotientEvaluation_eq n γ hγ _ f
      (s2e_divisor_tuple_enumeration D hD hd f hf)).trans hb

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Send the actual unordered zeros to the retained quotient of the curve power.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_projectiveDifferentialQuotientPoint
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    {Z B : Over (Spec ↧ℂ)} (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) : ComplexPoint B :=
  s2e_symmetricQuotientEvaluation (2 * k) γ
    ((s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus z).map e)

example
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    {Z B : Over (Spec ↧ℂ)} (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    s2e_projectiveDifferentialQuotientPoint hE w x hres y hy horder hout hgenus γ e z =
      s2e_symmetricQuotientEvaluation (2 * k) γ
        ((s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus z).map e) := rfl

/-- Every enumeration of the actual zeros gives the same retained quotient point. -/
theorem s2e_projectiveDifferentialQuotientPoint_eq
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    {Z B : Over (Spec ↧ℂ)} (γ : g3_power Z (2 * k) ⟶ B)
    (e : C → ComplexPoint Z)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ)))
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (f : Fin (2 * k) → C)
    (hf : (List.ofFn f : Multiset C) =
      s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus z) :
    s2e_projectiveDifferentialQuotientPoint hE w x hres y hy horder hout hgenus γ e z =
      Point.map γ (s2_lift (2 * k) (fun i => e (f i))) := by
  exact s2e_symmetricQuotientEvaluation_eq (2 * k) γ hγ _ _
    (s2e_sym_map_enumeration _ f hf e)

end HodgeLean.Foundations.Program
