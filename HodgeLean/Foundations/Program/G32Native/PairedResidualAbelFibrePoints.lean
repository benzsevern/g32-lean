import HodgeLean.Foundations.Program.G32Native.PairedResidualLinearSystemCriterion
import HodgeLean.Foundations.Program.G32Native.PairedResidualAbelEvaluation

/-! # Actual complex points of the specified full-system Abel fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
  [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The actual full-system projective image is precisely the fibre of the specified Abel value on points. -/
theorem residual_system_abel_fibre_points
    (k r : ℕ) (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm hOne q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ t, q ⟨p, t⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (p : ComplexPoint Z) (γ : g3_power Z (2 * k) ⟶ B)
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (v : W) (hv : v ≠ 0) (b : ComplexPoint B) :
    (∃ z : Projectivization ℂ W, residualProjectiveSystemPoint hOne y hy W
      (fun q => (hW q.val).mp q.property) hgenus γ id z = b) ↔
      Point.map a b = Point.map a (residualProjectiveSystemPoint hOne y hy W
        (fun q => (hW q.val).mp q.property) hgenus γ id (Projectivization.mk ℂ v hv)) := by
  classical
  let F := residualProjectiveSystemPoint hOne y hy W
    (fun q => (hW q.val).mp q.property) hgenus γ id
  change (∃ z, F z = b) ↔ Point.map a b = Point.map a (F (Projectivization.mk ℂ v hv))
  constructor
  · rintro ⟨z, hz⟩
    exact (congrArg (Point.map a) hz).symm.trans
      (residual_system_abel_value_constant Z B k r y hy W
        (fun q => (hW q.val).mp q.property) hgenus p γ hγ a ha z (Projectivization.mk ℂ v hv))
  · intro hb
    obtain ⟨x, hx⟩ := hsurj b
    let t : Fin (2 * k) → ComplexPoint Z := fun i => Point.map (g3_proj Z (2 * k) i) x
    let D := s2e_markedPoleDivisor t
    have hD : ∀ q, 0 ≤ D q := by
      intro q
      change 0 ≤ (∑ i, Finsupp.single (t i) (1 : ℤ)) q
      rw [Finsupp.finset_sum_apply]
      apply Finset.sum_nonneg
      intro i _
      rw [Finsupp.single_apply]
      split_ifs <;> norm_num
    have hd : b4c_deg D = (2 * k : ℕ) := s2e_markedPoleDivisor_degree t
    have heval : s2e_symmetricQuotientEvaluation (2 * k) γ (s2e_divisorSym D hD hd) = b := by
      have he := s2e_symmetricQuotientEvaluation_eq (2 * k) γ hγ _ t
        (s2e_divisor_tuple_enumeration D hD hd t rfl)
      have ht : s2_lift (2 * k) t = x := s2e_lift_coordinates (2 * k) x
      exact he.trans ((congrArg (Point.map γ) ht).trans hx)
    have hbd := (congrArg (fun q : ComplexPoint B => Point.map a q) heval).symm.trans
      (residual_abel_value_effective_divisor Z B (2 * k) p γ hγ a ha D hD hd)
    have hvb := residual_abel_value_projective_system Z B k r y hy W
      (fun q => (hW q.val).mp q.property) hgenus p γ hγ a ha (Projectivization.mk ℂ v hv)
    have hp : weightedSum (analyticAbel (C := ComplexPoint Z) hOne p) D =
        weightedSum (analyticAbel (C := ComplexPoint Z) hOne p)
          (b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y) :=
      (theta (C := ComplexPoint Z) hOne).injective (hbd.symm.trans (hb.trans hvb))
    have hdv : b4c_deg (b4c_divForm (hE := hOne) v.val + s2e_markedPoleDivisor y) = (2 * k : ℕ) :=
      residualProjectiveDivisor_degree hOne y W
        (fun q => ⟨((hW q.val).mp q.property).1, ((hW q.val).mp q.property).2.2⟩)
        hgenus (Projectivization.mk ℂ v hv)
    let S : Finset (ComplexPoint Z) := Finset.univ.image y
    have hS : ∀ q, q ∈ S ↔ q ∈ Set.range y := by
      intro q
      simp [S, Set.mem_range]
    have hWS : ∀ q, q ∈ W ↔ b4c_IsMeroForm hOne q ∧
        (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hOne q p) 0) ∧
        (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hOne q p) 0) ∧
        ∀ p ∈ S, ∀ t, q ⟨p, t⟩ = 0 := by
      intro q
      simpa only [hS] using hW q
    obtain ⟨q, hq, hqD⟩ := (residual_full_space_divisor_abel_criterion hOne S W hWS y hy hS
      v hv p D hD (hd.trans hdv.symm)).mpr hp
    refine ⟨Projectivization.mk ℂ q hq, ?_⟩
    have hqdiv : residualProjectiveDivisor hOne y W (Projectivization.mk ℂ q hq) = D := hqD
    simpa only [F, residualProjectiveSystemPoint, Sym.map_id, hqdiv] using heval

#print axioms residual_system_abel_fibre_points
end HodgeLean.Foundations.Program.G32Native
