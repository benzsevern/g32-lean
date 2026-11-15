import HodgeLean.Foundations.Program.SchoenCycleStep1
import Mathlib.Data.List.FinRange
import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity
import HodgeLean.Foundations.Program.SchoenCycleDifferentialQuotient

/-! # Reduced unordered points in the retained quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Quotient evaluation distinguishes unordered complex tuples, retaining repeated entries.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_symmetricQuotientEvaluation_injective
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! w : B ⟶ T, γ ≫ w = v) :
    Function.Injective (s2e_symmetricQuotientEvaluation
      (T := Over.mk (𝟙 (Spec ↧ℂ))) N γ) := by
  intro s t h
  let f := s2e_symEnumeration s
  let g := s2e_symEnumeration t
  obtain ⟨σ, hσ⟩ := s2e_step1_retained_symmetric_orbits Z B N γ hsurj hinv hquot
    (s2_lift N f) (s2_lift N g) h
  change s2_lift N f ≫ s2_permute Z N σ = s2_lift N g at hσ
  rw [s2e_lift_permute] at hσ
  have hfg : (fun i => f (σ.symm i)) = g := by
    funext i
    have hi := congrArg (fun z => z ≫ g3_proj Z N i) hσ
    simpa only [s2_check_lift_proj] using hi
  apply Subtype.ext
  have hs : (List.ofFn f : Multiset (ComplexPoint Z)) = s :=
    (s2e_sym_exists_enumeration s).choose_spec
  have ht : (List.ofFn g : Multiset (ComplexPoint Z)) = t :=
    (s2e_sym_exists_enumeration t).choose_spec
  have hp : (List.ofFn f : Multiset (ComplexPoint Z)) =
      List.ofFn (fun i => f (σ.symm i)) :=
    (Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm σ.symm f)).symm
  have he := congrArg (fun z => (List.ofFn z : Multiset (ComplexPoint Z))) hfg
  exact hs.symm.trans (hp.trans (he.trans ht))

/-- The actual paired divisor assignment distinguishes its projective parameters.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14. -/
theorem s2e_pairedDifferentialQuotientPoint_injective
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (k r : ℕ)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (x : Fin r → ComplexPoint Z)
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v) :
    let : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    Function.Injective (s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w x hres y hy horder hout hgenus γ id) := by
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  dsimp only
  intro u v h
  apply s2e_projectiveDifferentialSymmetricPower_injective
    (Module.finrank_fin_fun (n := 1) ℂ) w x hres y hy horder hout hgenus
  have he := s2e_symmetricQuotientEvaluation_injective Z B (2 * k) γ hsurj hinv hquot h
  simpa only [Sym.map_id] using he

end HodgeLean.Foundations.Program
