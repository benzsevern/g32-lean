import HodgeLean.Foundations.Program.SchoenCycleU1SupportProjection
import HodgeLean.Foundations.Program.SchoenCycleU1SectionEvaluation

/-! # Regular functions separating a finite divisor support -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A general linear combination of a finite separating family still separates
all the specified evaluations.
Source: Hartshorne, Algebraic Geometry, I.1, avoidance of finitely many hyperplanes. -/
theorem s2e_u1_generic_separating_linear_combination
    {ι κ A : Type} [Fintype ι] [Fintype κ] [CommRing A] [Algebra ℂ A]
    (e : ι → A →ₐ[ℂ] ℂ) (s : κ → A)
    (hsep : ∀ i j, i ≠ j → ∃ k, e i (s k) ≠ e j (s k)) :
    a3r_Generic {a : κ → ℂ | Function.Injective (fun i => e i (∑ k, a k • s k))} := by
  classical
  have hpair (ij : ι × ι) : a3r_Generic {a : κ → ℂ |
      ij.1 ≠ ij.2 → e ij.1 (∑ k, a k • s k) ≠ e ij.2 (∑ k, a k • s k)} := by
    by_cases hij : ij.1 = ij.2
    · exact a3r_generic_univ.mono fun _ _ h => (h hij).elim
    obtain ⟨k, hk⟩ := hsep ij.1 ij.2 hij
    let G : MvPolynomial κ ℂ := ∑ l, C (e ij.1 (s l) - e ij.2 (s l)) * X l
    have hG : G ≠ 0 := by
      intro h
      have hh := congrArg (MvPolynomial.eval (fun l => if l = k then 1 else 0)) h
      have hz : e ij.1 (s k) - e ij.2 (s k) = 0 := by simpa [G] using hh
      exact hk (sub_eq_zero.mp hz)
    refine (a3r_generic_of_ne_zero G hG).mono ?_
    intro a ha _ he
    apply ha
    change MvPolynomial.eval a G = 0
    simp only [G, map_sum, map_mul, eval_C, eval_X]
    have hh : (∑ l, a l * e ij.1 (s l)) - (∑ l, a l * e ij.2 (s l)) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul] using sub_eq_zero.mpr he
    rw [← Finset.sum_sub_distrib] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  refine (a3r_generic_iInter_fintype _ hpair).mono ?_
  intro a ha i j he
  by_contra hij
  exact ha (i, j) hij he

/-- On one affine neighbourhood, a single actual regular function distinguishes
all points of a finite support.
Source: Hartshorne, Algebraic Geometry, II.2, affine schemes and regular functions. -/
theorem s2e_u1_affine_support_separating_section
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hUa : IsAffineOpen U)
    (S : Finset (ComplexPoint X)) (hS : ∀ x ∈ S, x.underlying ∈ U) :
    ∃ s : Γ(X.left, U), Set.InjOn (fun x : ComplexPoint X => Point.evaluate U s x) S := by
  classical
  letI := s2e_step1_sectionAlgebra X U
  let e (i : S) : Γ(X.left, U) →ₐ[ℂ] ℂ := s2e_step1_pointEvaluation X U i.val
    (s2e_step1_point_preimage X i.val U (hS i.val i.property))
  have hex (ij : S × S) : ∃ s : Γ(X.left, U),
      ij.1 ≠ ij.2 → e ij.1 s ≠ e ij.2 s := by
    by_cases hij : ij.1 = ij.2
    · exact ⟨0, fun h => (h hij).elim⟩
    have he : e ij.1 ≠ e ij.2 := by
      intro he
      apply hij
      apply Subtype.ext
      exact s2e_step1_point_ext_on_affine X U hUa _ _ _ _ he
    have hh : ∃ s, e ij.1 s ≠ e ij.2 s := by
      by_contra h
      push_neg at h
      exact he (AlgHom.ext h)
    obtain ⟨s, hs⟩ := hh
    exact ⟨s, fun _ => hs⟩
  choose s hs using hex
  obtain ⟨a, ha⟩ := (s2e_u1_generic_separating_linear_combination e s
    (fun i j hij => ⟨(i, j), hs (i, j) hij⟩)).nonempty
  refine ⟨∑ l, a l • s l, ?_⟩
  intro x hx y hy he
  have hh : e ⟨x, hx⟩ (∑ l, a l • s l) = e ⟨y, hy⟩ (∑ l, a l • s l) := by
    dsimp only [e]
    rw [s2e_u1_pointEvaluation_eq_evaluate X U x (hS x hx),
      s2e_u1_pointEvaluation_eq_evaluate X U y (hS y hy)]
    exact he
  exact congrArg Subtype.val (ha hh)

end HodgeLean.Foundations.Program
