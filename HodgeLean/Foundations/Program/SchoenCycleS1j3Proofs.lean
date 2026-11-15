import HodgeLean.Foundations.Program.SchoenCycleMixedBranchPrincipality
import HodgeLean.Foundations.Program.SchoenCycleMarkedGeneratorUnit
import HodgeLean.Foundations.Program.SchoenCycleMixedBlockProducts
import HodgeLean.Foundations.Program.SchoenCycleS1j1
import HodgeLean.Foundations.Program.SchoenCycleS1i3
import HodgeLean.Foundations.Program.SchoenCycleS1i4
import HodgeLean.Foundations.Program.SchoenCycleBranchOffSupport

/-! # Mixed branch equations and analytic generators
Implication from the explicit inputs to the stated local comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open Filter Topology Manifold HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

/-- The actual insertion image has a local generator equal to a unit times its block constant coefficient.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_branch_generator_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    [SmoothOfRelativeDimension n B.hom]
    (x : ComplexPoint (g3_power Z n)) (b : ℕ) (m : Fin b → ℕ)
    (hm : ∀ a, 0 < m a) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a)
    (e : OpenPartialHomeomorph (ComplexPoint B) (Fin n → ℂ))
    (he : ∀ᶠ q in 𝓝 x, ∀ a (j : Fin (m a)),
      e (Point.map γ q) (ι ⟨a, j⟩) =
        (-1 : ℂ) ^ (m a - j.val) *
        aeval (fun i : Fin (m a) =>
          (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)).symm
            (extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a)
              (Point.map (g3_proj Z n (ι ⟨a, i⟩)) q) -
             extChartAt 𝓘(ℂ, Fin 1 → ℂ) (p a) (p a)))
          (esymm (Fin (m a)) ℂ (m a - j.val)))
    (q : ℕ) (hq : n = q + 1) (a : Fin b) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    ∃ (U : B.left.affineOpens) (_hU : γ.left x.underlying ∈ U.1)
      (c : Γ(B.left, U.1)) (η : (Fin n → ℂ) → ℂ),
      (s2c_branchIdeal Z B q γq (p a)).ideal U = Ideal.span {c} ∧
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0,
        let v := (ComplexPoint.localChart B n (Point.map γ x)).symm
          (ComplexPoint.localChart B n (Point.map γ x) (Point.map γ x) + z)
        Point.evaluate U.1 c v = η z * e v (ι ⟨a, ⟨0, hm a⟩⟩)) := by
  subst n
  change ∃ (U : B.left.affineOpens) (_ : γ.left x.underlying ∈ U.1)
    (c : Γ(B.left, U.1)) (η : (Fin (q + 1) → ℂ) → ℂ),
    (s2c_branchIdeal Z B q γ (p a)).ideal U = Ideal.span {c} ∧
      AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧ _
  let N := q + 1
  letI : Smooth B.hom := SmoothOfRelativeDimension.smooth N B.hom
  let L := b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ)
  let y := Point.map γ x
  let C := ComplexPoint.localChart B N y
  let Q := fun z => Point.map γ (s2e_curvePowerRootChart Z N x L z)
  let S := Finset.univ.image (fun j : Fin (m a) => ι ⟨a, j⟩)
  have hS := s2e_mixed_block_indices Z N x b m ι p hp hx a
  obtain ⟨U, hyU, c, hc, u, hu⟩ :=
    s2e_mixed_branch_affine_generator Z B q γ hγ hquot x (p a) S hS
  obtain ⟨e₀, hy₀, he₀0, ha₀, _hai₀, he₀⟩ :=
    s2e_mixed_coefficient_neighbourhood Z B N γ hγ hquot x b m hm ι p hp hx
  have hr := s2e_mixed_coefficients_on_root_chart Z B N γ x b m ι p hx e he
  have hr₀ := s2e_mixed_coefficients_on_root_chart Z B N γ x b m ι p hx e₀ he₀
  have hmap : Filter.map Q (𝓝 0) = 𝓝 y :=
    s2e_root_chart_quotient_map_nhds Z B N γ x b m ι e₀ hy₀ he₀0 hr₀
  have heq : e =ᶠ[𝓝 y] e₀ := by
    rw [← hmap]
    change ∀ᶠ z in 𝓝 0, e (Q z) = e₀ (Q z)
    filter_upwards [hr, hr₀] with z hz hz₀
    funext i
    obtain ⟨⟨l, j⟩, rfl⟩ := ι.surjective i
    exact (hz l j).trans (hz₀ l j).symm
  have hE : AnalyticAt ℂ (fun z => e (C.symm (C y + z))) 0 := by
    apply ha₀.congr
    have hh : (fun z => e (C.symm (C y + z))) =ᶠ[𝓝 0]
        (fun z => e₀ (C.symm (C y + z))) :=
      (s2e_centered_native_chart_tendsto B N y).eventually heq
    exact hh.symm
  let i₀ := ι ⟨a, ⟨0, hm a⟩⟩
  let E := fun v : ComplexPoint B => e v i₀
  have hG : AnalyticAt ℂ (fun z => E (C.symm (C y + z))) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i₀).analyticAt _).comp hE
  have hprod : ∀ᶠ z in 𝓝 0, E (Q z) = (-1 : ℂ) ^ m a * ∏ i ∈ S, z i := by
    filter_upwards [hr] with z hz
    have hh := hz a ⟨0, hm a⟩
    simp only [Fin.val_zero, Nat.sub_zero] at hh
    rw [s2e_mixed_block_constant_product N b m ι a z] at hh
    exact hh
  letI : SmoothOfRelativeDimension N (g3_power Z N).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power Z 1 N
  obtain ⟨η, hη, hη0, hηeq⟩ := s2e_marked_generator_native_unit
    Z B N N γ x S U.1 hyU c u hu E hG ((-1 : ℂ) ^ m a)
    (pow_ne_zero _ (by norm_num)) hprod hmap
  exact ⟨U, hyU, c, η, hc, hη, hη0, hηeq⟩

/-- A tuple with no marked coordinate lies in an affine open where the actual branch ideal is the unit ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15. -/
theorem s2e_branch_equation_off_support_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (x : ComplexPoint (g3_power Z n)) (p : ComplexPoint Z)
    (hx : ∀ i, Point.map (g3_proj Z n i) x ≠ p)
    (q : ℕ) (hq : n = q + 1) :
    let γq : g3_power Z (q + 1) ⟶ B := eqToHom (congrArg (g3_power Z) hq.symm) ≫ γ
    ∃ (U : B.left.affineOpens), γ.left x.underlying ∈ U.1 ∧
      (s2c_branchIdeal Z B q γq p).ideal U = ⊤ := by
  subst n
  change ∃ U : B.left.affineOpens, γ.left x.underlying ∈ U.1 ∧
    (s2c_branchIdeal Z B q γ p).ideal U = ⊤
  exact s2e_affine_ideal_eq_top_of_not_mem_support _ _
    (s2e_branch_support_excludes_unmarked_tuple Z B q γ hγ hquot x p hx)

end HodgeLean.Foundations.Program
