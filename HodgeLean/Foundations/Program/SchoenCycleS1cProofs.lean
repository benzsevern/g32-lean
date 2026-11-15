import HodgeLean.Foundations.Program.SchoenCycleS1cSingleBranch
import HodgeLean.Foundations.Program.SchoenCycleS1b
import HodgeLean.Foundations.Program.SchoenCyclePoleClearing

/-! # Paired slice geometry
Implication from the native paired family and retained finite categorical quotient
to the stated slice geometry. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- Both actual branch ideals restrict to the reduced residue-coordinate hyperplane.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.4, pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_chain_paired_branch_ideals_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R))
    (hpair : ∀ i j,
      b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
        (w i) (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (n : ℕ) (hn : 2 * k = n + 1) (j : Fin r) :
    let : ConnectedSpace (ComplexPoint Z) :=
      AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let γn : g3_power Z (n + 1) ⟶ B :=
      eqToHom (congrArg (g3_power Z) hn.symm) ≫ γ
    let H : PP.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Point.underlying ''
        {R : ComplexPoint PP | ∃ (v : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) ×
          (Fin r → ℂ)) (hv : v ≠ 0),
          ep.symm R = Projectivization.mk ℂ v hv ∧ v.2 j = 0}))
    (s2c_branchIdeal Z B n γn (y ⟨2 * j.val, by omega⟩)).comap ℓ.left = H ∧
      (s2c_branchIdeal Z B n γn (y ⟨2 * j.val + 1, by omega⟩)).comap ℓ.left = H := by
  constructor
  · exact s2e_paired_single_branch_ideal Z B k r hr y hy w hres horder hout hgenus
      hd γ hγ hsurj hquot ℓ hℓ hpair n hn j false
  · exact s2e_paired_single_branch_ideal Z B k r hr y hy w hres horder hout hgenus
      hd γ hγ hsurj hquot ℓ hℓ hpair n hn j true

end HodgeLean.Foundations.Program
