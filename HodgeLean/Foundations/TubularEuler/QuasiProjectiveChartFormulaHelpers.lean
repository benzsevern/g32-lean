import HodgeLean.Foundations.TubularEuler.QuasiProjectiveRatioHelpers
import HodgeLean.Foundations.TubularEuler.ProjectorPermutationHelpers
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! # Retained chart formula from regular projective ratios

The homogeneous coordinate selected at the given point stays nonzero nearby.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.ComplexPoint AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
open scoped ContDiff
namespace HodgeLean.Foundations.TubularEuler

theorem retained_projector_ratio_chart_formula
    (X : Over (Spec ↧ℂ)) (d N : ℕ) [SmoothOfRelativeDimension d X.hom]
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ)))
    (z : ComplexPoint X) (a : Fin d → ℂ) (ha : a ∈ (localChart X d z).target) :
    ∃ (c : (Fin d → ℂ) → (Fin N → ℂ))
      (L : (Fin (N+1) → Fin (N+1) → ℂ) ≃L[ℝ]
        (Fin (N+1) → Fin (N+1) → ℂ)),
      ContDiffAt ℝ ω c a ∧
      (fun b => quasiProjectiveProjector e ((localChart X d z).symm b))
        =ᶠ[𝓝 a] (fun b => L (affineHermitianProjector (c b))) := by
  classical
  let P := fun b => Point.map e ((localChart X d z).symm b)
  obtain ⟨⟨v, hv⟩, hPv⟩ := surjective_vectorToComplexPoint (P a)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hiP : P a ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1 := by
    rw [← hPv]
    exact (s2e_standardProjectiveAffineOpen_mem_iff v hv i).mpr hi
  let q := fun b j => Point.evaluate (s2e_standardProjectiveAffineOpen i).1
    (projectiveRatioSection i j) (P b)
  have hq (j) : AnalyticAt ℂ (fun b => q b j) a :=
    retained_projectiveRatio_analyticAt X d N e z a ha i j hiP
  let σ : Equiv.Perm (Fin (N+1)) := Equiv.swap 0 i
  let c : (Fin d → ℂ) → Fin N → ℂ := fun b j => q b (σ j.succ)
  let L : (Fin (N+1) → Fin (N+1) → ℂ) ≃L[ℝ]
      (Fin (N+1) → Fin (N+1) → ℂ) := projectorMatrixPermutation σ
  refine ⟨c, L, ?_, ?_⟩
  · have hc : AnalyticAt ℂ c a := by
      apply AnalyticAt.pi
      intro j
      exact hq (σ j.succ)
    exact hc.contDiffAt.restrict_scalars ℝ
  · have hP : ContinuousAt P a :=
      (Point.continuous_map e).continuousAt.comp ((localChart X d z).continuousAt_symm ha)
    have hn : ∀ᶠ b in 𝓝 a, P b ∈ Point.overOpen (s2e_standardProjectiveAffineOpen i).1 :=
      hP ((Point.isOpen_overOpen _).mem_nhds hiP)
    filter_upwards [hn] with b hb
    have hqi : q b i = 1 := by
      obtain ⟨⟨w, hw⟩, hPw⟩ := surjective_vectorToComplexPoint (P b)
      change vectorToComplexPoint w hw = P b at hPw
      have hwi : w i ≠ 0 := by
        apply (s2e_standardProjectiveAffineOpen_mem_iff w hw i).mp
        rwa [hPw]
      change Point.evaluate _ _ (P b) = 1
      rw [← hPw, projectiveRatioSection_evaluate w hw i i hwi, div_self hwi]
    have hvec : (fun j => q b (σ j)) = Fin.cons 1 (c b) := by
      ext j
      refine Fin.cases ?_ (fun _ => rfl) j
      simpa only [σ, Equiv.swap_apply_left, Fin.cons_zero] using hqi
    change projectiveHermitianProjector N (P b) = L (affineHermitianProjector (c b))
    rw [projectiveHermitianProjector_ratio_formula N (P b) i hb]
    change hermitianProjector (q b) = L (hermitianProjector (Fin.cons 1 (c b)))
    rw [← hvec, hermitianProjector_permutation]
    ext j k
    change hermitianProjector (q b) j k = hermitianProjector (q b) (σ (σ j)) (σ (σ k))
    simp only [σ, Equiv.swap_apply_self]

end HodgeLean.Foundations.TubularEuler
