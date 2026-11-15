import HodgeLean.Foundations.BundleThom.ProductMatrixHomotopyHelpers

/-! # Local invariance of the actual product normal orientation

Base-dependent invertible complex frame changes preserve normal pullbacks on an open neighbourhood of each base point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- Constant complex frame changes preserve every relative coclass pulled back from the actual normal model.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation invariance. -/
theorem i1_productMatrixNormalMap_constant_pullback (B : Type) [TopologicalSpace B]
    (k n : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) (hd : A.det ≠ 0)
    (u : RelativeCohomology ℚ (puncturedPair ℂ k) n) :
    relativeCohomologyMap ℚ n
      (i1_productMatrixNormalMap k (fun _ : B => A) continuous_const (fun _ => hd)) u =
      relativeCohomologyMap ℚ n (i1_productNormalProjection B k) u := by
  rw [i1_productMatrixNormalMap_constant, relativeCohomologyMap_comp, LinearMap.comp_apply,
    i1_complexMatrix_relativeCohomologyMap]

/-- Every actual continuous invertible complex matrix family preserves normal coclass pullbacks locally on the base.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local complex frame comparison. -/
theorem i1_productMatrixNormalMap_locally_pullback {B : Type} [TopologicalSpace B]
    (k : ℕ) (A : B → Matrix (Fin k) (Fin k) ℂ) (hA : Continuous A)
    (hd : ∀ b, (A b).det ≠ 0) (b : B) :
    ∃ U : Opens B, b ∈ U ∧ ∀ (n : ℕ) (u : RelativeCohomology ℚ (puncturedPair ℂ k) n),
      relativeCohomologyMap ℚ n
        (i1_productMatrixNormalMap k (fun x : U => A x.1)
          (hA.comp continuous_subtype_val) (fun x => hd x.1)) u =
        relativeCohomologyMap ℚ n (i1_productNormalProjection U k) u := by
  obtain ⟨U, hb, hU⟩ := i1_matrixInterpolation_locally_invertible k A hA b (hd b)
  refine ⟨U, hb, ?_⟩
  let H : unitInterval × U → Matrix (Fin k) (Fin k) ℂ :=
    fun p => i1_matrixInterpolation k A b (p.1, p.2.1)
  have hH : Continuous H := (i1_matrixInterpolation_continuous k A hA b).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hdH : ∀ p, (H p).det ≠ 0 := fun p => hU p.1 p.2
  have hstart : ∀ x : U, H (0, x) = A b := by
    intro x
    simp [H, i1_matrixInterpolation]
  have hend : ∀ x : U, H (1, x) = A x.1 := by
    intro x
    simp [H, i1_matrixInterpolation]
  let h := i1_productMatrixNormalHomotopy k (fun _ : U => A b) (fun x : U => A x.1)
    continuous_const (hA.comp continuous_subtype_val) (fun _ => hd b) (fun x => hd x.1)
    H hH hdH hstart hend
  intro n u
  exact (i1_relativeCohomologyMap_homotopy h n u).symm.trans
    (i1_productMatrixNormalMap_constant_pullback U k n (A b) (hd b) u)

end HodgeLean.Foundations.BundleThom
