import HodgeLean.Foundations.BundleThom.Defs
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassLinearInvariance

/-! # Complex linear invariance of the normal orientation coclass

The matrix isotopy acts on the actual punctured pair before passing to cohomology.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- Homotopic actual pair maps induce the same rational relative cohomology pullback.
Source: Hatcher, Algebraic Topology, §3.1, homotopy invariance and universal coefficients. -/
theorem i1_relativeCohomologyMap_homotopy {P Q : TopPair} {f g : P ⟶ Q}
    (H : TopPair.Homotopy f g) (n : ℕ) (u : RelativeCohomology ℚ Q n) :
    relativeCohomologyMap ℚ n f u = relativeCohomologyMap ℚ n g u := by
  apply (relativeCohomologyEquivDualHomology ℚ P n).injective
  ext z
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    H.relativeHomologyMap_apply_eq]

/-- Every invertible complex matrix fixes all rational cohomology classes of the normal punctured pair.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex orientation. -/
theorem i1_complexMatrix_relativeCohomologyMap (k n : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.det ≠ 0)
    (u : RelativeCohomology ℚ (puncturedPair ℂ k) n) :
    relativeCohomologyMap ℚ n (complexMatrixPuncturedPairMap k A hA) u = u := by
  let H := (Matrix.nonempty_complexIsotopyToOne A hA).some
  have h := i1_relativeCohomologyMap_homotopy (complexMatrixPuncturedPairHomotopy k hA H) n u
  simpa only [relativeCohomologyMap_id, LinearMap.id_apply] using h.symm

/-- Invertible complex normal coordinate changes preserve the specified orientation coclass.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, complex Thom orientation. -/
theorem i1_complexMatrix_normalizedPointCoclass (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) (hA : A.det ≠ 0) :
    relativeCohomologyMap ℚ (2 * k) (complexMatrixPuncturedPairMap k A hA)
      (normalizedPointCoclass k) = normalizedPointCoclass k :=
  i1_complexMatrix_relativeCohomologyMap k (2 * k) A hA (normalizedPointCoclass k)

end HodgeLean.Foundations.BundleThom
