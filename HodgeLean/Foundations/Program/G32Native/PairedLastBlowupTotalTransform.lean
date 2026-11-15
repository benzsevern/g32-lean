import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagramGeometry
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Identifying the residual union with the last total transform -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The last total-transform ideal identity constructs its actual
cartesian square with the penultimate immersion. Flatness is unnecessary.
Source: Hartshorne, Algebraic Geometry, II.3, scheme-theoretic inverse image;
II.7.13, affine blowup charts. -/
theorem paired_last_total_transform_pullback
    {base : Scheme.{0}} {P V : Over base} (i : P ⟶ V) [IsClosedImmersion i.left]
    (J : V.left.IdealSheafData) {Q X : Scheme.{0}}
    (i₀ : Q ⟶ X) [IsClosedImmersion i₀] (σ : V.left ⟶ X)
    (hI : i₀.ker.comap σ = i.left.ker ⊓ J) :
    ∃ p : (residualUnion i J).left ⟶ Q,
      IsPullback p (residualUnionι i J).left i₀ σ := by
  let t := (residualUnionι i J).left
  have hT : i₀.ker.comap σ = t.ker := by
    change i₀.ker.comap σ = (i.left.ker ⊓ J).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hI
  have hle : i₀.ker ≤ (t ≫ σ).ker := by
    rw [← Scheme.IdealSheafData.map_ker, ← hT]
    exact Scheme.IdealSheafData.le_map_comap _ _
  let p := IsClosedImmersion.lift i₀ (t ≫ σ) hle
  have hp : p ≫ i₀ = t ≫ σ := IsClosedImmersion.lift_fac _ _ _
  exact ⟨p, (isPullback_of_isClosedImmersion t i₀ p σ hp.symm hT).flip⟩

#print axioms paired_last_total_transform_pullback

end HodgeLean.Foundations.Program.G32Native
