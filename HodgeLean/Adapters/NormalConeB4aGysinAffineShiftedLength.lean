import HodgeLean.Adapters.NormalConeB4aGysinPullConstant
import HodgeLean.Adapters.NormalConeB4aGysinParameterIdeal
import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluation
import HodgeLean.Adapters.NormalConeB4aGysinAffineSliceData
import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationLength

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- Every shifted section slice length is the corresponding affine
polynomial evaluation quotient length in the full source local ring. -/
theorem a3b4a_gysin_affine_shifted_slice_length
    {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (i : K ⟶ Z) (hi : IsClosedImmersion i) {n : ℕ}
    (U : Z.Opens) (hU : IsAffineOpen U) (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ)
    (w : ComplexPoint (Over.mk (i ≫ q))) (hw : i.base w.underlying ∈ U) :
    let V := i ⁻¹ᵁ U
    let R := Γ(K, V)
    letI : Algebra ℂ R := overSpecAlgebra (Over.mk (i ≫ q)) V
    let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R := MvPolynomial.aeval (fun j => i.app U (g j))
    letI : Algebra (MvPolynomial (Fin n) ℂ) R := φ.toAlgebra
    a3b4a_gysin_sliceLength q i U g a w =
      a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a)
        (a3b4a_gysin_affine_evaluation (i ≫ q) V w hw) := by
  classical
  letI := hi
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let R := Γ(K, V)
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra ℂ R := overSpecAlgebra (Over.mk (i ≫ q)) V
  let φ : A →ₐ[ℂ] R := MvPolynomial.aeval (fun j => i.app U (g j))
  letI : Algebra A R := φ.toAlgebra
  letI : IsScalarTower ℂ A R := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let p := (hV.primeIdealOf ⟨w.underlying, hw⟩).asIdeal
  let L := Localization.AtPrime p
  let E := a3b4a_gysin_affine_evaluation (i ≫ q) V w hw
  have hkernel : RingHom.ker E = p := a3b4a_gysin_affine_point_kernel V hV w hw
  have hcoord (j : Fin n) :
      algebraMap A L (MvPolynomial.X j - MvPolynomial.C (a j)) =
        algebraMap R L (i.app U (g j - a3b4a_gysin_sectionConst q U (a j))) := by
    rw [IsScalarTower.algebraMap_apply A R L]
    apply congrArg (algebraMap R L)
    change φ (MvPolynomial.X j - MvPolynomial.C (a j)) =
      i.app U (g j - a3b4a_gysin_sectionConst q U (a j))
    rw [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, map_sub,
      a3b4a_gysin_pull_sectionConst]
    rfl
  have hid : (RingHom.ker (MvPolynomial.aeval a)).map (algebraMap A L) =
      Ideal.ofList (List.ofFn (fun j =>
        algebraMap R L (i.app U (g j - a3b4a_gysin_sectionConst q U (a j))))) := by
    rw [← a3b4a_gysin_parameter_ideal a, Ideal.map_ofList, List.map_ofFn]
    exact congrArg Ideal.ofList (congrArg List.ofFn (funext hcoord))
  have hlength := (a3b4a_gysin_affine_slice_data V hV w.underlying hw
    (fun j => i.app U (g j - a3b4a_gysin_sectionConst q U (a j)))).2
  have hactual : a3b4a_gysin_sliceLength q i U g a w =
      Module.length L (L ⧸ (RingHom.ker (MvPolynomial.aeval a)).map (algebraMap A L)) := by
    rw [a3b4a_gysin_sliceLength, dif_pos hw, hid]
    exact hlength
  letI : (RingHom.ker E).IsPrime := RingHom.ker_isPrime E
  have htransport (p' : Ideal R) [p'.IsPrime] (hp' : p' = RingHom.ker E) :
      Module.length (Localization.AtPrime p')
        (Localization.AtPrime p' ⧸ (RingHom.ker (MvPolynomial.aeval a)).map
          (algebraMap A (Localization.AtPrime p'))) =
      a3b4a_gysin_evaluationSliceLength (MvPolynomial.aeval a) E := by
    subst p'
    rfl
  exact hactual.trans (htransport p hkernel.symm)

end HodgeLean.Adapters
