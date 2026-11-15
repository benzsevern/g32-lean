import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluation
import HodgeLean.Adapters.NormalConeB4aGysinAffineSliceData
import HodgeLean.Adapters.NormalConeB4aGysinPolynomialQuasiFinite
import HodgeLean.Adapters.NormalConeB4aGysinEvaluationIsolation
import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluationCompat

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite length section slice isolates its marked complex point,
without a regular-sequence assumption on the slice. -/
theorem a3b4a_gysin_affine_slice_isolated
    {Z K : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)} [IsNoetherian Z]
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (i : K ⟶ Z) (hi : IsClosedImmersion i) {n : ℕ}
    (U : Z.Opens) (hU : IsAffineOpen U) (g : Fin n → Γ(Z, U))
    (w : ComplexPoint (Over.mk (i ≫ q))) (hw : i.base w.underlying ∈ U)
    (hzero : ∀ j, Point.evaluate (X := Over.mk q) U (g j)
      (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w) = 0)
    (m : ℕ) (hlen : a3b4a_gysin_sliceLength q i U g 0 w = m) :
    ∃ N : Set (ComplexPoint (Over.mk (i ≫ q))), IsOpen N ∧ w ∈ N ∧
      N ⊆ Point.overOpen (X := Over.mk (i ≫ q)) (i ⁻¹ᵁ U) ∧
      ∀ w' ∈ N, (∀ j, Point.evaluate (X := Over.mk q) U (g j)
        (a3b4_anMap (q := i ≫ q) (q' := q) i rfl w') = 0) → w' = w := by
  classical
  letI := hi
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let R := Γ(K, V)
  let A := MvPolynomial (Fin n) ℂ
  letI : Algebra ℂ R := overSpecAlgebra (Over.mk (i ≫ q)) V
  let φ : A →ₐ[ℂ] R := MvPolynomial.aeval (fun j => i.app U (g j))
  letI : Algebra A R := φ.toAlgebra
  haveI : IsScalarTower ℂ A R := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI : LocallyOfFiniteType (i ≫ q) := inferInstance
  haveI : Algebra.FiniteType ℂ R := by
    rw [← RingHom.finiteType_algebraMap]
    change (algebraMap ℂ R).FiniteType
    apply ((i ≫ q).finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hV
      (by simp only [Scheme.Hom.preimage_top, le_top])).comp
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective
  let p := (hV.primeIdealOf ⟨w.underlying, hw⟩).asIdeal
  let E : R →ₐ[ℂ] ℂ := a3b4a_gysin_affine_evaluation (i ≫ q) V w hw
  have hE (s : R) : E s = Point.evaluate (X := Over.mk (i ≫ q)) V s w :=
    Point.evaluationHom_apply (X := Over.mk (i ≫ q)) V ⟨w, hw⟩ s
  have hkernel : RingHom.ker E = p := a3b4a_gysin_affine_point_kernel V hV w hw
  have hzeroR (j : Fin n) : E (algebraMap A R (MvPolynomial.X j)) = 0 := by
    change E (φ (MvPolynomial.X j)) = 0
    rw [MvPolynomial.aeval_X, hE]
    let f : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
    have he := Point.evaluate_map f U (g j) w
    exact he.symm.trans (hzero j)
  let L := Localization.AtPrime p
  have hcoord (j : Fin n) : algebraMap A L (MvPolynomial.X j) =
      algebraMap R L (i.app U (g j)) := by
    rw [IsScalarTower.algebraMap_apply A R L]
    change algebraMap R L (φ (MvPolynomial.X j)) = _
    rw [MvPolynomial.aeval_X]
  obtain ⟨_, hlengthEq⟩ :=
    a3b4a_gysin_affine_slice_data V hV w.underlying hw (fun j => i.app U (g j))
  have hseq : a3b4a_gysin_sliceSequence q i U g 0 w.underlying hw =
      List.ofFn (fun j => K.presheaf.germ V w.underlying hw (i.app U (g j))) := by
    simp only [a3b4a_gysin_sliceSequence, Pi.zero_apply, map_zero, sub_zero]
    rfl
  have hlen₀ := hlen
  rw [a3b4a_gysin_sliceLength, dif_pos hw, hseq] at hlen₀
  have hlength := hlengthEq.symm.trans hlen₀
  have hgl : List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j)) =
      List.ofFn (fun j => algebraMap R L (i.app U (g j))) := congrArg List.ofFn (funext hcoord)
  letI : Algebra.QuasiFiniteAt A p := a3b4a_gysin_polynomial_slice_quasiFinite p E hkernel hzeroR
    m (by
      change Module.length L (L ⧸ Ideal.ofList
        (List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j)))) = m
      rw [hgl]
      exact hlength)
  letI : Algebra.FiniteType A R := Algebra.FiniteType.of_restrictScalars_finiteType ℂ A R
  obtain ⟨N, hN, hEN, hisolate⟩ := a3b4a_gysin_quasiFinite_evaluation_isolated
    (B := A) p E hkernel
  let e := a3b4a_gysin_affine_point_homeomorph (i ≫ q) V hV
  have he (z : {z : ComplexPoint (Over.mk (i ≫ q)) // z.underlying ∈ V}) (s : R) :
      e z s = Point.evaluate (X := Over.mk (i ≫ q)) V s z.val :=
    a3b4a_gysin_affine_point_homeomorph_apply (i ≫ q) V hV z s
  have heE : e ⟨w, hw⟩ = E := by
    apply AlgHom.ext
    intro s
    exact (he _ s).trans (hE s).symm
  let N₀ := Subtype.val '' (e ⁻¹' N)
  have hN₀ : IsOpen N₀ :=
    (Point.isOpen_overOpen (X := Over.mk (i ≫ q)) V).isOpenEmbedding_subtypeVal.isOpenMap
      _ (hN.preimage e.continuous)
  refine ⟨N₀, hN₀, ?_, ?_, ?_⟩
  · refine ⟨⟨w, hw⟩, ?_, rfl⟩
    change e ⟨w, hw⟩ ∈ N
    rw [heE]
    exact hEN
  · rintro _ ⟨z, _, rfl⟩
    exact z.property
  · rintro _ ⟨z, hzN, rfl⟩ hz
    have hres : (e z).comp (IsScalarTower.toAlgHom ℂ A R) =
        E.comp (IsScalarTower.toAlgHom ℂ A R) := by
      apply MvPolynomial.algHom_ext
      intro j
      change e z (φ (MvPolynomial.X j)) = E (φ (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, he, hE]
      let f : Over.mk (i ≫ q) ⟶ Over.mk q := Over.homMk i rfl
      exact (Point.evaluate_map f U (g j) z.val).symm.trans
        ((hz j).trans ((hzero j).symm.trans (Point.evaluate_map f U (g j) w)))
    exact congrArg Subtype.val (e.injective ((hisolate (e z) hzN hres).trans heE.symm))

end HodgeLean.Adapters
