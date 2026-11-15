import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeEtaleParameters
import HodgeLean.Adapters.NormalConeB4aGysinAffineStalk
import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluation
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeRegularSystem
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeDimension

/-! # Centered affine étale parameters in the actual scheme stalk

The affine stalk equivalence transports the explicit localized coordinate
ideal to the maximal ideal of the original target stalk.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem affine_etale_parameter_germs_generate_maximal
    (X : Over (Spec ↧ℂ)) (U : X.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hxU : x.underlying ∈ U) (d : ℕ) :
    letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
    ∀ (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, U)), φ.toRingHom.Etale →
      (∀ j, Point.evaluate U (φ (MvPolynomial.X j)) x = 0) →
      Ideal.ofList (List.ofFn fun j => X.left.presheaf.germ U x.underlying hxU
        (φ (MvPolynomial.X j))) = IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) := by
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  intro φ hφ hzero
  let B := Γ(X.left, U)
  let A := MvPolynomial (Fin d) ℂ
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra.Etale A B := hφ
  let u := a3b4a_gysin_affine_evaluation X.hom U x hxU
  let q := (hU.primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
  let p := RingHom.ker (MvPolynomial.aeval (R := ℂ) (0 : Fin d → ℂ))
  have hkernel : RingHom.ker u = q := a3b4a_gysin_affine_point_kernel U hU x hxU
  have hcenter : u.comp φ = MvPolynomial.aeval (0 : Fin d → ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    change u (φ (MvPolynomial.X j)) = MvPolynomial.aeval (0 : Fin d → ℂ) (MvPolynomial.X j)
    rw [MvPolynomial.aeval_X]
    exact (Point.evaluationHom_apply (X := X) U ⟨x, hxU⟩ (φ (MvPolynomial.X j))).trans (hzero j)
  letI : q.LiesOver p := by
    constructor
    change p = q.comap φ.toRingHom
    rw [← hkernel]
    change p = RingHom.ker (u.toRingHom.comp φ.toRingHom)
    exact (congrArg (fun v : A →ₐ[ℂ] ℂ => RingHom.ker v) hcenter).symm
  obtain ⟨e, he⟩ := a3b4a_gysin_affine_stalk_equiv U hU x.underlying hxU
  let I := Ideal.ofList (List.ofFn fun j => X.left.presheaf.germ U x.underlying hxU
    (φ (MvPolynomial.X j)))
  have hmap : I.map e.toRingHom = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    calc
      _ = Ideal.ofList (List.ofFn fun j =>
          algebraMap A (Localization.AtPrime q) (MvPolynomial.X j)) := by
        rw [Ideal.map_ofList, List.map_ofFn]
        apply congrArg Ideal.ofList
        apply congrArg List.ofFn
        funext j
        exact he (φ (MvPolynomial.X j))
      _ = _ := etale_zero_parameters_generate_local_maximal q
  have hmapMax : (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)).map e.toRingHom =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := IsLocalRing.map_ringEquiv_maximalIdeal e
  have hh := congrArg (Ideal.comap e.toRingHom) (hmap.trans hmapMax.symm)
  have hbackI : (I.map e.toRingHom).comap e.toRingHom = I :=
    Ideal.comap_map_of_bijective e.toRingHom e.bijective
  have hbackM : ((IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)).map e.toRingHom).comap
      e.toRingHom = IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) :=
    Ideal.comap_map_of_bijective e.toRingHom e.bijective
  exact hbackI.symm.trans (hh.trans hbackM)

theorem affine_etale_parameter_germs_are_regular
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ (pointChart e).source)
    (U : X.left.Opens) (hU : IsAffineOpen U) (hxU : x.underlying ∈ U) :
    letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
    ∀ (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, U)), φ.toRingHom.Etale →
      (∀ j, Point.evaluate U (φ (MvPolynomial.X j)) x = 0) →
      RingTheory.Sequence.IsRegular (X.left.presheaf.stalk x.underlying)
        (List.ofFn fun j => X.left.presheaf.germ U x.underlying hxU (φ (MvPolynomial.X j))) := by
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  intro φ hφ hzero
  obtain ⟨V, _hV, hxV, hdimV⟩ := exists_affine_of_point_chart_dimension X d e he x hx
  letI : SmoothOfRelativeDimension d (ComplexPoint.openScheme X V).hom := hdimV
  have hdim := a3b4g_ringKrullDim_stalk_of_openScheme X V (m := d) x hxV
  letI : IsRegularLocalRing (X.left.presheaf.stalk x.underlying) :=
    Smooth.isRegularLocalRing_stalk_complex (f := X.hom) x.underlying
  exact regular_sequence_of_maximal_generators (X.left.presheaf.stalk x.underlying) d _
    hdim List.length_ofFn (affine_etale_parameter_germs_generate_maximal X U hU x hxU d φ hφ hzero)

end AlgebraicGeometry.SingularCycles
