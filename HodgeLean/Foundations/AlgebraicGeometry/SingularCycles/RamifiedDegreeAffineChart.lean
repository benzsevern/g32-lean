import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeDimension
import HodgeLean.Adapters.NormalConeB4aGysinAffineEvaluationCompat

/-! # Actual point charts from affine étale coordinate maps

The affine point homeomorphism and the étale evaluation chart give a chart
on the original complex point space whose coordinates are regular sections.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexAlgHom HodgeLean.Adapters HodgeLean.Foundations.Analytic
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem affine_etale_point_chart
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) (x : ComplexPoint X) (hxU : x.underlying ∈ U)
    (d : ℕ) :
    letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
    ∀ φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, U), φ.toRingHom.Etale →
      ∃ e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ),
        x ∈ e.source ∧ e.source ⊆ Point.overOpen (X := X) U ∧
        ∀ y ∈ e.source, ∀ k, e y k = Point.evaluate U (φ (MvPolynomial.X k)) y := by
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  intro φ hφ
  let B := Γ(X.left, U)
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := φ.toAlgebra
  letI : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) B :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := hφ
  let H := a3b4a_gysin_affine_point_homeomorph X.hom U hU
  let xU : {y : ComplexPoint X // y.underlying ∈ U} := ⟨x, hxU⟩
  let u := H xU
  let E := H.toOpenPartialHomeomorph.trans (etaleAlgHomProjectionChart (n := d) B u)
  let hf := (Point.isOpen_overOpen (X := X) U).isOpenEmbedding_subtypeVal
  let e := E.lift_openEmbedding hf
  have hxE : xU ∈ E.source :=
    ⟨Set.mem_univ _, mem_etaleAlgHomProjectionChart_source (n := d) B u⟩
  refine ⟨e, ⟨xU, hxE, rfl⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨yU, _, rfl⟩ := hy
    exact yU.2
  · intro y hy k
    obtain ⟨yU, hyU, rfl⟩ := hy
    change (E.lift_openEmbedding hf) (Subtype.val yU) k = _
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply E hf]
    change etaleAlgHomProjectionChart (n := d) B u (H yU) k = _
    rw [etaleAlgHomProjectionChart_apply_of_mem (n := d) B u (H yU) hyU.2]
    change H yU (φ (MvPolynomial.X k)) = _
    exact a3b4a_gysin_affine_point_homeomorph_apply X.hom U hU yU (φ (MvPolynomial.X k))

theorem affine_etale_holomorphic_point_chart
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) (x : ComplexPoint X) (hxU : x.underlying ∈ U)
    (d : ℕ) :
    letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
    ∀ (φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, U)), φ.toRingHom.Etale →
      (∀ k, Point.evaluate U (φ (MvPolynomial.X k)) x = 0) →
      ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)),
        a3b4_IsHolChart X.hom e ∧ x ∈ (pointChart e).source ∧ pointChart e x = 0 ∧
          (pointChart e).source ⊆ Point.overOpen (X := X) U ∧
          ∀ y ∈ (pointChart e).source, ∀ k,
            pointChart e y k = Point.evaluate U (φ (MvPolynomial.X k)) y := by
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  letI : LocallyOfFiniteType (Over.mk X.hom).hom := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (Over.mk X.hom).hom := ‹QuasiCompact X.hom›
  letI : IsSeparated (Over.mk X.hom).hom := ‹IsSeparated X.hom›
  intro φ hφ hzero
  obtain ⟨a, hxa, hsource, hvalues⟩ := affine_etale_point_chart X U hU x hxU d φ hφ
  let H := (Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin d → ℂ)).symm
  let e := a.trans H.toOpenPartialHomeomorph
  have he : a3b4_IsHolChart X.hom e := by
    constructor
    · intro j
      exact Fin.elim0 j
    · intro k
      have hf := anrem_isHolFun_restrict (f4_analytification (Over.mk X.hom))
        (fun y (hy : y ∈ e.source) => hsource hy.1)
        (f4_isHolFun_evaluate (Over.mk X.hom) U (φ (MvPolynomial.X k)))
      convert hf using 1
      funext y
      exact hvalues y.1 y.2.1 k
  have hx : x ∈ (pointChart e).source := ⟨⟨hxa, by trivial⟩, by trivial⟩
  refine ⟨e, he, hx, ?_, ?_, ?_⟩
  · funext k
    exact (hvalues x hxa k).trans (hzero k)
  · intro y hy
    exact hsource hy.1.1
  · intro y hy k
    exact hvalues y hy.1.1 k

end AlgebraicGeometry.SingularCycles
