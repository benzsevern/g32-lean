import HodgeLean.Foundations.TubularEuler.SurjectiveScalarTensorHelpers
import HodgeLean.Foundations.TubularEuler.CenteredCoordinateHelpers
import HodgeLean.Foundations.TubularEuler.ParameterDifferentialKernelHelpers
import HodgeLean.Foundations.TubularEuler.AnalyticConormalDifferentialHelpers

/-! # Faithfulness of the analytic differential on actual maximal cotangents

The original regular chart parameters identify zero analytic differential
with membership in the square of the actual maximal ideal.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem actualStalkDifferential_zero_iff_mem_square
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (a : X.left.presheaf.stalk x.underlying)
    (ha : a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) :
    actualStalkDifferential X d z x hx a = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2 := by
  let A := X.left.presheaf.stalk x.underlying
  have hker : RingHom.ker x.stalkHom.hom = IsLocalRing.maximalIdeal A := by
    ext b
    exact ⟨a3b4g_mem_of_stalkHom_eq_zero x b, a3b4g_stalkHom_eq_zero_of_mem x b⟩
  let D : A →+ ((Fin d → ℂ) →L[ℂ] ℂ) := {
    toFun := actualStalkDifferential X d z x hx
    map_zero' := actualStalkDifferential_square_zero X d z x hx 0 (zero_mem _)
    map_add' := actualStalkDifferential_add X d z x hx }
  constructor
  · intro hzero
    have h := differential_zero_mem_square_of_parameters d x.stalkHom.hom D
      (actualStalkDifferential_mul X d z x hx)
      (regularChartCenteredGerm X d z x hx)
      ((regularChartCenteredGerm_span X d z x hx).trans hker.symm)
      (regularChartCenteredGerm_differential X d z x hx) a (hker.symm ▸ ha) hzero
    simpa only [hker] using h
  · exact actualStalkDifferential_square_zero X d z x hx a

theorem actualMaximalCotangentDifferential_injective
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) :
    Function.Injective (actualConormalDifferential X d z x hx
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) le_rfl) := by
  let m := IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)
  let D := actualConormalDifferential X d z x hx m le_rfl
  intro a b hab
  obtain ⟨u, hu⟩ := m.toCotangent_surjective (a - b)
  have hd : actualStalkDifferential X d z x hx u.val = 0 := by
    change D (m.toCotangent u) = 0
    rw [hu, map_sub, hab, sub_self]
  have hs := (actualStalkDifferential_zero_iff_mem_square X d z x hx u.val u.property).mp hd
  have hz : m.toCotangent u = 0 := (Ideal.toCotangent_eq_zero m u).mpr hs
  rw [hu] at hz
  exact sub_eq_zero.mp hz

theorem complexPoint_stalkHom_surjective (X : Over (Spec (CommRingCat.of ℂ)))
    (x : ComplexPoint X) : Function.Surjective x.stalkHom.hom := by
  intro c
  refine ⟨X.left.presheaf.germ ⊤ x.underlying (show x.underlying ∈ (⊤ : X.left.Opens) from trivial)
    (a3b4a_gysin_sectionConst X.hom ⊤ c), ?_⟩
  rw [a3b4g_stalkHom_germ]
  exact a3b4a_gysin_evaluate_sectionConst X.hom ⊤ x trivial c

theorem actualMaximalCotangentFibreDifferential_injective
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source) :
    letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
    Function.Injective (actualConormalFibreDifferential X d z x hx
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) le_rfl) := by
  letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
  letI : IsScalarTower (X.left.presheaf.stalk x.underlying) ℂ ((Fin d → ℂ) →L[ℂ] ℂ) := {
    smul_assoc := by
      intro r c v
      change (x.stalkHom.hom r * c) • v = x.stalkHom.hom r • (c • v)
      exact mul_smul _ _ _ }
  exact liftBaseChange_injective_of_surjective
    (actualConormalDifferential X d z x hx
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) le_rfl)
    (complexPoint_stalkHom_surjective X x)
    (actualMaximalCotangentDifferential_injective X d z x hx)

#print axioms actualMaximalCotangentFibreDifferential_injective

#print axioms complexPoint_stalkHom_surjective

#print axioms actualMaximalCotangentDifferential_injective

#print axioms actualStalkDifferential_zero_iff_mem_square

end HodgeLean.Foundations.TubularEuler
