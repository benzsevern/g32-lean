import HodgeLean.Foundations.Program.SchoenTowerJetDifferentials
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- A base element whose absolute differential generates the target differential module makes
the target algebra formally unramified over that base.
Source: Hartshorne, Algebraic Geometry, II.8, first exact sequence of differentials. -/
theorem s2t_formallyUnramified_of_differential_generator {K R A : Type*}
    [CommRing K] [CommRing R] [CommRing A] [Algebra K R] [Algebra R A]
    [Algebra K A] [IsScalarTower K R A] (t : R)
    (hspan : Submodule.span A {KaehlerDifferential.D K A (algebraMap R A t)} = ⊤) :
    Algebra.FormallyUnramified R A := by
  let L := KaehlerDifferential.map K R A A
  have hker : Submodule.span A {KaehlerDifferential.D K A (algebraMap R A t)} ≤
      LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ (rfl : _ = KaehlerDifferential.D K A (algebraMap R A t))
    change L (KaehlerDifferential.D K A (algebraMap R A t)) = 0
    dsimp only [L]
    rw [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
      Derivation.map_algebraMap]
  constructor
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective K R A x
  exact hker (hspan ▸ Submodule.mem_top)

/-- An unramified coordinate over a polynomial ring generates the absolute differentials.
Source: Hartshorne, Algebraic Geometry, II.8, first exact sequence of differentials. -/
theorem s2t_polynomial_coordinate_differential_spans {K A : Type*}
    [CommRing K] [CommRing A] [Algebra K A] [Algebra (Polynomial K) A]
    [IsScalarTower K (Polynomial K) A] [Algebra.FormallyUnramified (Polynomial K) A] :
    Submodule.span A {(KaehlerDifferential.D K A
      (algebraMap (Polynomial K) A Polynomial.X))} = ⊤ := by
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange K (Polynomial K) A) := by
    apply LinearMap.range_eq_top.mp
    rw [KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  apply top_unique
  intro x htop
  clear htop
  obtain ⟨y, rfl⟩ := hsurj x
  induction y with
  | tmul r s =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    apply Submodule.smul_mem _ r
    have hs : s = (KaehlerDifferential.polynomialEquiv K s) •
        KaehlerDifferential.D K (Polynomial K) Polynomial.X := by
      exact ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply s).symm
    rw [hs, map_smul, KaehlerDifferential.map_D]
    exact Submodule.smul_of_tower_mem _ _
      (Submodule.subset_span (Set.mem_singleton _))
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- The coordinate differential of a formally étale polynomial algebra is nonzero when the
algebra is nontrivial.
Source: Mathlib, `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`. -/
theorem s2t_polynomial_coordinate_differential_ne_zero {K A : Type*}
    [CommRing K] [CommRing A] [Nontrivial A] [Algebra K A] [Algebra (Polynomial K) A]
    [IsScalarTower K (Polynomial K) A] [Algebra.FormallyEtale (Polynomial K) A] :
    KaehlerDifferential.D K A (algebraMap (Polynomial K) A Polynomial.X) ≠ 0 := by
  intro hz
  have hh := congrArg (fun z => TensorProduct.rid (Polynomial K) A
    (TensorProduct.map (LinearMap.id : A →ₗ[Polynomial K] A)
      (KaehlerDifferential.polynomialEquiv K).toLinearMap
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Polynomial K) A).symm z))) hz
  simp only [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
    KaehlerDifferential.polynomialEquiv_D, Polynomial.derivative_X,
    TensorProduct.rid_tmul, one_smul, map_zero] at hh
  exact one_ne_zero hh

end HodgeLean.Foundations.Program
