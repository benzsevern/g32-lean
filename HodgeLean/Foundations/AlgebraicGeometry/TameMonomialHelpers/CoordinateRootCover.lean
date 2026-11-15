import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.FieldHelpers
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.RingTheory.RingHom.Etale

/-! # Universal coordinate-root covers of monomial charts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace AlgebraicGeometry.TameMonomialCover.Helpers

/-- The polynomial coordinate map for adjoining simultaneous parameter roots.
Source: Mathlib, MvPolynomial.expand and ULift.algEquiv. -/
def rootParameterMap (k : Type*) [CommRing k] (n m : ℕ) :
    MvPolynomial (Fin n) k →ₐ[k] ULift.{0} (MvPolynomial (Fin n) k) :=
  ULift.algEquiv.symm.toAlgHom.comp (MvPolynomial.expand m)

example (k : Type*) [CommRing k] (n m : ℕ) (i : Fin n) :
    rootParameterMap k n m (MvPolynomial.X i) =
      ULift.up ((MvPolynomial.X i : MvPolynomial (Fin n) k) ^ m) := by
  rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_X]
  rfl

/-- The simultaneous coordinate-root map is integral for every positive root degree.
Source: Mathlib, IsIntegral.of_pow and MvPolynomial.induction_on. -/
theorem rootParameterMap_integral
    (k : Type*) [CommRing k] (n m : ℕ) (hm : 0 < m) :
    (rootParameterMap k n m).toRingHom.IsIntegral := by
  let P := MvPolynomial (Fin n) k
  let B := ULift.{0} P
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  change (algebraMap P B).IsIntegral
  apply algebraMap_isIntegral_iff.mpr
  have hC (a : k) : algebraMap P B (MvPolynomial.C a) = ULift.up (MvPolynomial.C a) := by
    change rootParameterMap k n m (MvPolynomial.C a) = _
    rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_C]
    rfl
  have hX (i : Fin n) : IsIntegral P (ULift.up (MvPolynomial.X i) : B) := by
    apply IsIntegral.of_pow hm
    have H : (ULift.up (MvPolynomial.X i) : B) ^ m = algebraMap P B (MvPolynomial.X i) := by
      change _ = rootParameterMap k n m (MvPolynomial.X i)
      rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_X]
      rfl
    rw [H]
    exact isIntegral_algebraMap
  constructor
  intro b
  rcases b with ⟨b⟩
  induction b using MvPolynomial.induction_on with
  | C a => rw [← hC]; exact isIntegral_algebraMap
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (hX i)

/-- The actual coordinate-root tensor algebra is etale over the root polynomial ring and integral over the retained chart ring.
Source: Mathlib, Algebra.Etale.baseChange and Algebra.IsPushout.isIntegral. -/
theorem coordinate_root_tensor
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (n m : ℕ) (hm : 0 < m)
    (c : MvPolynomial (Fin n) k →ₐ[k] R) (hc : c.toRingHom.Etale) :
    let P := MvPolynomial (Fin n) k
    let B := ULift.{0} P
    letI := (rootParameterMap k n m).toRingHom.toAlgebra
    letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
    letI : Module P B := Algebra.toModule (R := P) (A := B)
    letI := c.toRingHom.toAlgebra
    let T := B ⊗[P] R
    ∃ w : Fin n → T,
      (∀ j, w j ^ m = algebraMap R T (c (MvPolynomial.X j))) ∧
      Algebra.Etale B T ∧ Algebra.IsIntegral R T ∧
      ∀ j, w j = algebraMap B T (ULift.up (MvPolynomial.X j)) := by
  let P := MvPolynomial (Fin n) k
  let B := ULift.{0} P
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  let T := B ⊗[P] R
  letI : Algebra.Etale P R := hc.toAlgebra
  letI : Algebra.IsIntegral P B :=
    algebraMap_isIntegral_iff.mp (rootParameterMap_integral k n m hm)
  let w (j : Fin n) : T := algebraMap B T (ULift.up (MvPolynomial.X j))
  refine ⟨w, ?_, inferInstance,
    Algebra.IsPushout.isIntegral (R := P) (S := B) (A := R) (SA := T), fun _ => rfl⟩
  intro j
  change (algebraMap B T (ULift.up (MvPolynomial.X j))) ^ m = _
  rw [← map_pow]
  have H : (ULift.up (MvPolynomial.X j) : B) ^ m = algebraMap P B (MvPolynomial.X j) := by
    change _ = rootParameterMap k n m (MvPolynomial.X j)
    rw [rootParameterMap, AlgHom.comp_apply, MvPolynomial.expand_X]
    rfl
  rw [H, ← IsScalarTower.algebraMap_apply P B T, IsScalarTower.algebraMap_apply P R T]
  rfl

/-- Compatible roots in an ambient algebra give a map from the actual coordinate-root tensor cover with the prescribed root values.
Source: Mathlib, Algebra.TensorProduct.lift and MvPolynomial.algHom_ext. -/
theorem coordinate_root_tensor_lift
    {k R L : Type*} [CommRing k] [CommRing R] [CommRing L] [Algebra k R] [Algebra k L]
    (n m : ℕ) (c : MvPolynomial (Fin n) k →ₐ[k] R) (f : R →ₐ[k] L)
    (w : Fin n → L) (hw : ∀ j, w j ^ m = f (c (MvPolynomial.X j))) :
    let P := MvPolynomial (Fin n) k
    let B := ULift.{0} P
    letI := (rootParameterMap k n m).toRingHom.toAlgebra
    letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
    letI : Module P B := Algebra.toModule (R := P) (A := B)
    letI := c.toRingHom.toAlgebra
    let T := B ⊗[P] R
    ∃ τ : T →+* L,
      (∀ r, τ (algebraMap R T r) = f r) ∧
      ∀ j, τ (algebraMap B T (ULift.up (MvPolynomial.X j))) = w j := by
  let P := MvPolynomial (Fin n) k
  let B := ULift.{0} P
  letI := (rootParameterMap k n m).toRingHom.toAlgebra
  letI : SMul P B := (rootParameterMap k n m).toRingHom.toAlgebra.toSMul
  letI : Module P B := Algebra.toModule (R := P) (A := B)
  letI := c.toRingHom.toAlgebra
  let T := B ⊗[P] R
  let s : B →ₐ[k] L := (MvPolynomial.aeval w).comp ULift.algEquiv.toAlgHom
  have H : s.comp (rootParameterMap k n m) = f.comp c := by
    apply MvPolynomial.algHom_ext
    intro j
    change (MvPolynomial.aeval w) (MvPolynomial.expand m (MvPolynomial.X j)) = f (c (MvPolynomial.X j))
    rw [MvPolynomial.expand_X, map_pow, MvPolynomial.aeval_X]
    exact hw j
  letI := (f.comp c).toRingHom.toAlgebra
  let sP : B →ₐ[P] L := { s.toRingHom with
    commutes' p := congrArg (fun h : P →ₐ[k] L => h p) H }
  let fP : R →ₐ[P] L := { f.toRingHom with commutes' _ := rfl }
  letI : IsScalarTower P P B := IsScalarTower.of_algebraMap_eq' (R := P) (S := P) (A := B) (by rw [Algebra.algebraMap_self, RingHom.comp_id])
  let τ : T →ₐ[P] L := Algebra.TensorProduct.lift sP fP (fun _ _ => Commute.all _ _)
  refine ⟨τ.toRingHom, ?_, ?_⟩
  · intro r
    change τ (1 ⊗ₜ[P] r) = f r
    dsimp only [τ]
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · intro j
    change τ ((ULift.up (MvPolynomial.X j)) ⊗ₜ[P] 1) = w j
    dsimp only [τ]
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    change (MvPolynomial.aeval w) (MvPolynomial.X j) = w j
    exact MvPolynomial.aeval_X _ _

end AlgebraicGeometry.TameMonomialCover.Helpers
