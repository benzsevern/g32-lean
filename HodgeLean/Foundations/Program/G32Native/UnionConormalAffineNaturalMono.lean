import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineScalarComparison
import HodgeLean.Foundations.Program.G32Native.UnionConormalFramedScalarMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalKernelScalar

/-! # Monicity of the natural affine conormal comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal HodgeLean.Foundations.Program

/-- The natural affine conormal arrow is monic when its kernel is an
intersection and the other kernel contains a nonzero scalar on the first component. -/
lemma unionConormal_affine_natural_mono
    (R A B C : CommRingCat.{0}) [IsDomain B]
    (p : R ⟶ A) (q : R ⟶ B) (r : R ⟶ C) (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R)))
    (hP : RingHom.ker p.hom = RingHom.ker q.hom ⊓ RingHom.ker r.hom)
    (a : RingHom.ker r.hom) (ha : q a.val ≠ 0) (n : ℕ)
    (eM : (Scheme.Modules.pullback (Spec.map k)).obj (s2c_conormal (Spec.map p)) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf) (Fin n) : (Spec B).Modules))
    (eN : s2c_conormal (Spec.map q) ≅
      (SheafOfModules.free (R := (Spec B).ringCatSheaf) (Fin n) : (Spec B).Modules)) :
    Mono (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R R))) (Spec.map k) h) := by
  letI : Algebra R B := q.hom.toAlgebra
  let P := RingHom.ker p.hom
  let I := RingHom.ker q.hom
  let J := RingHom.ker r.hom
  let E : (ModuleCat.extendScalars (algebraMap R R)).obj (ModuleCat.of R P) ⟶
      ModuleCat.of R I := ModuleCat.ofHom (unionKernelMap P I (hP.trans_le inf_le_left))
  let G : ModuleCat.of R I ⟶
      (ModuleCat.extendScalars (algebraMap R R)).obj (ModuleCat.of R P) :=
    ModuleCat.ofHom (unionKernelScalarLift P I J hP a)
  have hE (x : P) : (E.hom ((1 : R) ⊗ₜ[R] x)).val = algebraMap R R x.val := by
    change (1 : R) • x.val = x.val
    exact one_smul _ _
  exact unionConormal_affine_scalar_comparison_mono A B p q k h E hE
    ((ModuleCat.extendScalars q.hom).map G) (q a.val) ha
    (unionKernelMap_baseChange_scalarLift P I J hP a) n eM eN

#print axioms unionConormal_affine_natural_mono
end HodgeLean.Foundations.Program.G32Native
