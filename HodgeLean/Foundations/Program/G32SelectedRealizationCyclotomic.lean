import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

noncomputable section
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_cyclotomic_action {m : ℕ} [NeZero m]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (hT : Polynomial.aeval T (Polynomial.cyclotomic m ℚ) = 0) :
    ∃ ρ : cyc_Field m →ₐ[ℚ] Module.End ℚ V,
      ρ (IsCyclotomicExtension.zeta m ℚ (cyc_Field m)) = T := by
  let hζ := IsCyclotomicExtension.zeta_spec m ℚ (cyc_Field m)
  let pb := hζ.powerBasis ℚ
  have hmin : minpoly ℚ pb.gen = Polynomial.cyclotomic m ℚ := by
    rw [IsPrimitiveRoot.powerBasis_gen]
    exact (Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)).symm
  have ht : Polynomial.aeval T (minpoly ℚ pb.gen) = 0 := by rw [hmin]; exact hT
  refine ⟨pb.lift T ht, ?_⟩
  simpa only [pb, IsPrimitiveRoot.powerBasis_gen] using pb.lift_gen T ht

theorem g32y_cyclotomic_coordinates {m : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (ρ : cyc_Field m →ₐ[ℚ] Module.End ℚ V) :
    ∃ h : ℕ, ∃ e : V ≃ₗ[ℚ] (Fin h → cyc_Field m),
      ∀ a, cyc_scalar e a = ρ a := by
  letI : Module (cyc_Field m) V := Module.compHom V ρ.toRingHom
  letI : IsScalarTower ℚ (cyc_Field m) V := ⟨fun q a v ↦ by
    change ρ (q • a) v = q • ρ a v
    rw [map_smul, LinearMap.smul_apply]⟩
  letI : Module.Finite (cyc_Field m) V :=
    Module.Finite.of_restrictScalars_finite ℚ (cyc_Field m) V
  let b := Module.finBasis (cyc_Field m) V
  let e : V ≃ₗ[ℚ] (Fin (Module.finrank (cyc_Field m) V) → cyc_Field m) := {
    b.equivFun.toAddEquiv with
    map_smul' := fun q v ↦ b.equivFun.toAddMonoidHom.toRatLinearMap.map_smul q v }
  refine ⟨Module.finrank (cyc_Field m) V, e, ?_⟩
  intro a
  ext v
  apply e.injective
  change b.equivFun (b.equivFun.symm (fun i ↦ a * b.equivFun v i)) = b.equivFun (a • v)
  rw [b.equivFun.apply_symm_apply, map_smul]
  rfl

theorem g32y_aeval_intertwine {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (f : U →ₗ[ℚ] V) (T : Module.End ℚ U) (S : Module.End ℚ V)
    (h : f ∘ₗ T = S ∘ₗ f) (p : Polynomial ℚ) :
    f ∘ₗ Polynomial.aeval T p = Polynomial.aeval S p ∘ₗ f := by
  have hn (n : ℕ) : f ∘ₗ (T ^ n) = (S ^ n) ∘ₗ f := by
    induction n with
    | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, h, ← LinearMap.comp_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, LinearMap.comp_smul, LinearMap.smul_comp, hn]

end HodgeLean.Foundations.Program
