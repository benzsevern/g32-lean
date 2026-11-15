import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedMarkedIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineResidualRestriction

/-! # The marked ideal on the reciprocal supplied chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- On the chart with ratio u/v, the normalized marked equation is αs−1.
Only the value of α on the slice needs to be invertible. -/
theorem pairedC3_supplied_reciprocal_marked_ideal
    {Q X Y : Scheme} [IsIntegral Q] (i : Q ⟶ Y) [IsClosedImmersion i]
    (σ : X ⟶ Y) (D E : Y.IdealSheafData)
    (hproper : (E.comap i).support ≠ ⊤)
    (U : Y.affineOpens) [Nonempty (i ⁻¹ᵁ U.1)]
    (V : X.affineOpens) (hV : V.1 ≤ σ ⁻¹ᵁ U.1)
    (u v α : Γ(Y, U)) (s : Γ(X, V))
    (hu : D.ideal U = Ideal.span {u}) (hv : E.ideal U = Ideal.span {v})
    (hrel : (σ.appLE U.1 V.1 hV).hom u = s * (σ.appLE U.1 V.1 hV).hom v)
    (hs : Function.Surjective (eval₂RingHom (σ.appLE U.1 V.1 hV).hom s))
    (hk : RingHom.ker (eval₂RingHom (σ.appLE U.1 V.1 hV).hom s) =
      Ideal.span {C u - Polynomial.X * C v})
    (hα : (i.app U.1).hom (v - α * u) = 0)
    (hunit : IsUnit ((i.app U.1).hom α))
    (hbase : IsUnit (Ideal.Quotient.mk (((D ⊔ E) ⊔ i.ker).ideal U) α)) :
    let M₀ := (D ⊔ E) ⊔ i.ker
    let M := M₀.comap σ
    let q := Ideal.Quotient.mk (M.ideal V)
    let b := pairedC3AffineResidualCoefficient σ M₀ U V hV
    let β := Units.map b.toMonoidHom hbase.unit
    Ideal.map q ((s2c_strictTransform σ i.ker (D ⊔ E)).ideal V) =
      Ideal.span {(↑β : Γ(X, V) ⧸ M.ideal V) * q s - 1} := by
  let f := (i.app U.1).hom
  obtain ⟨γ, hγ⟩ := i.app_surjective U.1 U.2 (↑hunit.unit⁻¹)
  have hαf : f α = (hunit.unit : Γ(Q, i ⁻¹ᵁ U.1)) := hunit.unit_spec.symm
  have hγf : f γ = (↑hunit.unit⁻¹ : Γ(Q, i ⁻¹ᵁ U.1)) := hγ
  have hαrel : f v = f α * f u := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_mul] using hα
  have hγrel : f (u - γ * v) = 0 := by
    rw [map_sub, map_mul, hαrel, hαf, hγf, ← mul_assoc, Units.inv_mul, one_mul, sub_self]
  have hprod : α * γ - 1 ∈ i.ker.ideal U := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    change f (α * γ - 1) = 0
    rw [map_sub, map_mul, map_one, hαf, hγf, Units.mul_inv, sub_self]
  let M₀ := (D ⊔ E) ⊔ i.ker
  let M := M₀.comap σ
  let q := Ideal.Quotient.mk (M.ideal V)
  let b := pairedC3AffineResidualCoefficient σ M₀ U V hV
  let β := Units.map b.toMonoidHom hbase.unit
  have hprod' : Ideal.Quotient.mk (M₀.ideal U) α *
      Ideal.Quotient.mk (M₀.ideal U) γ = 1 := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (M₀.ideal U)), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show i.ker ≤ M₀ from le_sup_right) U hprod)
  have hγbase : Ideal.Quotient.mk (M₀.ideal U) γ =
      (↑hbase.unit⁻¹ : Γ(Y, U) ⧸ M₀.ideal U) := by
    rw [← hbase.unit_spec] at hprod'
    calc
      _ = (↑hbase.unit⁻¹ * ↑hbase.unit) * Ideal.Quotient.mk (M₀.ideal U) γ := by
        rw [Units.inv_mul, one_mul]
      _ = ↑hbase.unit⁻¹ := by rw [mul_assoc, hprod', mul_one]
  have hγchart : q ((σ.appLE U.1 V.1 hV).hom γ) = (↑β⁻¹ : Γ(X, V) ⧸ M.ideal V) := by
    change b (Ideal.Quotient.mk (M₀.ideal U) γ) = _
    rw [hγbase]
    rfl
  have hstrict := pairedC3_supplied_strict_marked_ideal i σ E D hproper U V hV
    v u γ s hv hu hrel hs hk hγrel
  dsimp only at hstrict
  rw [sup_comm E D] at hstrict
  change Ideal.map q _ = _
  rw [hstrict, hγchart]
  calc
    Ideal.span {q s - (↑β⁻¹ : Γ(X, V) ⧸ M.ideal V)} =
        Ideal.span {(↑β : Γ(X, V) ⧸ M.ideal V) * (q s - ↑β⁻¹)} :=
      (Ideal.span_singleton_mul_left_unit β.isUnit _).symm
    _ = _ := by rw [mul_sub, Units.mul_inv]

#print axioms pairedC3_supplied_reciprocal_marked_ideal
end HodgeLean.Foundations.Program.G32Native
