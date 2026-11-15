import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierModels
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartPrimitive
import HodgeLean.Foundations.Program.SchoenSelectedGeometryResidualPullback
import HodgeLean.Foundations.Program.SchoenSelectedGeometryActionInverse

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

open AlgebraicTopology.Singular

/-- The chosen supplier models yield the exact primitive square and residual scalar action. -/
theorem s0_supplier_primitive_comparison
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (S : g32p_Supplier)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ h, homPullback (f h).hom 1 = g32x_deck D t h)
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (q : X ⟶ Y) (j : X ⟶ g32x_J D t)
    (a : S.H ⧸ S.χ.ker → (Y ⟶ Y))
    (e : S.H ⧸ S.χ.ker ≃* Multiplicative (ZMod S.m))
    (he : ∀ h : S.H, e (QuotientGroup.mk h) = S.χ h)
    (ha1 : a 1 = 𝟙 Y) (ham : ∀ u v, a (u * v) = a v ≫ a u)
    (eC : b65z_fibre c D.C t ≃ₜ ComplexPoint X)
    (eY : rsq_Quot S.χ.ker (b65z_fibre c D.C t) ≃ₜ ComplexPoint Y)
    (hqpoint : ∀ z, Point.map q (eC z) = eY (rsq_proj S.χ.ker _ z))
    (hapoint : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (β : HQ X 1 ≃ₗ[ℚ] Cohomology ℚ (TopCat.of (b65z_fibre c D.C t)) 1)
    (hβ : ∀ x, β x = cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩) (cupComparison X 1 x))
    (hjb : Function.Bijective (homPullback j 1)) (hqi : Function.Injective (homPullback q 1))
    (hqr : ∀ x : HQ X 1, x ∈ LinearMap.range (homPullback q 1) ↔
      ∀ h : S.χ.ker, cohomologyMap ℚ 1
        (TopCat.ofHom ⟨fun z : b65z_fibre c D.C t ↦ h • z, (D.hG t h).continuous⟩) (β x) = β x)
    (hjd : ∀ h : g32p_G, ∀ x : HQ (g32x_J D t) 1,
      β (homPullback j 1 (g32x_deck D t h x)) =
        cohomologyMap ℚ 1 (TopCat.ofHom
          ⟨fun z : b65z_fibre c D.C t ↦ h⁻¹ • z, (D.hG t h⁻¹).continuous⟩)
          (β (homPullback j 1 x)))
    (P : g32p_Part (g32x_J D t) (fun h ↦ (f h).hom) S)
    (hP : Function.Injective (homPullback P.proj 1)) :
    let V := LinearMap.ker (Polynomial.aeval
      (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1) (Polynomial.cyclotomic S.m ℚ))
    ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
      (∀ v, homPullback q 1 (E v) = homPullback j 1 (homPullback P.proj 1 v)) ∧
      (∀ (h : S.H) v, homPullback (a ((QuotientGroup.mk h)⁻¹)) 1 (E v) =
        (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : HQ Y 1)) ∧
      Module.finrank ℚ V = 2 * P.k * Nat.totient S.m := by
  let C := b65z_fibre c D.C t
  let jB := (LinearEquiv.ofBijective (homPullback j 1) hjb).trans β
  let qB := β.toLinearMap ∘ₗ homPullback q 1
  let A := fun h : S.H ↦ cohomologyMap ℚ 1 (TopCat.ofHom
    ⟨fun z : C ↦ h⁻¹ • z, (D.hG t h⁻¹).continuous⟩)
  let T := fun h : S.H ↦ homPullback (a ((QuotientGroup.mk h)⁻¹)) 1
  let u := e.symm (Multiplicative.ofAdd 1)
  let B := homPullback (a u) 1
  let U := homPullback (a u⁻¹) 1
  have hqB : Function.Injective qB := β.injective.comp hqi
  have hjB : ∀ h : S.H, jB.toLinearMap ∘ₗ homPullback (f h).hom 1 = A h ∘ₗ jB.toLinearMap := by
    intro h
    ext x
    change β (homPullback j 1 (homPullback (f h).hom 1 x)) = A h (β (homPullback j 1 x))
    rw [hf]
    exact hjd h x
  have hT : ∀ h, qB ∘ₗ T h = A h ∘ₗ qB := by
    intro h
    ext x
    change β (homPullback q 1 (T h x)) = A h (β (homPullback q 1 x))
    rw [hβ, hβ]
    exact s0_residual_deck_pullback S.χ.ker (fun h : S.H ↦ (D.hG t h).continuous)
      X Y eC eY q a hqpoint hapoint h 1 x
  have hi : ∀ z, z ∈ LinearMap.range qB ↔ ∀ h : S.H, S.χ h = 1 → A h z = z := by
    intro z
    have hz : z ∈ LinearMap.range qB ↔ β.symm z ∈ LinearMap.range (homPullback q 1) := by
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, (β.symm_apply_apply _).symm⟩
      · rintro ⟨y, hy⟩
        exact ⟨y, (congrArg β hy).trans (β.apply_symm_apply z)⟩
    rw [hz, hqr, β.apply_symm_apply]
    constructor
    · intro hz h hh
      let k : S.χ.ker := ⟨h⁻¹, by simp [hh]⟩
      exact hz k
    · intro hz k
      have hh := hz ((k : S.H)⁻¹) (by rw [map_inv, show S.χ (k : S.H) = 1 from k.property, inv_one])
      simpa only [A, inv_inv, Subgroup.smul_def] using hh
  have heU : ∀ h : S.H, S.χ h = Multiplicative.ofAdd 1 → qB ∘ₗ U = A h ∘ₗ qB := by
    intro h hh
    have hu : (QuotientGroup.mk h : S.H ⧸ S.χ.ker) = u := by
      apply e.injective
      rw [he]
      exact hh.trans (e.apply_symm_apply _).symm
    simpa only [T, hu] using hT h
  obtain ⟨hBU, hUB⟩ := s0_algebraic_action_inverse Y a ha1 ham u 1
  obtain ⟨E, hE, hAct, hRank⟩ := s0_part_primitive_comparison (g32x_J D t)
    (fun h ↦ (f h).hom) S P hP jB qB hqB A T B U hBU hUB hjB hi heU hT
  refine ⟨E, ?_, hAct, hRank⟩
  intro v
  exact β.injective (hE v)

#print axioms s0_supplier_primitive_comparison
end HodgeLean.Foundations.Program
