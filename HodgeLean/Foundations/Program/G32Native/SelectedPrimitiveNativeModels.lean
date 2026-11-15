import HodgeLean.Foundations.Program.G32Native.SelectedPrimitiveNativePrefix
import HodgeLean.Foundations.Program.SchoenSelectedGeometryQuotientFormRank
import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelHolomorphic
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierPrimitive
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartRetraction

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

theorem selectedPrimitiveNativeModels {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (S : g32p_Supplier)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    {A : g32t_Sixfold} (X : g32p_Cover A)
    (hJ : X.J = g32x_J D t) (hAut : HEq X.aut (fun a ↦ (f a).hom))
    (hGrp : HEq X.grp (inferInstance : GrpObj (g32x_J D t)))
    (hS : g32p_Admissible X.aut S)
    (hCurve :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ (C₀ Y₀ Z₀ : Over (Spec ↧ℂ)),
      ∃ (_ : IsIntegral C₀.left) (_ : Smooth C₀.hom) (_ : IsProjective C₀.hom),
      ∃ (_ : IsIntegral Y₀.left) (_ : Smooth Y₀.hom) (_ : IsProjective Y₀.hom),
      ∃ (_ : IsIntegral Z₀.left) (_ : Smooth Z₀.hom) (_ : IsProjective Z₀.hom),
      TopologicalSpace.dim C₀.left = 1 ∧ TopologicalSpace.dim Y₀.left = 1 ∧
      TopologicalSpace.dim Z₀.left = 1 ∧
      ∃ (q : C₀ ⟶ Y₀) (p : Y₀ ⟶ Z₀) (j : C₀ ⟶ g32x_J D t)
        (a : (S.H ⧸ S.χ.ker) → (Y₀ ⟶ Y₀))
        (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
        (eC : C ≃ₜ ComplexPoint C₀) (eY : Y ≃ₜ ComplexPoint Y₀)
        (eZ : Z ≃ₜ ComplexPoint Z₀),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      a 1 = 𝟙 Y₀ ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧
      Function.Injective a ∧ (∀ u, a u ≫ p = p) ∧
      (∀ x, Point.map q (eC x) = eY (rsq_proj S.χ.ker C x)) ∧
      (∀ y, Point.map p (eY y) = eZ (rsq_coarsen S.χ.ker y)) ∧
      (∀ u y, Point.map (a u) (eY y) = eY (u • y)) ∧
      Function.Bijective (homPullback j 1) ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        ∃ (_ : IsManifold 𝓘(ℂ, ℂ) ω Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Z),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) ω eC ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) ω eY ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eY.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) ω eZ ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm ∧
        (∃ (y : Fin (g32p_exponents S).length → Y)
          (r : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
          Function.Injective (fun i ↦ rsq_coarsen S.χ.ker (y i)) ∧
          (∀ i, b4_IsRotGen ℂ (y i) (r i) ∧
            e (r i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
          (∀ z : Y, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
            ∃ i, rsq_coarsen S.χ.ker z = rsq_coarsen S.χ.ker (y i))) ∧
        (let V := LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))
        ∀ P : g32p_Part (g32x_J D t) (fun h ↦ (f h).hom) S,
          ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
            (∀ v, homPullback q 1 (E v) = homPullback j 1 (homPullback P.proj 1 v)) ∧
            (∀ (h : S.H) v,
              homPullback (a ((QuotientGroup.mk h)⁻¹)) 1 (E v) =
                (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : HQ Y₀ 1)) ∧
            Module.finrank ℚ V = 2 * P.k * Nat.totient S.m ∧
            2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ Z) +
              (g32p_exponents S).length)) :
    let C := b65z_fibre c D.C t
    let Y := rsq_Quot S.χ.ker C
    let Z := rsq_Quot S.H C
    ∃ (C₀ Y₀ Z₀ : Over (Spec ↧ℂ)),
      ∃ (_ : IsIntegral C₀.left) (_ : Smooth C₀.hom) (_ : IsProjective C₀.hom),
      ∃ (_ : IsIntegral Y₀.left) (_ : Smooth Y₀.hom) (_ : IsProjective Y₀.hom),
      ∃ (_ : IsIntegral Z₀.left) (_ : Smooth Z₀.hom) (_ : IsProjective Z₀.hom),
      TopologicalSpace.dim C₀.left = 1 ∧ TopologicalSpace.dim Y₀.left = 1 ∧
      TopologicalSpace.dim Z₀.left = 1 ∧
      ∃ (q : C₀ ⟶ Y₀) (p : Y₀ ⟶ Z₀) (j : C₀ ⟶ g32x_J D t)
        (a : (S.H ⧸ S.χ.ker) → (Y₀ ⟶ Y₀))
        (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
        (eC : C ≃ₜ ComplexPoint C₀) (eY : Y ≃ₜ ComplexPoint Y₀)
        (eZ : Z ≃ₜ ComplexPoint Z₀),
      (∀ h : S.H, e (QuotientGroup.mk h) = S.χ h) ∧
      a 1 = 𝟙 Y₀ ∧ (∀ u v, a (u * v) = a v ≫ a u) ∧
      Function.Injective a ∧ (∀ u, a u ≫ p = p) ∧
      (∀ x, Point.map q (eC x) = eY (rsq_proj S.χ.ker C x)) ∧
      (∀ y, Point.map p (eY y) = eZ (rsq_coarsen S.χ.ker y)) ∧
      (∀ u y, Point.map (a u) (eY y) = eY (u • y)) ∧
      Function.Bijective (homPullback j 1) ∧
      ∃ cy : ChartedSpace ℂ Y, ∃ cz : ChartedSpace ℂ Z,
        letI := cy
        letI := cz
        ∃ (_ : IsManifold 𝓘(ℂ, ℂ) ω Y) (_ : IsManifold 𝓘(ℂ, ℂ) ω Z),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) ω eC ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim C₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eC.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) ω eY ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Y₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eY.symm ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) ω eZ ∧
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm ∧
        (∃ (y : Fin (g32p_exponents S).length → Y)
          (r : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker),
          Function.Injective (fun i ↦ rsq_coarsen S.χ.ker (y i)) ∧
          (∀ i, b4_IsRotGen ℂ (y i) (r i) ∧
            e (r i) = Multiplicative.ofAdd ((g32p_exponents S)[i] : ZMod S.m)) ∧
          (∀ z : Y, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
            ∃ i, rsq_coarsen S.χ.ker z = rsq_coarsen S.χ.ker (y i))) ∧
    let P := X.part S hS
    ∃ (jC : C₀ ⟶ X.J), HEq jC j ∧
      (∀ x, Point.map q (eC x) = eY (rsq_proj S.χ.ker (b65z_fibre c D.C t) x)) ∧
      (∀ z, Point.map p (eY z) = eZ (rsq_coarsen S.χ.ker z)) ∧
      (∀ u : S.H, e (QuotientGroup.mk u) = S.χ u) ∧
      Function.Bijective (homPullback jC 1) ∧
      ∃ primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
        (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
          (Polynomial.cyclotomic S.m ℚ)),
        (∀ v, homPullback q 1 (primitive v) =
          homPullback jC 1 (homPullback P.proj 1 v)) ∧
        (∀ (u : S.H) v,
          homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
            (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y₀ 1)) ∧
        Module.finrank ℚ (LinearMap.ker
          (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
            (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m ∧
        2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (Z)) +
          (g32p_exponents S).length := by
  classical
  obtain ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq, hp, ha, hj, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi', hbranch, hprimitive⟩ := hCurve
  letI := cy
  letI := cz
  letI := hy
  letI := hz
  refine ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq, hp, ha, hj, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi', hbranch, ?_⟩
  exact selectedPrimitiveNativePrefix X (g32x_J D t) (fun a ↦ (f a).hom)
    hJ hAut hGrp S hS (b65z_fibre c D.C t) C₀ Y₀ Z₀ q p j a e eC eY eZ
    hq hp he hj hprimitive

#print axioms selectedPrimitiveNativeModels
end HodgeLean.Foundations.Program
