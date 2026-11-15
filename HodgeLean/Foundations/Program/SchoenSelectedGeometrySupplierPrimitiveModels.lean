import HodgeLean.Foundations.Program.SchoenSelectedGeometryPartInvariantRank
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

theorem s0_supplier_models_with_primitive {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (S : g32p_Supplier)
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ h, homPullback (f h).hom 1 = g32x_deck D t h) :
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
      Function.Injective (homPullback q 1) ∧
      (∀ x : HQ C₀ 1, x ∈ LinearMap.range (homPullback q 1) ↔
        ∀ h : S.χ.ker,
          AlgebraicTopology.Singular.cohomologyMap ℚ 1
            (TopCat.ofHom ⟨fun y : C ↦ h • y, (D.hG t h).continuous⟩)
            (AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)
              (cupComparison C₀ 1 x)) =
          AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)
            (cupComparison C₀ 1 x)) ∧
      (∀ h : g32p_G, ∀ x : HQ (g32x_J D t) 1,
        AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)
          (cupComparison C₀ 1 (homPullback j 1 (g32x_deck D t h x))) =
        AlgebraicTopology.Singular.cohomologyMap ℚ 1
          (TopCat.ofHom ⟨fun y : C ↦ h⁻¹ • y, (D.hG t h⁻¹).continuous⟩)
          (AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨eC, eC.continuous⟩)
            (cupComparison C₀ 1 (homPullback j 1 x)))) ∧
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
        (let V := LinearMap.ker (Polynomial.aeval
          (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1) (Polynomial.cyclotomic S.m ℚ))
        ∀ P : g32p_Part (g32x_J D t) (fun h ↦ (f h).hom) S,
          ∃ E : HQ P.P 1 ≃ₗ[ℚ] V,
            (∀ v, homPullback q 1 (E v) = homPullback j 1 (homPullback P.proj 1 v)) ∧
            (∀ (h : S.H) v, homPullback (a ((QuotientGroup.mk h)⁻¹)) 1 (E v) =
              (E (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S h) v) : HQ Y₀ 1)) ∧
            Module.finrank ℚ V = 2 * P.k * Nat.totient S.m ∧
            2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ Z) +
              (g32p_exponents S).length) := by
  classical
  obtain ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq', hp', ha, hj, hqi, hqr, hjdeck, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi'⟩ := s0_supplier_model_maps D t S
  letI := cy
  letI := cz
  letI := hy
  letI := hz
  have hH : ∀ h : S.H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun z : b65z_fibre c D.C t ↦ h • z) := fun h ↦ D.hG t h
  letI := rsq_t2Space (Module.finrank_self ℂ) (fun h ↦ (hH h).continuous)
  have hproj := s0_model_square_holomorphic C₀ Z₀ eC eZ hC hZi' (q ≫ p)
    (rsq_proj S.H (b65z_fibre c D.C t)) (by
      intro x
      rw [Point.map_comp_apply, hq', hp']
      rfl)
  have hGenus := s0_quotient_form_rank hH
    (rsq_proj S.H (b65z_fibre c D.C t)) hproj
    (rsq_proj_isGaloisCover S.H (b65z_fibre c D.C t))
  refine ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq', hp', ha, hj, hqi, hqr, hjdeck, cy, cz, hy, hz,
    hC, hCi', hY, hYi', hZ, hZi', ?_⟩
  let β := (cupComparison C₀ 1).trans
    (HodgeLean.Foundations.Singular.cohomologyHomeomorphEquiv eC 1).symm
  have hβ (x : HQ C₀ 1) : β x = AlgebraicTopology.Singular.cohomologyMap ℚ 1
      (TopCat.ofHom ⟨eC, eC.continuous⟩) (cupComparison C₀ 1 x) := rfl
  intro V P
  obtain ⟨E, hE, hAct, hRank⟩ := s0_supplier_primitive_comparison D t S f hf C₀ Y₀ q j a e he ha1 ham eC eY
    hq' ha β hβ hj hqi (by simpa only [hβ] using hqr)
    (by simpa only [hβ] using hjdeck) P
    (s0_part_proj_injective (g32x_J D t) (fun h ↦ (f h).hom) S P)
  refine ⟨E, hE, hAct, hRank, ?_⟩
  have hk := s0_part_invariant_rank D t hg f hf S P
  rw [hGenus] at hk
  exact hk

#print axioms s0_supplier_models_with_primitive
end HodgeLean.Foundations.Program
