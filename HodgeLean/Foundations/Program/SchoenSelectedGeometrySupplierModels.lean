import HodgeLean.Foundations.Program.SchoenSelectedGeometryDeckAlgebraic
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicInjection
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicGalois
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySupplierCurve
import HodgeLean.Foundations.Program.SchoenSelectedGeometryModelTower
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiComparison
import HodgeLean.Foundations.Program.G32SelectedRealizationSecond
import HodgeLean.Foundations.Program.G32SelectedProp46
import HodgeLean.Foundations.Program.RiemannSurfaceQuotient
import HodgeLean.Adapters.CycleClassPullbackDefs
import HodgeLean.Foundations.Program.UniversalFamilyB60cIsogeny
import HodgeLean.Foundations.Program.CycleFoundationsPullback

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

theorem s0_supplier_model_maps {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (S : g32p_Supplier) :
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
        ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim Z₀.left) → ℂ) 𝓘(ℂ, ℂ) ω eZ.symm := by
  classical
  let C := b65z_fibre c D.C t
  let Y := rsq_Quot S.χ.ker C
  let Z := rsq_Quot S.H C
  have hH : ∀ h : S.H, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ h • x) :=
    fun h ↦ D.hG t h
  have hK : ∀ h : S.χ.ker, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ h • x) :=
    fun h ↦ hH h
  letI := rsq_t2Space (Module.finrank_self ℂ) (fun h ↦ (hH h).continuous)
  letI := rsq_t2Space (Module.finrank_self ℂ) (fun h ↦ (hK h).continuous)
  obtain ⟨e, he, hfaith, cy, cz, hy, hz, hq, _, hp, hact, _⟩ :=
    s0_supplier_curve_aux D t S
  letI := hfaith
  letI := cy
  letI := cz
  letI := hy
  letI := hz
  have hinv : ∀ (u : S.H ⧸ S.χ.ker) (y : Y),
      rsq_coarsen S.χ.ker (u • y) = rsq_coarsen S.χ.ker y := by
    intro u y
    induction u using QuotientGroup.induction_on with
    | H h =>
      induction y using Quotient.inductionOn' with
      | h x => exact MulAction.orbitRel.Quotient.quotient_smul_eq
  obtain ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
      hCd, hYd, hZd, eC, eY, eZ, hC, hCi', hY, hYi', hZ, hZi',
      q, p, a, hq', hp', ha, ha1, ham, hai, hap⟩ :=
    s0_curve_model_tower C Y Z (S.H ⧸ S.χ.ker)
      (rsq_proj S.χ.ker C) (rsq_coarsen S.χ.ker) hq hp hact hinv
  obtain ⟨aj, haj, j, hj, hjpoint⟩ := s0_selected_abelJacobi_comparison D t C₀ eC hCi'
    (Classical.choice (inferInstance : Nonempty C))
  have hqi := s0_algebraic_curve_pullback_injective (rsq_proj S.χ.ker C) hq
    (rsq_proj_nonconstant (H := S.χ.ker) (X := C) (Module.finrank_self ℂ))
    C₀ Y₀ eC eY q hq'
  have hqr := s0_algebraic_galois_range hK (rsq_proj S.χ.ker C) hq
    (rsq_proj_isGaloisCover S.χ.ker C) C₀ Y₀ eC eY q hq'
  letI := b2_latticeMap_discrete (b3_periodF ℂ C) (b3_isWeightOne (Module.finrank_self ℂ))
  have hajc := (b3_abelJacobi_holomorphic (E := ℂ) (Module.finrank_self ℂ)
    (Classical.choice (inferInstance : Nonempty C)) aj haj).continuous
  have hjdeck := s0_selected_algebraic_deck_betti D t C₀ eC
    (Classical.choice (inferInstance : Nonempty C)) aj haj hajc j hjpoint
  exact ⟨C₀, Y₀, Z₀, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, q, p, j, a, e, eC, eY, eZ, he, ha1, ham, hai,
    hap, hq', hp', ha, hj, hqi, hqr, hjdeck, cy, cz, hy, hz, hC, hCi', hY, hYi', hZ, hZi'⟩

#print axioms s0_supplier_model_maps
end HodgeLean.Foundations.Program
