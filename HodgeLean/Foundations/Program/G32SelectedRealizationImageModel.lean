import HodgeLean.Foundations.Program.G32SelectedRealizationImage

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_abelian_image (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (f : AbelianEnd X) (φ : b2_abelianLattice X →+ b2_abelianLattice X)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l = abelianPeriod X x (φ l))
    (N : ℕ) (hN : 0 < N) (hsq : ∀ l, φ (φ l) = N • φ l) :
    ∃ (P : Over (Spec ↧ℂ)) (_ : GrpObj P) (_ : IsCommMonObj P)
      (_ : IsIntegral P.left) (_ : Smooth P.hom) (_ : IsProjective P.hom),
    ∃ i : P ⟶ X, ∃ q : X ⟶ P,
    IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 P ^ N ∧
      LinearMap.range (homPullback q 1) = LinearMap.range (homPullback f.hom 1) := by
  classical
  let L := φ.range
  let : Module.Finite ℤ L := Module.Finite.of_surjective φ.rangeRestrict.toIntLinearMap
    φ.rangeRestrict_surjective
  let : Module.Free ℤ L := Module.Free.of_basis
    (Submodule.basisOfPid (abelianLatticeBasis X) φ.range.toIntSubmodule).2
  let F := b2_imageF (b2_abelianF X) φ
  have hφF := b2_abelianEnd_preserves X f φ hφ
  let hF := b2_image_isWeightOne (b2_abelianF X) (b2_abelianF_isWeightOne X) φ hφF
  let QI := b2_imageQ Q φ
  let hQI := b2_image_isRiemannForm (b2_abelianF X) Q hQ φ
  let P := b5_model L F hF QI
  let : GrpObj P := b5_groupObj L F hF QI hQI
  let : IsCommMonObj P := b5_commutative L F hF QI hQI
  let : IsIntegral P.left := b5_integral L F hF QI hQI
  let : Smooth P.hom := b5_smooth L F hF QI hQI
  let : IsProjective P.hom := b5_projective L F hF QI hQI
  let e : L ≃+ b2_abelianLattice P := b5_periodEquiv L F hF QI hQI
  have heF : F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF P :=
    b5_period_filtration L F hF QI hQI
  let iL : b2_abelianLattice P →+ b2_abelianLattice X :=
    φ.range.subtype.comp e.symm.toAddMonoidHom
  let pL : b2_abelianLattice X →+ b2_abelianLattice P :=
    e.toAddMonoidHom.comp φ.rangeRestrict
  have hiL : b2_abelianF P ≤ (b2_abelianF X).comap (b2_cplxMap iL) := by
    intro x hx
    rw [← heF] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hc : b2_cplxMap iL ∘ₗ b2_cplxMap e.toAddMonoidHom =
        b2_cplxMap φ.range.subtype := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul c l =>
        change c ⊗ₜ[ℤ] (e.symm (e l)).val = c ⊗ₜ[ℤ] l.val
        rw [e.symm_apply_apply]
      | add x y hx hy => simp only [map_add, LinearMap.comp_apply, hx, hy]
    change b2_cplxMap iL (b2_cplxMap e.toAddMonoidHom y) ∈ b2_abelianF X
    have hh := LinearMap.congr_fun hc y
    simp only [LinearMap.comp_apply] at hh
    rw [hh]
    exact hy
  have hpL : b2_abelianF X ≤ (b2_abelianF P).comap (b2_cplxMap pL) := by
    intro x hx
    have hy : b2_cplxMap φ.rangeRestrict x ∈ F := by
      change b2_cplxMap φ.range.subtype (b2_cplxMap φ.rangeRestrict x) ∈ b2_abelianF X
      rw [b2a_cplxMap_rangeRestrict]
      exact hφF hx
    have hc : b2_cplxMap pL = b2_cplxMap e.toAddMonoidHom ∘ₗ
        b2_cplxMap φ.rangeRestrict := by
      ext c l
      rfl
    change b2_cplxMap pL x ∈ b2_abelianF P
    rw [hc, LinearMap.comp_apply, ← heF]
    exact Submodule.mem_map_of_mem hy
  have hret : pL.comp iL = N • AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro l
    obtain ⟨r, rfl⟩ := e.surjective l
    change e (φ.rangeRestrict ((e.symm (e r)).val)) = N • e r
    rw [e.symm_apply_apply]
    calc
      e (φ.rangeRestrict r.val) = e (N • r) := by
        apply congrArg e
        apply Subtype.ext
        change φ r.val = N • r.val
        obtain ⟨x, hx⟩ := r.property
        rw [← hx, hsq]
      _ = N • e r := e.toAddMonoidHom.map_nsmul N r
  have hperiod : ∀ x l, abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x (iL (pL l)) := by
    intro x l
    have heq : iL (pL l) = φ l := by
      change (e.symm (e (φ.rangeRestrict l))).val = φ l
      rw [e.symm_apply_apply]
      rfl
    rw [heq]
    exact hφ x l
  obtain ⟨i, q, hi, hq, hr, hqi⟩ := g32y_lattice_retract X P f iL pL hiL hpL N hret hperiod
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    i, q, hi, hq, hr, ?_⟩
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : homPullback i 1 ∘ₗ homPullback q 1 = (N : ℚ) • LinearMap.id := by
    rw [← spec_homPullback_comp, hr, ← zpow_natCast, spec_homPullback_zpow,
      spec_homPullback_id]
    simp only [Int.cast_natCast]
  have hs : Function.Surjective (homPullback i 1) := by
    intro x
    refine ⟨(N : ℚ)⁻¹ • homPullback q 1 x, ?_⟩
    rw [map_smul, ← LinearMap.comp_apply, hc, LinearMap.smul_apply, LinearMap.id_apply,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [← hqi, spec_homPullback_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)]

end HodgeLean.Foundations.Program
