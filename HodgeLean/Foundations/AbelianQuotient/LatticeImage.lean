import HodgeLean.Foundations.AbelianQuotient.RiemannForm
import HodgeLean.Foundations.AbelianQuotient.H1Helpers
import HodgeLean.Foundations.Program.G32SelectedRealizationImage

noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The integral lattice image supplies an algebraic factorization with a surjective period map. -/
theorem lattice_image_factorization (A : Variety)
    (Q : LinearMap.BilinForm ℤ (b2_abelianLattice A.X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice A.X) (b2_abelianF A.X) Q)
    (f : AbelianEnd A.X) (φ : b2_abelianLattice A.X →+ b2_abelianLattice A.X)
    (hφ : ∀ x l, abelianPeriod A.X (abelianEndAction A.X f x) l =
      abelianPeriod A.X x (φ l))
    (N : ℕ) (hsq : ∀ l, φ (φ l) = N • φ l) :
    ∃ (B : Variety) (i : Hom B A) (q : Hom A B),
      q.hom ≫ i.hom = f.hom ∧ i.hom ≫ q.hom = (multiplication B N).hom ∧
      ∃ ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice B.X,
        Function.Surjective ψ ∧ ∀ x l,
          abelianPeriod A.X (homPullback q.hom 1 x) l = abelianPeriod B.X x (ψ l) := by
  classical
  let L := φ.range
  let : Module.Finite ℤ L := Module.Finite.of_surjective φ.rangeRestrict.toIntLinearMap
    φ.rangeRestrict_surjective
  let : Module.Free ℤ L := Module.Free.of_basis
    (Submodule.basisOfPid (abelianLatticeBasis A.X) φ.range.toIntSubmodule).2
  let F := b2_imageF (b2_abelianF A.X) φ
  have hφF := b2_abelianEnd_preserves A.X f φ hφ
  let hF := b2_image_isWeightOne (b2_abelianF A.X) (b2_abelianF_isWeightOne A.X) φ hφF
  let QI := b2_imageQ Q φ
  let hQI := b2_image_isRiemannForm (b2_abelianF A.X) Q hQ φ
  let P := b5_model L F hF QI
  let : GrpObj P := b5_groupObj L F hF QI hQI
  let : IsCommMonObj P := b5_commutative L F hF QI hQI
  let : IsIntegral P.left := b5_integral L F hF QI hQI
  let : Smooth P.hom := b5_smooth L F hF QI hQI
  let : IsProjective P.hom := b5_projective L F hF QI hQI
  let e : L ≃+ b2_abelianLattice P := b5_periodEquiv L F hF QI hQI
  have heF : F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF P :=
    b5_period_filtration L F hF QI hQI
  let iL : b2_abelianLattice P →+ b2_abelianLattice A.X :=
    φ.range.subtype.comp e.symm.toAddMonoidHom
  let pL : b2_abelianLattice A.X →+ b2_abelianLattice P :=
    e.toAddMonoidHom.comp φ.rangeRestrict
  have hiL : b2_abelianF P ≤ (b2_abelianF A.X).comap (b2_cplxMap iL) := by
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
    change b2_cplxMap iL (b2_cplxMap e.toAddMonoidHom y) ∈ b2_abelianF A.X
    have hh := LinearMap.congr_fun hc y
    simp only [LinearMap.comp_apply] at hh
    rw [hh]
    exact hy
  have hpL : b2_abelianF A.X ≤ (b2_abelianF P).comap (b2_cplxMap pL) := by
    intro x hx
    have hy : b2_cplxMap φ.rangeRestrict x ∈ F := by
      change b2_cplxMap φ.range.subtype (b2_cplxMap φ.rangeRestrict x) ∈ b2_abelianF A.X
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
  have hperiod : ∀ x l, abelianPeriod A.X (abelianEndAction A.X f x) l =
      abelianPeriod A.X x (iL (pL l)) := by
    intro x l
    have heq : iL (pL l) = φ l := by
      change (e.symm (e (φ.rangeRestrict l))).val = φ l
      rw [e.symm_apply_apply]
      rfl
    rw [heq]
    exact hφ x l
  obtain ⟨i, him, hi⟩ := g32x_exists_hom_of_filtration A.X P iL hiL
  obtain ⟨q, hqm, hq⟩ := g32x_exists_hom_of_filtration P A.X pL hpL
  let B : Variety := ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hqi : q ≫ i = f.hom := by
    let qi : AbelianEnd A.X := ⟨q ≫ i, inferInstance⟩
    have hEq : qi = f := by
      apply spec_abelianEndAction_injective A.X
      change homPullback (q ≫ i) 1 = homPullback f.hom 1
      apply LinearMap.ext
      intro x
      apply abelianPeriod_injective A.X
      funext l
      rw [spec_homPullback_comp, LinearMap.comp_apply, hq, hi]
      exact (hperiod x l).symm
    exact congrArg AbelianEnd.hom hEq
  have hiq : i ≫ q = (multiplication B N).hom := by
    let iq : AbelianEnd P := ⟨i ≫ q, inferInstance⟩
    let mulN : AbelianEnd P := ⟨(multiplication B N).hom, inferInstance⟩
    have hEq : iq = mulN := by
      apply spec_abelianEndAction_injective P
      change homPullback (i ≫ q) 1 = homPullback (multiplication B N).hom 1
      rw [multiplication_nat_hom, spec_homPullback_zpow, spec_homPullback_id, Int.cast_natCast]
      apply LinearMap.ext
      intro x
      apply abelianPeriod_injective P
      funext l
      rw [spec_homPullback_comp, LinearMap.comp_apply, hi, hq]
      have hl := DFunLike.congr_fun hret l
      change pL (iL l) = N • l at hl
      rw [hl, LinearMap.smul_apply, LinearMap.id_apply, map_smul, Pi.smul_apply]
      obtain ⟨eP, heP⟩ := spec_abelianPeriod_equiv P
      simp only [← heP, map_nsmul, nsmul_eq_mul, smul_eq_mul]
    exact congrArg AbelianEnd.hom hEq
  refine ⟨B, ⟨i, him⟩, ⟨q, hqm⟩, hqi, hiq, pL, ?_, hq⟩
  exact e.surjective.comp φ.rangeRestrict_surjective

end HodgeLean.Foundations.AbelianQuotient
