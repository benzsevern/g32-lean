import HodgeLean.Foundations.Program.PrymFamilyB4Defs
import HodgeLean.Foundations.Program.PrymFamilyB4Action
import HodgeLean.Foundations.Program.HurwitzPrym
import HodgeLean.Foundations.Program.TorusAlgebraization

/-! # B4b: lattice transport proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem b4b_action_sq_aux (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X) (J : Λ →+ Λ)
    (hJ : ∀ x, J (J x) = (-3 : ℤ) • x) :
    (b4b_cohomologyAction Λ X e J).comp (b4b_cohomologyAction Λ X e J) =
      (-3 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply (abelianPeriodEquiv X).injective
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp [b4b_cohomologyAction, b4b_periodPrecomp, hJ]

theorem b4b_action_preserves_aux (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (he : F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF X)
    (J : Λ →+ Λ) (hJ : F ≤ F.comap (b2_cplxMap J)) :
    letI := (torusCohomology_cupProductOf X).finite
    ∀ pq : ℤ × ℤ, ((abelianVarietyCohomologyOf (finiteBetti_abelian X)
        (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
        (torusCohomology_cupProductOf X)).weight1.H pq).map ((b4b_cohomologyAction Λ X e J).baseChange ℂ) ≤
      (abelianVarietyCohomologyOf (finiteBetti_abelian X)
        (spec_bettiDeRhamIso_abelian X) (hodgeDecomposition_of_abelian X)
        (torusCohomology_cupProductOf X)).weight1.H pq := by
  letI := (torusCohomology_cupProductOf X).finite
  let T := b4b_cohomologyAction Λ X e J
  let ep := LinearEquiv.baseChange ℚ ℂ _ _ (b4b_periodLinearEquiv X)
  let φ : b2_abelianLattice X →+ b2_abelianLattice X :=
    e.toAddMonoidHom.comp (J.comp e.symm.toAddMonoidHom)
  have hcomm (x : ℂ ⊗[ℤ] Λ) : b2_cplxMap e.toAddMonoidHom (b2_cplxMap J x) =
      b2_cplxMap φ (b2_cplxMap e.toAddMonoidHom x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c x =>
      change c ⊗ₜ[ℤ] e (J x) = c ⊗ₜ[ℤ] e (J (e.symm (e x)))
      rw [e.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hφ : b2_abelianF X ≤ (b2_abelianF X).comap (b2_cplxMap φ) := by
    rw [← he]
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_comap]
    exact ⟨b2_cplxMap J x, hJ hx, hcomm x⟩
  have hnat (w : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℤ] b2_abelianLattice X) :
      b2b_pairing _ (ep (T.baseChange ℂ w)) y =
        b2b_pairing _ (ep w) (b2_cplxMap φ y) := by
    induction w using TensorProduct.inductionOn with
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      rw [ha, hb]
    | tmul c v =>
      induction y using TensorProduct.inductionOn with
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
      | tmul d x =>
        change c * (d * (((abelianPeriodEquiv X) (T v) x : ℚ) : ℂ)) =
          c * (d * (((abelianPeriodEquiv X) v (φ x) : ℚ) : ℂ))
        congr 2
        norm_cast
        simp [T, b4b_cohomologyAction, b4b_periodPrecomp, φ]
  have hhol : (cohomologyHodgePiece X 1 (1, 0)).map (T.baseChange ℂ) ≤
      cohomologyHodgePiece X 1 (1, 0) := by
    intro z hz
    rw [Submodule.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hu : ep w ∈ b2b_hodgeOne (b2_abelianLattice X) (b2_abelianF X) := by
      rw [← b4b_h10_period X]
      exact Submodule.mem_map_of_mem hw
    rw [b2b_hodgeOne, Submodule.mem_comap, Submodule.mem_dualAnnihilator] at hu
    have hout : ep (T.baseChange ℂ w) ∈
        b2b_hodgeOne (b2_abelianLattice X) (b2_abelianF X) := by
      rw [b2b_hodgeOne, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
      intro y hy
      rw [hnat]
      exact hu (b2_cplxMap φ y) (hφ hy)
    rw [← b4b_h10_period X] at hout
    obtain ⟨u, hu, heu⟩ := hout
    have huv : u = T.baseChange ℂ w := ep.injective heu
    rw [← huv]
    exact hu
  have hholC : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X := by
    simpa [spec_g4_cohomologyHodgePiece_one_eq X, latticeHodgePieces] using hhol
  have hanti := spec_map_antiholomorphic_le_of_holomorphic X T hholC
  intro pq
  by_cases h10 : pq = (1, 0)
  · subst pq
    exact hhol
  by_cases h01 : pq = (0, 1)
  · subst pq
    change (cohomologyHodgePiece X 1 (0, 1)).map (T.baseChange ℂ) ≤
      cohomologyHodgePiece X 1 (0, 1)
    simpa [spec_g4_cohomologyHodgePiece_one_eq X, latticeHodgePieces] using hanti
  · change (cohomologyHodgePiece X 1 pq).map (T.baseChange ℂ) ≤ _
    rw [cohomologyHodgePiece_one_eq_bot X pq h10 h01, Submodule.map_bot]
    exact bot_le

theorem b4b_transportForm_riemann_aux (Λ : Type) [AddCommGroup Λ]
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (e : Λ ≃+ b2_abelianLattice X) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (he : F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF X)
    (Q : LinearMap.BilinForm ℤ Λ) (hQ : b2_IsRiemannForm Λ F Q) :
    b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X)
      (b4b_transportForm Λ X e Q) := by
  have hs (z : ℂ ⊗[ℤ] Λ) :
      b2_cplxMap e.symm.toAddMonoidHom (b2_cplxMap e.toAddMonoidHom z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul c x => simp [b2_cplxMap]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change Q (e.symm x) (e.symm x) = 0
    exact hQ.alt _
  · intro x hx y hy
    rw [← he] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    change LinearMap.BilinForm.baseChange ℂ (Q.compl₁₂ e.symm.toAddMonoidHom.toIntLinearMap
      e.symm.toAddMonoidHom.toIntLinearMap) _ _ = 0
    rw [b2a_baseChange_compl, hs, hs]
    exact hQ.isotropic x hx y hy
  · intro x hx hx0
    rw [← he] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    change 0 < (Complex.I * LinearMap.BilinForm.baseChange ℂ
      (Q.compl₁₂ e.symm.toAddMonoidHom.toIntLinearMap
        e.symm.toAddMonoidHom.toIntLinearMap) _ _).re
    rw [b2a_conj_cplxMap, b2a_baseChange_compl, hs, hs]
    apply hQ.positive x hx
    intro h
    apply hx0
    rw [h, map_zero]

/-! ## The selected covers and their B5 models -/

open HodgeLean.Papers

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

#print axioms b4_riemannExistence
#print axioms b3_exists_intersectionForm

/-- Thirteen fixed, distinct branch points on the Riemann sphere.
Source: G32 v0.16, §3.1; Forster, §1.3. -/
def b4b_branch : Fin 13 → OnePoint ℂ := fun j ↦ ((j.val : ℂ) : OnePoint ℂ)

example : b4b_branch 0 = ((0 : ℂ) : OnePoint ℂ) := by
  simp only [b4b_branch, Fin.val_zero, Nat.cast_zero]

theorem b4b_branch_injective : Function.Injective b4b_branch := by
  intro i j h
  have h' : (i.val : ℂ) = (j.val : ℂ) := OnePoint.coe_injective h
  exact Fin.ext (Nat.cast_injective h')

theorem b4b_sphere_genus : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
  have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
  rw [h, finrank_bot]

end HodgeLean.Foundations.Program
