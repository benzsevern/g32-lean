import HodgeLean.Foundations.AbelianQuotient.Surjectivity

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A surjective homomorphism gives an injective rational H¹ pullback. -/
theorem injective_pullback_of_surjective {P Q : Variety} (f : Hom P Q)
    (hs : Function.Surjective (Point.map f.hom)) :
    Function.Injective (homPullback f.hom 1) := by
  obtain ⟨A, hA⟩ := spec_abelianHom_analyticRepresentation f.hom
  have hsurj := abq_analyticRepresentation_surjective P Q f.hom hs A hA
  letI := isZLattice_complexExponentialLattice P.X (dim P.X.left)
  letI := discrete_complexExponentialLattice P.X (dim P.X.left)
  letI := isZLattice_complexExponentialLattice Q.X (dim Q.X.left)
  letI := discrete_complexExponentialLattice Q.X (dim Q.X.left)
  let b := abelianLatticeBasis Q.X
  let bR := b.ofZLatticeBasis ℝ (abelianPeriodLattice Q.X)
  let cR := (abelianLatticeBasis P.X).ofZLatticeBasis ℝ (abelianPeriodLattice P.X)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv Q.X
  let χ := e x
  let F : (Fin (dim Q.X.left) → ℂ) →ₗ[ℝ] ℝ :=
    bR.constr ℝ (fun i => (χ (b i) : ℝ))
  have hF : ∀ l : abelianPeriodLattice Q.X, F l = (χ l : ℝ) := by
    intro l
    simp only [F, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
      smul_eq_mul]
    simp only [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    conv_rhs => rw [← b.sum_repr l]
    simp only [map_sum, map_zsmul, zsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  have hFA : F.comp (A.restrictScalars ℝ) = 0 := by
    apply cR.ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hc : cR i = (abelianLatticeBasis P.X i : Fin (dim P.X.left) → ℂ) :=
      Module.Basis.ofZLatticeBasis_apply ℝ _ _ i
    rw [hc]
    let l := abelianLatticeBasis P.X i
    have hl := homPullback_analyticRepresentation_mem_lattice f.hom A hA l
    have ht := abelianPeriod_homPullback_analyticRepresentation f.hom A hA x l
    rw [hx, map_zero, Pi.zero_apply] at ht
    change F (A l) = 0
    rw [hF (⟨A l, hl⟩ : abelianPeriodLattice Q.X)]
    change (e x ⟨A l, hl⟩ : ℝ) = 0
    rw [he, ← ht, Rat.cast_zero]
  have hFzero : F = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    exact LinearMap.congr_fun hFA v
  apply e.injective
  apply AddMonoidHom.ext
  intro l
  have hl := hF l
  rw [hFzero, LinearMap.zero_apply] at hl
  have hχ : χ l = 0 := by exact_mod_cast hl.symm
  simpa only [map_zero, AddMonoidHom.zero_apply] using hχ

end HodgeLean.Foundations.AbelianQuotient
