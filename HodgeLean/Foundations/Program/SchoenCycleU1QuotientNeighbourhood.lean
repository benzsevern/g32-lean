import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Affine quotient neighbourhoods inside invariant opens -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An invariant open around an ordered divisor contains the whole preimage of
an affine neighbourhood of its retained quotient point, including at collisions.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1;
Hartshorne, Algebraic Geometry, II.3, finite morphisms and closed points. -/
theorem s2e_u1_quotient_affine_chart_inside_invariant_open
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (W : (g3_power Z N).left.Opens)
    (hinv : ∀ σ, W ≤ (s2_permute Z N σ).left ⁻¹ᵁ W)
    (x : ComplexPoint (g3_power Z N)) (hx : x.underlying ∈ W) :
    ∃ U : B.left.Opens, IsAffineOpen U ∧ (Point.map γ x).underlying ∈ U ∧ γ.left ⁻¹ᵁ U ≤ W := by
  classical
  let X := g3_power Z N
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let b := γ.left x.underlying
  have hb : IsClosed ({b} : Set B.left) := by
    have hb0 : IsClosed ({(Point.map γ x).underlying} : Set B.left) :=
      ((pointEquivClosedPoint B.hom) ⟨(Point.map γ x).left, by simp⟩).2
    simpa only [b, Point.underlying_map] using hb0
  let F : Set X.left := (γ.left ⁻¹' {b}) ∩ (W : Set X.left)ᶜ
  have hF : IsClosed F := (hb.preimage γ.left.continuous).inter W.isOpen.isClosed_compl
  have hFc : F ∩ closedPoints X.left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyF, hy⟩
    let yp : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hy) (by simp)
    have hyp : yp.underlying = y := pointOfClosedPoint_apply X.hom y hy _
    have hyb : γ.left y = b := hyF.1
    have hxy : Point.map γ x = Point.map γ yp := by
      apply underlying_injective_of_locallyOfFiniteType
      simp only [Point.underlying_map, hyp]
      exact hyb.symm
    obtain ⟨σ, hσ⟩ := s2e_step1_retained_symmetric_orbits Z B N γ hsurj hγ hquot x yp hxy
    have hw : yp.underlying ∈ W := by
      rw [← hσ, Point.underlying_map]
      exact hinv σ hx
    exact hyF.2 (hyp ▸ hw)
  have hFe : F = ∅ := by
    have he := JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed
    rw [hFc, closure_empty, hF.closure_eq] at he
    exact he.symm
  have hclosed : IsClosed (γ.left '' (W : Set X.left)ᶜ) :=
    γ.left.isClosedMap _ W.isOpen.isClosed_compl
  let V : B.left.Opens := ⟨(γ.left '' (W : Set X.left)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hbV : b ∈ V := by
    rintro ⟨y, hy, hyb⟩
    have hyF : y ∈ F := ⟨hyb, hy⟩
    simpa only [hFe, Set.mem_empty_iff_false] using hyF
  obtain ⟨_, ⟨U, hU, rfl⟩, hbU, hUV⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open hbV V.isOpen
  refine ⟨U, hU, ?_, ?_⟩
  · change b ∈ (U : Set B.left)
    exact hbU
  · intro y hy
    by_contra hn
    exact hUV hy ⟨y, hn, rfl⟩

end HodgeLean.Foundations.Program
