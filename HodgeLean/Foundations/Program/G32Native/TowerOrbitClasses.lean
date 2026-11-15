import HodgeLean.Foundations.Program.SchoenCycleC2
import HodgeLean.Adapters.CyclePushforward

/-! # Retained tower orbit cycles

T22 and T23 of SchoenTransferJ2NativeInput retain the actual rational orbit
cycle, its proper image, and the specified linear map G.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Source coheight and normalized representatives for every rational coefficient vector.
Source: Schoen (1988), printed p. 15; Fulton, Intersection Theory, 19.1–19.2. -/
theorem tower_orbit_source
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (hcodim : ∀ t : Fin m, ∀ x ∈
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
      Order.coheight x = k)
    (c : ∀ t : Fin m,
      s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k)
    (hc : ∀ t : Fin m, a3b4_IsCycleClass W.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t))
    (a : Fin m → ℚ) :
    let γ := s2e_rationalOrbitCycle ι δ m a
    (∀ x ∈ γ.support, Order.coheight x = k) ∧
    ∃ cr, a3b4_IsCycleClass W.hom γ k cr ∧
      s2e_classToAbsolute W γ k cr = ∑ t : Fin m, a t •
        s2e_classToAbsolute W
          (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k (c t) := by
  exact ⟨s2e_rationalOrbitCycle_coheight ι δ k m hcodim a,
    s2e_rationalOrbitCycle_normalized_sum ι δ k m himm hdisj c hc a⟩

/-- The proper image of a finite orbit sum has no prime outside the images of
its actual component generic points; coefficients may cancel or have degree zero.
Source: Fulton, Intersection Theory, 1.4. -/
theorem tower_orbit_pushed_coheight
    {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (k m : ℕ)
    (himage : ∀ t : Fin m, Order.coheight
      (φ.left ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left))) = k)
    (a : Fin m → ℚ) :
    ∀ x ∈ (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ m a)).support,
      Order.coheight x = k := by
  classical
  let points : Fin m → W.left := fun t =>
    (ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)
  let s : Finset W.left := Finset.univ.image points
  have hs : (s2e_rationalOrbitCycle ι δ m a).support ⊆ s := by
    intro x hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp
      (s2e_rationalOrbitCycle_support_subset ι δ m a hx)
    rw [s2e_componentCycle_support] at ht
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩
  intro x hx
  have hx' := a1x_pushforward_support φ.left
    (s2e_rationalOrbitCycle ι δ m a) s hs hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
  exact himage t

/-- The actual pushforward retains the residue degree of each orbit prime.
Source: Fulton, Intersection Theory, 1.4. -/
theorem tower_orbit_pushforward_formula
    {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (δ : W ⟶ W) (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (m : ℕ) (a : Fin m → ℚ) :
    a1p_pushforward φ.left (s2e_rationalOrbitCycle ι δ m a) =
      ∑ t : Fin m,
        (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ).mapRange
          (a t * (a1p_degree φ.left
            ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left)) : ℚ) * ·)
          (mul_zero _) := by
  classical
  let F : AlgebraicCycle W.left ℚ →+ AlgebraicCycle W₀.left ℚ :=
    { toFun := a1p_pushforward φ.left
      map_zero' := a1x_pushforward_zero φ.left
      map_add' := a1p_pushforward_add φ.left }
  change F (∑ t : Fin m, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  change a1p_pushforward φ.left
    ((s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).mapRange
      (a t * ·) (mul_zero _)) = _
  rw [a1p_pushforward_mul]
  unfold s2e_componentCycle
  rw [a1p_pushforward_single]
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.single_apply, Over.comp_left,
    Scheme.Hom.comp_apply, one_mul]
  split_ifs <;> simp only [mul_one, mul_zero]

end HodgeLean.Foundations.Program.G32Native
