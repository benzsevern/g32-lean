import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals
import HodgeLean.Foundations.Program.SchoenCycleCartierCharts

/-! # Global paired Cartier branch avoidance
The local ideal-module tests supply their own compatible affine charts.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Paired restrictions and the ambient and source local Cartier tests
force global avoidance of the reduced branch locus outside the centre. -/
theorem s2e_paired_cartier_branch_avoidance
    {Q X : Scheme} (u : Q ⟶ X) (I J : X.IdealSheafData)
    (hpair : I.comap u = J.comap u)
    (hambient : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (((I ⊔ J).ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)))
    (hslice : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty ((((I ⊔ J).comap u).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V))) :
    Disjoint (Set.range u)
      (closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨q, rfl⟩ hx
  obtain ⟨U, V, _, hqV, hVU, hfreeU, hfreeV⟩ :=
    s2e_compatible_cartier_charts u (I ⊔ J) hambient hslice q
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine V.1.toScheme := V.2
  let t : V.1.toScheme ⟶ U.1.toScheme := u.resLE U.1 V.1 hVU
  have hsq : t ≫ U.1.ι = V.1.ι ≫ u := u.resLE_comp_ι hVU
  have hpair' : (I.comap U.1.ι).comap t = (J.comap U.1.ι).comap t := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      hsq, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hpair]
  have ha := s2e_cartier_free_on_open_subscheme (I ⊔ J) U.1 hfreeU
  have hs := s2e_cartier_free_on_open_subscheme ((I ⊔ J).comap u) V.1 hfreeV
  have havoid := s2e_affine_paired_cartier_branch_avoidance t
    (I.comap U.1.ι) (J.comap U.1.ι) hpair'
    (by rw [← Scheme.IdealSheafData.comap_sup]; exact ha)
    (by rw [← Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp,
          hsq, Scheme.IdealSheafData.comap_comp]; exact hs)
  let p : V.1.toScheme := ⟨q, hqV⟩
  have hpoint : U.1.ι (t p) = u q := by
    exact congrArg (fun f : V.1.toScheme ⟶ X => f p) hsq
  have hlocal : t p ∈ U.1.ι ⁻¹' closure
      ((I.support : Set X) \ ((I ⊔ J).support : Set X)) := by
    change U.1.ι (t p) ∈ closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))
    rwa [hpoint]
  rw [U.1.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.1.ι.continuous,
    Set.preimage_sdiff] at hlocal
  have hlocal' : t p ∈ closure (((I.comap U.1.ι).support : Set U.1.toScheme) \
      (((I.comap U.1.ι) ⊔ (J.comap U.1.ι)).support : Set U.1.toScheme)) := by
    rw [← Scheme.IdealSheafData.comap_sup,
      Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact hlocal
  exact Set.disjoint_left.mp havoid ⟨p, rfl⟩ hlocal'

/-- A lifted paired Cartier slice avoids both actual reduced strict branch
transforms, using the ambient exceptional and source Cartier tests. -/
theorem s2e_lifted_pair_strict_branch_avoidance
    {Q B B' : Scheme} (b : B' ⟶ B) (ℓ : Q ⟶ B) (u : Q ⟶ B')
    (hfac : u ≫ b = ℓ) (D₁ D₂ : B.IdealSheafData)
    (hpair : D₁.comap ℓ = D₂.comap ℓ)
    (hambient : ∀ x : B', ∃ U : B'.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap b).ideal U) ≃ₗ[Γ(B', U)] Γ(B', U)))
    (hslice : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap ℓ).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V))) :
    Disjoint (Set.range u)
      (((s2c_strictTransform b D₁ (D₁ ⊔ D₂)).support : Set B') ∪
        ((s2c_strictTransform b D₂ (D₁ ⊔ D₂)).support : Set B')) := by
  have hpair' : (D₁.comap b).comap u = (D₂.comap b).comap u := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfac, hpair]
  have ha : ∀ x : B', ∃ U : B'.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁.comap b) ⊔ (D₂.comap b)).ideal U) ≃ₗ[Γ(B', U)] Γ(B', U)) := by
    rw [← Scheme.IdealSheafData.comap_sup]
    exact hambient
  have hs : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty (((((D₁.comap b) ⊔ (D₂.comap b)).comap u).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V)) := by
    rw [← Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp, hfac]
    exact hslice
  have hfirst := s2e_paired_cartier_branch_avoidance u (D₁.comap b) (D₂.comap b) hpair' ha hs
  have hsecond := s2e_paired_cartier_branch_avoidance u (D₂.comap b) (D₁.comap b) hpair'.symm
    (by rw [sup_comm]; exact ha) (by rw [sup_comm]; exact hs)
  apply disjoint_sup_right.mpr
  constructor
  · rw [s2e_strictTransform_support_eq_removed_pullback, Scheme.IdealSheafData.comap_sup]
    exact hfirst
  · rw [s2e_strictTransform_support_eq_removed_pullback, Scheme.IdealSheafData.comap_sup,
      sup_comm (D₁.comap b) (D₂.comap b)]
    exact hsecond

/-- A paired integral Cartier slice lifts uniquely as its actual strict
transform and avoids both processed branch divisors. -/
theorem s2e_paired_blowup_slice_strict_lift_avoiding_branches
    {Q B B' : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (b : B' ⟶ B) [IsSeparated b.left] (D₁ D₂ : B.left.IdealSheafData)
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D₁ ⊔ D₂).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)]
          Γ(T.left, U))) → ∃! u : T ⟶ B', u ≫ b = f)
    (hambient : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U)))
    (ℓ : Q ⟶ B) [IsClosedImmersion ℓ.left]
    (hpair : D₁.comap ℓ.left = D₂.comap ℓ.left)
    (hCartier : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((D₁.comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U))) :
    ∃! u : Q ⟶ B', u ≫ b = ℓ ∧ IsClosedImmersion u.left ∧
      u.left.ker = s2c_strictTransform b.left ℓ.left.ker (D₁ ⊔ D₂) ∧
      Disjoint (Set.range u.left)
        (((s2c_strictTransform b.left D₁ (D₁ ⊔ D₂)).support : Set B'.left) ∪
          ((s2c_strictTransform b.left D₂ (D₁ ⊔ D₂)).support : Set B'.left)) := by
  obtain ⟨u, ⟨hu, himm, htrans⟩, huniq⟩ :=
    s2e_paired_blowup_slice_strict_lift b D₁ D₂ hblowup ℓ hpair hCartier
  have hcentre : ∀ x : Q.left, ∃ U : Q.left.affineOpens, x ∈ U.1 ∧
      Nonempty ((((D₁ ⊔ D₂).comap ℓ.left).ideal U) ≃ₗ[Γ(Q.left, U)] Γ(Q.left, U)) := by
    rw [s2e_paired_centre_comap ℓ.left D₁ D₂ hpair]
    exact hCartier
  have havoid := s2e_lifted_pair_strict_branch_avoidance b.left ℓ.left u.left
    (congrArg Over.Hom.left hu) D₁ D₂ hpair hambient hcentre
  refine ⟨u, ⟨hu, himm, htrans, havoid⟩, ?_⟩
  intro v hv
  exact huniq v ⟨hv.1, hv.2.1, hv.2.2.1⟩

end HodgeLean.Foundations.Program
