import HodgeLean.Foundations.Program.SchoenTowerI2bUnpairedBlowupSupport
import HodgeLean.Foundations.Program.SchoenTowerI2bBranchRegularity

/-! Applying the unpaired support construction to the retained branch chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained etale branch chart puts every actual upper point over a deeper unpaired stratum in its strict transform.
Source: independent retained coordinates and the actual unpaired blowup support construction. -/
theorem s2v_i2b_retained_chart_unpaired_support
    {ι : Type} [DecidableEq ι] (n : ℕ)
    (X Y U : Over (Spec ↧ℂ)) [IsAffine U.left]
    (a : U ⟶ X) [IsOpenImmersion a.left] (b : Y ⟶ X)
    (D : ι → X.left.IdealSheafData) (A B t : ι)
    (hAB : A ≠ B) (htA : t ≠ A) (htB : t ≠ B)
    (I : X.left.IdealSheafData) (hI : I = D A ⊔ D B)
    (hcartier : ∀ y : Y.left, ∃ V : Y.left.affineOpens, y ∈ V.1 ∧
      Nonempty (((I.comap b.left).ideal V) ≃ₗ[Γ(Y.left, V)] Γ(Y.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ W : T.left.affineOpens, x ∈ W.1 ∧
        Nonempty (((I.comap f.left).ideal W) ≃ₗ[Γ(T.left, W)] Γ(T.left, W))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (x : ComplexPoint X) (hx : x ∈ Set.range (Point.map a))
    (hcentre : x.left (IsLocalRing.closedPoint ℂ) ∈ I.support)
    (ht : x.left (IsLocalRing.closedPoint ℂ) ∈ (D t).support)
    (c : MvPolynomial (Fin n) ℂ →+* Γ(U.left, ⊤)) (hc : c.Etale)
    (J : Finset ι) (κ : J ↪ Fin n) (z : ι → Γ(U.left, ⊤))
    (hJ : ∀ s, s ∈ J ↔ x.left (IsLocalRing.closedPoint ℂ) ∈ (D s).support)
    (hz : ∀ s : J, z s = c (MvPolynomial.X (κ s)))
    (hideal : ∀ s, ((D s).comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {z s}) :
    ∀ y : Y.left, b.left y = x.left (IsLocalRing.closedPoint ℂ) →
      y ∈ (s2c_strictTransform b.left (D t) I).support := by
  have hpair : x.left (IsLocalRing.closedPoint ℂ) ∈ (D A).support ∧
      x.left (IsLocalRing.closedPoint ℂ) ∈ (D B).support := by
    rw [hI, Scheme.IdealSheafData.support_sup] at hcentre
    exact hcentre
  let aJ : J := ⟨A, (hJ A).mpr hpair.1⟩
  let bJ : J := ⟨B, (hJ B).mpr hpair.2⟩
  let tJ : J := ⟨t, (hJ t).mpr ht⟩
  have haJbJ : aJ ≠ bJ := fun he => hAB (congrArg Subtype.val he)
  have htJaJ : tJ ≠ aJ := fun he => htA (congrArg Subtype.val he)
  have htJbJ : tJ ≠ bJ := fun he => htB (congrArg Subtype.val he)
  obtain ⟨hreg, hreg', hregt, hregt'⟩ :=
    s2v_i2b_retained_branch_regular_sequences n c hc J κ z hz aJ bJ tJ haJbJ htJaJ htJbJ
  have hIring : (I.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ =
      Ideal.span {z A, z B} := by
    rw [hI, Scheme.IdealSheafData.comap_sup]
    change ((D A).comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ ⊔
      ((D B).comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = _
    rw [hideal A, hideal B]
    exact (Ideal.span_insert (z A) {z B}).symm
  have hrange : x.left (IsLocalRing.closedPoint ℂ) ∈ Set.range a.left := by
    obtain ⟨xU, hxU⟩ := hx
    have he := congrArg (fun q : ComplexPoint X => q.left) hxU
    change xU.left ≫ a.left = x.left at he
    have hp := congrArg (fun f : Spec ↧ℂ ⟶ X.left => f (IsLocalRing.closedPoint ℂ)) he
    rw [Scheme.Hom.comp_apply] at hp
    exact ⟨xU.left (IsLocalRing.closedPoint ℂ), hp⟩
  intro y hy
  apply s2v_i2b_unpaired_blowup_support_inclusion X Y U a b (D t) I hcartier hblowup
    (z A) (z B) (z t) hIring (hideal t) hreg hreg' hregt hregt' y
  · rw [hy]
    exact hrange
  · rw [hy]
    exact ht

end HodgeLean.Foundations.Program
