import HodgeLean.Foundations.Program.SchoenCartierUniversalFieldLift
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerPrincipal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An ideal whose pullback is locally free of rank one on an integral scheme has proper support on a reduced base. -/
theorem s2v_l1b_cartier_support_ne_top
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B'.left] [IsReduced B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U))) :
    I.support ≠ ⊤ := by
  intro h
  have hI : I = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp h
  obtain ⟨x⟩ := (inferInstance : Nonempty B'.left)
  obtain ⟨U, hx, ⟨e⟩⟩ := hcartier x
  haveI : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  have hzero : (I.comap b.left).ideal U = ⊥ := by
    rw [hI, Scheme.IdealSheafData.comap_bot, Scheme.IdealSheafData.ideal_bot]
    rfl
  have he : e.symm 0 = e.symm 1 := by
    apply Subtype.ext
    have hmem (z : (I.comap b.left).ideal U) : z.val = 0 := by
      exact Ideal.mem_bot.mp (hzero.le z.property)
    exact (hmem _).trans (hmem _).symm
  exact zero_ne_one (e.symm.injective he)

/-- Every retained lift of a dominant field point through the Cartier universal property is dominant. -/
theorem s2v_l1b_retained_field_lift_dominant
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : B'.left, ∃ U : B'.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap b.left).ideal U) ≃ₗ[Γ(B'.left, U)] Γ(B'.left, U)))
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    {K : Type} [Field K] (η : Spec (.of K) ⟶ B.left) [IsDominant η]
    (θ : Spec (.of K) ⟶ B'.left) (hθ : θ ≫ b.left = η) :
    IsDominant θ := by
  have hI := s2v_l1b_cartier_support_ne_top B' B b I hcartier
  obtain ⟨ψ, hψ, hdom⟩ := s2_cartierUniversal_fieldLift B' B b I hI huniv η
  let T := Over.mk (η ≫ B.hom)
  let f : T ⟶ B := Over.homMk η
  let v : T ⟶ B' := Over.homMk θ (by
    rw [← Over.w b, ← Category.assoc, hθ]
    rfl)
  let w : T ⟶ B' := Over.homMk ψ (by
    rw [← Over.w b, ← Category.assoc, hψ]
    rfl)
  obtain ⟨_, _, huniq⟩ := huniv T f (s2_dominant_fieldPoint_cartier η I hI)
  have he : θ = ψ := congrArg Over.Hom.left
    ((huniq v (Over.OverMorphism.ext hθ)).trans
      (huniq w (Over.OverMorphism.ext hψ)).symm)
  exact he ▸ hdom

/-- Dominance propagates along the retained tower without choosing replacement generic maps. -/
theorem s2v_l1b_retained_tower_dominant
    {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (huniv : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    {K : Type} [Field K] (η : ∀ i, Spec (.of K) ⟶ (B i).left)
    [IsDominant (η 0)]
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc) :
    ∀ i, IsDominant (η i) := by
  intro i
  induction i using Fin.induction with
  | zero => infer_instance
  | succ i ih =>
    haveI := ih
    exact s2v_l1b_retained_field_lift_dominant (B i.succ) (B i.castSucc)
      (b i) (I i) (hcartier i) (huniv i) (η i.castSucc) (η i.succ) (hη i)

/-- The exact generic section map is injective for every nonempty open of an integral base. -/
theorem s2v_l1b_dominant_section_map_injective
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η]
    (U : X.Opens) [Nonempty U] (hηU : ⊤ ≤ η ⁻¹ᵁ U) :
    Function.Injective (η.appLE U ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom := by
  let κ : X.functionField ⟶ CommRingCat.of K :=
    Spec.preimage (s2_dominantFieldFactor η)
  have hκ : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η := by
    rw [Spec.map_preimage]
    exact s2_dominantFieldFactor_comp η
  haveI : Subsingleton (Spec X.functionField) := by
    change Subsingleton (PrimeSpectrum X.functionField)
    infer_instance
  have hU : ⊤ ≤ (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U := by
    intro z _
    change X.fromSpecStalk (genericPoint X) z ∈ U
    rw [Subsingleton.elim z (IsLocalRing.closedPoint X.functionField),
      Scheme.fromSpecStalk_closedPoint]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  rw [s2v_l1b_section_map_of_generic_factor X η κ hκ U hU hηU]
  exact κ.hom.injective.comp (X.germToFunctionField_injective U)

/-- Trivialized ideals on an affine neighborhood have generators whose exceptional product stays nonzero in the retained covering field. -/
theorem s2v_l1b_generic_trivialized_product_nonzero
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η]
    (U : X.affineOpens) [Nonempty U.1] (hηU : ⊤ ≤ η ⁻¹ᵁ U.1)
    {J : Type*} [Fintype J] (I : J → Ideal Γ(X, U))
    (e : ∀ j, I j ≃ₗ[Γ(X, U)] Γ(X, U)) :
    ∃ a : J → Γ(X, U), (∀ j, I j = Ideal.span {a j}) ∧
      (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom (∏ j, a j) ≠ 0 := by
  exact s2v_l1b_trivialized_ideal_product_nonzero _
    (s2v_l1b_dominant_section_map_injective X η U.1 hηU) I e

end HodgeLean.Foundations.Program
