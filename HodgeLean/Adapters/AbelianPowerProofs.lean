import HodgeLean.Adapters.AbelianPowerDefs
import HodgeLean.Foundations.ProjectivePoint

/-! # The power `A^r`, stage G3 (part 1): proof obligations

One `_aux` theorem per statement of `AbelianPower.lean`, all open. HC no distance; AV milestone
no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ))

open CartesianMonoidalCategory in
theorem spec_g3_isLimit_fan_aux (r : ℕ) :
    Nonempty (IsLimit (Fan.mk (g3_power A r) (g3_proj A r))) := by
  induction r with
  | zero =>
    exact ⟨IsLimit.mk (fun s => SemiCartesianMonoidalCategory.toUnit s.pt)
      (fun s j => j.as.elim0) (fun _ _ _ => SemiCartesianMonoidalCategory.toUnit_unique _ _)⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    refine ⟨(extendFanIsLimit (fun _ : Fin (n + 1) => A) ih
      (tensorProductIsBinaryProduct A (g3_power A n))).ofIsoLimit
      (Cone.ext (Iso.refl _) ?_)⟩
    rintro ⟨j⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (Category.id_comp (fst A (g3_power A n))).symm
    · exact (Category.id_comp (snd A (g3_power A n) ≫ g3_proj A n i)).symm

open CartesianMonoidalCategory in
theorem spec_g3_isCommMonObj_power_aux [GrpObj A] [IsCommMonObj A] (r : ℕ) :
    IsCommMonObj (g3_power A r) := by
  induction r with
  | zero => exact (inferInstance : IsCommMonObj (𝟙_ (Over (Spec ↧ℂ))))
  | succ n ih => exact (inferInstance : IsCommMonObj (A ⊗ g3_power A n))

open CartesianMonoidalCategory in
theorem spec_g3_isMonHom_proj_aux [GrpObj A] (r : ℕ) (i : Fin r) :
    IsMonHom (g3_proj A r i) := by
  induction r with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (inferInstance : IsMonHom (fst A (g3_power A n)))
    · have := ih i
      have : IsMonHom (snd A (g3_power A n)) := inferInstance
      exact (inferInstance : IsMonHom (snd A (g3_power A n) ≫ g3_proj A n i))

/-- The constant map `1 : X ⟶ M` is a monoid homomorphism, since `1 = toUnit ≫ η`. -/
private theorem g3_isMonHom_one {X M : Over (Spec ↧ℂ)} [MonObj X] [MonObj M] :
    IsMonHom (1 : X ⟶ M) := by
  rw [Hom.one_def]; infer_instance

open CartesianMonoidalCategory in
theorem spec_g3_isMonHom_incl_aux [GrpObj A] (r : ℕ) (i : Fin r) :
    IsMonHom (g3_incl A r i) := by
  induction r with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have := g3_isMonHom_one (X := A) (M := g3_power A n)
      exact (inferInstance : IsMonHom (lift (𝟙 A) (1 : A ⟶ g3_power A n)))
    · have := ih i
      have := g3_isMonHom_one (X := A) (M := A)
      exact (inferInstance : IsMonHom (lift (1 : A ⟶ A) (g3_incl A n i)))

open CartesianMonoidalCategory in
theorem spec_g3_incl_proj_aux [GrpObj A] (r : ℕ) (i j : Fin r) :
    g3_incl A r i ≫ g3_proj A r j = if i = j then 𝟙 A else 1 := by
  induction r with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · change lift (𝟙 A) 1 ≫ fst A (g3_power A n) = _
      simp
    · have := spec_g3_isMonHom_proj_aux A n j
      change lift (𝟙 A) 1 ≫ snd A (g3_power A n) ≫ g3_proj A n j = _
      simp [MonObj.one_comp, (Fin.succ_ne_zero j).symm]
    · change lift 1 (g3_incl A n i) ≫ fst A (g3_power A n) = _
      simp [Fin.succ_ne_zero]
    · change lift 1 (g3_incl A n i) ≫ snd A (g3_power A n) ≫ g3_proj A n j = _
      simp [ih]

open CartesianMonoidalCategory in
theorem spec_g3_prod_proj_incl_aux [GrpObj A] [IsCommMonObj A] {r : ℕ}
    [IsCommMonObj (g3_power A r)] :
    ∏ i, (g3_proj A r i ≫ g3_incl A r i) = 𝟙 (g3_power A r) := by
  obtain ⟨h⟩ := spec_g3_isLimit_fan_aux A r
  refine Fan.IsLimit.hom_ext h _ _ fun j => ?_
  have := spec_g3_isMonHom_proj_aux A r j
  have key := map_prod (IsMonHom.monoidHom (g3_proj A r j) (g3_power A r))
    (fun i => g3_proj A r i ≫ g3_incl A r i) Finset.univ
  simp only [IsMonHom.monoidHom_apply, Category.assoc, spec_g3_incl_proj_aux] at key
  change _ ≫ g3_proj A r j = 𝟙 _ ≫ g3_proj A r j
  rw [Category.id_comp]
  rw [key, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [hij, MonObj.comp_one]
  · simp

theorem spec_g3_proj_incl_one_aux [GrpObj A] :
    g3_proj A 1 0 = (ρ_ A).hom ∧ g3_incl A 1 0 = (ρ_ A).inv := by
  refine ⟨(CartesianMonoidalCategory.rightUnitor_hom A).symm, ?_⟩
  change CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ 𝟙_ (Over (Spec ↧ℂ))) = (ρ_ A).inv
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.rightUnitor_inv_fst]
  · exact CartesianMonoidalCategory.toUnit_unique _ _

theorem spec_g3_isCommMonObj_of_power_aux [GrpObj A] {r : ℕ} (hr : 0 < r)
    [IsCommMonObj (g3_power A r)] : IsCommMonObj A := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hsp : CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n) ≫
      CartesianMonoidalCategory.fst A (g3_power A n) = 𝟙 A :=
    CartesianMonoidalCategory.lift_fst _ _
  rw [isCommMonObj_iff_isMulCommutative]
  refine fun X => ⟨⟨fun f g => ?_⟩⟩
  have key : ∀ f g : X ⟶ A, f * g =
      ((f ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) *
        (g ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) :
          X ⟶ g3_power A (n + 1)) ≫
        CartesianMonoidalCategory.fst A (g3_power A n) := by
    intro f g
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hsp, Category.comp_id, Category.comp_id]
  have hc : ((f ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) *
      (g ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) : X ⟶ g3_power A (n + 1)) =
      (g ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) *
        (f ≫ CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ g3_power A n)) :=
    @mul_comm (X ⟶ g3_power A (n + 1)) _ _ _
  rw [key f g, hc, ← key g f]

theorem spec_g3_smooth_power_aux [Smooth A.hom] (r : ℕ) : Smooth (g3_power A r).hom := by
  induction r with
  | zero => change Smooth (𝟙 _); infer_instance
  | succ n ih =>
    change Smooth (pullback.fst A.hom (g3_power A n).hom ≫ A.hom)
    infer_instance

theorem spec_g3_smoothOfRelativeDimension_power_aux (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (r : ℕ) : SmoothOfRelativeDimension (r * d) (g3_power A r).hom := by
  induction r with
  | zero => rw [zero_mul]; change SmoothOfRelativeDimension 0 (𝟙 _); infer_instance
  | succ n ih =>
    change SmoothOfRelativeDimension _ (pullback.fst A.hom (g3_power A n).hom ≫ A.hom)
    rw [Nat.succ_mul]
    infer_instance

theorem spec_g3_isIntegral_power_aux [Smooth A.hom] [GeometricallyIntegral A.hom] (r : ℕ) :
    IsIntegral (g3_power A r).left := by
  induction r with
  | zero => change IsIntegral (Spec ↧ℂ); infer_instance
  | succ n ih =>
    have := spec_g3_smooth_power_aux A n
    have : IsLocallyNoetherian (g3_power A n).left :=
      LocallyOfFiniteType.isLocallyNoetherian (g3_power A n).hom
    change IsIntegral (pullback A.hom (g3_power A n).hom)
    infer_instance

theorem spec_g3_isIntegral_power_zero_aux : IsIntegral (g3_power A 0).left := by
  change IsIntegral (Spec ↧ℂ)
  infer_instance

theorem spec_g3_isProjective_power_zero_aux : IsProjective (g3_power A 0).hom := by
  exact HodgeLean.Foundations.isProjective_specComplex_id

theorem spec_g3_isIntegral_power_one_aux [IsIntegral A.left] :
    IsIntegral (g3_power A 1).left := by
  let e : (g3_power A 1).left ≅ A.left := (Over.forget _).mapIso (ρ_ A)
  exact IsIntegral.of_isIso e.inv

theorem spec_g3_isProjective_power_one_aux [IsProjective A.hom] :
    IsProjective (g3_power A 1).hom := by
  obtain ⟨P⟩ := (inferInstance : IsProjective A.hom).nonempty_presentation
  have := P.isClosedImmersion
  let e : (g3_power A 1).left ≅ A.left := (Over.forget _).mapIso (ρ_ A)
  have he : e.hom ≫ A.hom = (g3_power A 1).hom := Over.w (ρ_ A).hom
  exact ⟨⟨{ ambientDimension := P.ambientDimension
            immersion := e.hom ≫ P.immersion
            immersion_toBase := by rw [Category.assoc, P.immersion_toBase, he] }⟩⟩

end HodgeLean.Adapters
