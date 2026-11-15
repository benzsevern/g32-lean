import HodgeLean.Foundations.NormalPresentation.Defs

/-! # Open bodies for positive normal presentations

All hypotheses concern the supplied arrows, their kernels or local coordinates.
No hypothesis packages a desired normal or Euler comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.NormalPresentation
variable {C : Type*} [Category* C] [Abelian C] {L A E N : C}

/-- The distinguished ideal injection makes the canonical sequence short exact.
Source: Fulton, Intersection Theory, §B.7; Hartshorne, II.5.
Concrete instance: Checks.canonical_positive. -/
theorem canonical_shortExact_aux (a : L ⟶ A) (b : L ⟶ E) [Mono a] :
    (canonical a b).ShortExact := by
  letI : Mono (relation a b) := mono_of_mono_fac
    (show relation a b ≫ biprod.fst = a by simp [relation])
  change (ShortComplex.mk (relation a b) (cokernel.π (relation a b)) _).ShortExact
  exact ⟨ShortComplex.exact_cokernel (relation a b)⟩

/-- The same quotient retains the free directions and the actual divisor cokernel.
Source: Fulton, Intersection Theory, §B.7; Hartshorne, II.6.
Concrete instance: Checks.elementary_positive. -/
theorem elementary_shortExact_aux (a : L ⟶ A) (b : L ⟶ E) [Mono a] :
    (elementary a b).ShortExact := by
  letI : Mono (relation a b) := mono_of_mono_fac
    (show relation a b ≫ biprod.fst = a by simp [relation])
  have hm : Mono (freeArrow a b) := by
    apply Preadditive.mono_of_cancel_zero
    intro T x hx
    have hx' : (x ≫ biprod.inr) ≫ cokernel.π (relation a b) = 0 := by
      simpa [freeArrow, projection, Category.assoc] using hx
    let l := Abelian.monoLift (relation a b) (x ≫ biprod.inr) hx'
    have hl : l ≫ relation a b = x ≫ biprod.inr := Abelian.monoLift_comp _ _ _
    have hla : l ≫ a = 0 := by
      have := congrArg (fun f => f ≫ biprod.fst) hl
      simpa [relation, Category.assoc] using this
    have hz : l = 0 := (cancel_mono a).mp (by simpa using hla)
    have := congrArg (fun f => f ≫ biprod.snd) hl
    simpa [hz, relation, Category.assoc] using this.symm
  have hd : projection a b ≫ divisorArrow a b = biprod.fst ≫ cokernel.π a :=
    cokernel.π_desc _ _ _
  have he : Epi (divisorArrow a b) := epi_of_epi_fac hd
  letI : Epi (elementary a b).g := he
  letI : Epi (projection a b) := inferInstanceAs (Epi (cokernel.π (relation a b)))
  have hc : IsColimit (CokernelCofork.ofπ (elementary a b).g (elementary a b).zero) := by
    change IsColimit (CokernelCofork.ofπ (divisorArrow a b) (elementary a b).zero)
    apply CokernelCofork.IsColimit.ofπ'
    intro T k hk
    have hk' : biprod.inr ≫ projection a b ≫ k = 0 := by
      simpa only [elementary, freeArrow, Category.assoc] using hk
    have hak : a ≫ biprod.inl ≫ projection a b ≫ k = 0 := by
      have hr : relation a b = a ≫ biprod.inl + b ≫ biprod.inr := by
        apply biprod.hom_ext <;> simp [relation]
      have h := congrArg (fun f : L ⟶ A ⊞ E => f ≫ projection a b ≫ k) hr
      have hzero : relation a b ≫ projection a b ≫ k = 0 := by
        simp [projection]
      rw [hzero, Preadditive.add_comp] at h
      simpa only [Category.assoc, hk', comp_zero, add_zero] using h.symm
    refine ⟨cokernel.desc a (biprod.inl ≫ projection a b ≫ k) hak, ?_⟩
    change divisorArrow a b ≫ _ = k
    apply (cancel_epi (projection a b)).mp
    rw [← Category.assoc, hd]
    simp only [Category.assoc, cokernel.π_desc]
    apply biprod.hom_ext'
    · simp
    · simpa using hk'.symm
  letI : Mono (elementary a b).f := hm
  letI : Epi (elementary a b).g := he
  exact ⟨(elementary a b).exact_of_g_is_cokernel hc⟩

private def shear (v : A ⟶ E) : A ⊞ E ⟶ A ⊞ E :=
  biprod.lift biprod.fst (biprod.snd + biprod.fst ≫ v)

private lemma shear_relation (a : L ⟶ A) (t : L ⟶ E) (v : A ⟶ E) :
    relation a t ≫ shear v = relation a (t + a ≫ v) := by
  apply biprod.hom_ext <;> simp [relation, shear, Preadditive.comp_add]

private def forward (a : L ⟶ A) (b : L ⟶ E) (u : A ⟶ E) : quotient a b ⟶ quotient a (b + a ≫ u) :=
  comparison a b (shear u ≫ projection a (b + a ≫ u)) (by
    rw [← Category.assoc, shear_relation]; exact cokernel.condition _)

private def backward (a : L ⟶ A) (b : L ⟶ E) (u : A ⟶ E) : quotient a (b + a ≫ u) ⟶ quotient a b :=
  comparison a (b + a ≫ u) (shear (-u) ≫ projection a b) (by
    rw [← Category.assoc, shear_relation]
    have h : (b + a ≫ u) + a ≫ (-u) = b := by simp [Preadditive.comp_neg]
    rw [h]; exact cokernel.condition _)

private def transport (a : L ⟶ A) (b : L ⟶ E) (u : A ⟶ E) : quotient a b ≅ quotient a (b + a ≫ u) where
  hom := forward a b u
  inv := backward a b u
  hom_inv_id := by
    apply (cancel_epi (cokernel.π (relation a b))).mp
    simp only [forward, backward, comparison, projection, cokernel.π_desc_assoc,
      Category.assoc, cokernel.π_desc, Category.comp_id]
    have h : shear u ≫ shear (-u) = 𝟙 (A ⊞ E) := by
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        simp [shear, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    rw [← Category.assoc, h, Category.id_comp]
  inv_hom_id := by
    apply (cancel_epi (cokernel.π (relation a (b + a ≫ u)))).mp
    simp only [forward, backward, comparison, projection, cokernel.π_desc_assoc,
      Category.assoc, cokernel.π_desc, Category.comp_id]
    have h : shear (-u) ≫ shear u = 𝟙 (A ⊞ E) := by
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
        simp [shear, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    rw [← Category.assoc, h, Category.id_comp]


/-- Changing the transverse column by a multiple of the distinguished ideal
preserves the divisor projection and fixes the retained directions.
Source: Fulton, Intersection Theory, §B.7, change of presentation.
Concrete instance: Checks.fixed_hyperplane_positive. -/
theorem fixed_hyperplane_transport_aux (a : L ⟶ A) (b : L ⟶ E) (u : A ⟶ E) :
    ∃ e : quotient a b ≅ quotient a (b + a ≫ u),
      projection a b ≫ e.hom =
        (biprod.lift biprod.fst (biprod.snd + biprod.fst ≫ u)) ≫
          projection a (b + a ≫ u) ∧
      freeArrow a b ≫ e.hom = freeArrow a (b + a ≫ u) ∧
      e.hom ≫ divisorArrow a (b + a ≫ u) = divisorArrow a b := by
  refine ⟨transport a b u, ?_⟩
  constructor
  · exact cokernel.π_desc _ _ _
  constructor
  · have h : (biprod.inr : E ⟶ A ⊞ E) ≫ shear u = biprod.inr := by
      apply biprod.hom_ext <;> simp [shear, Preadditive.comp_add]
    simp only [freeArrow, transport, forward, comparison, projection,
      Category.assoc, cokernel.π_desc]
    rw [← Category.assoc, h]
  · apply (cancel_epi (cokernel.π (relation a b))).mp
    simp [transport, forward, comparison, projection, divisorArrow, Category.assoc, shear]

/-- Where the distinguished coordinate is invertible, the quotient is the
retained free module; its chart records the transverse column and its sign.
Source: Hartshorne, II.5 and II.8, local frames of a presented module.
Concrete instance: Checks.quotient_chart_positive. -/
theorem quotient_chart_aux (a : L ⟶ A) (b : L ⟶ E) [IsIso a] :
    ∃ e : quotient a b ≅ E,
      projection a b ≫ e.hom =
        biprod.snd - biprod.fst ≫ inv a ≫ b ∧
      freeArrow a b ≫ e.hom = 𝟙 E := by
  let q : A ⊞ E ⟶ E := biprod.desc (-(inv a ≫ b)) (𝟙 E)
  have hq : relation a b ≫ q = 0 := by
    simp [relation, q]
  let e : quotient a b ≅ E := {
    hom := comparison a b q hq
    inv := freeArrow a b
    hom_inv_id := by
      apply (cancel_epi (cokernel.π (relation a b))).mp
      apply biprod.hom_ext'
      · simp [comparison, freeArrow, projection, q, Category.assoc]
        have hr : inv a ≫ relation a b = biprod.inl + (inv a ≫ b) ≫ biprod.inr := by
          apply biprod.hom_ext <;> simp [relation, Preadditive.add_comp]
        have h : biprod.inl ≫ projection a b +
            (inv a ≫ b) ≫ biprod.inr ≫ projection a b = 0 := by
          rw [← Category.assoc, ← Preadditive.add_comp, ← hr]
          simp [projection]
        simpa [projection, Preadditive.neg_comp, Category.assoc] using
          (eq_neg_of_add_eq_zero_left h).symm
      · simp [comparison, freeArrow, projection, q, Category.assoc]
    inv_hom_id := by
      simp [comparison, freeArrow, projection, q, Category.assoc] }
  refine ⟨e, ?_, ?_⟩
  · simp only [e, comparison, projection, cokernel.π_desc]
    apply biprod.hom_ext' <;> simp [q, Preadditive.comp_sub]
  · exact e.inv_hom_id

/-- An epimorphic geometric presentation with exactly the specified kernel
identifies its actual target with this quotient, preserving the whole arrow.
Take N to be Conormal.sheaf of the immersion, rather than an abstract class.
Source: Hartshorne, II.5 and II.8; Fulton, §B.7.
Concrete instance: Checks.identification_positive. -/
theorem identification_aux (a : L ⟶ A) (b : L ⟶ E)
    (q : A ⊞ E ⟶ N) (h : relation a b ≫ q = 0) [Epi q]
    (hker : (ShortComplex.mk (relation a b) q h).Exact) :
    IsIso (comparison a b q h) := by
  letI : Mono (comparison a b q h) := hker.mono_cokernelDesc
  letI : Epi (comparison a b q h) := epi_of_epi_fac
    (show projection a b ≫ comparison a b q h = q from cokernel.π_desc _ _ _)
  exact isIso_of_mono_of_epi _

end HodgeLean.Foundations.NormalPresentation
