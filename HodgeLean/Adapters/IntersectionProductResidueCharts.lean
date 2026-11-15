import HodgeLean.Adapters.IntersectionProductConeSeparation
/-! # Residue fields and degrees through affine charts

These lemmas transport prime-quotient fraction fields and residue degrees along
open affine charts.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Order MvPolynomial TensorProduct
namespace HodgeLean.Adapters
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- An open affine chart identifies the scheme residue field with the fraction field of its prime quotient. -/
theorem IntersectionProductScaf_chart_residue_quotient_fractionRing
    {Y : Scheme.{0}} (R : CommRingCat.{0}) (κ : Spec R ⟶ Y)
    [IsOpenImmersion κ] (p : Spec R) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Algebra (R ⧸ p.asIdeal) (Y.residueField (κ p)) :=
      (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
        (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)).toAlgebra
    IsFractionRing (R ⧸ p.asIdeal) (Y.residueField (κ p)) := by
  letI : p.asIdeal.IsPrime := p.isPrime
  letI : Algebra (R ⧸ p.asIdeal) (Y.residueField (κ p)) :=
    (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
      (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)).toAlgebra
  let e : p.asIdeal.ResidueField ≃ₐ[R ⧸ p.asIdeal] Y.residueField (κ p) :=
    { ((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).symm.commRingCatIsoToRingEquiv with
      commutes' := fun r => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e
#print axioms IntersectionProductScaf_chart_residue_quotient_fractionRing

/-- Residue degree is unchanged when a morphism is restricted through compatible open charts. -/
theorem IntersectionProductScaf_degree_open_square
    {U V Y Z : Scheme.{0}} (f : Y ⟶ Z) (g : U ⟶ V)
    (j : U ⟶ Y) (k : V ⟶ Z) [IsOpenImmersion j] [IsOpenImmersion k]
    (h : j ≫ f = g ≫ k) (u : U) : a1p_degree f (j u) = a1p_degree g u := by
  have hj : a1p_degree j u = 1 := a1x_degree_eq_one_of_surjective j u
    (ConcreteCategory.bijective_of_isIso (j.residueFieldMap u)).2
  have hk : a1p_degree k (g u) = 1 := a1x_degree_eq_one_of_surjective k (g u)
    (ConcreteCategory.bijective_of_isIso (k.residueFieldMap (g u))).2
  calc
    _ = a1p_degree (j ≫ f) u := by rw [a1p_degree_comp, hj, mul_one]
    _ = a1p_degree (g ≫ k) u := congrArg (fun q => a1p_degree q u) h
    _ = _ := by rw [a1p_degree_comp, hk, one_mul]
#print axioms IntersectionProductScaf_degree_open_square

/-- Evaluation through an open chart agrees with the quotient fraction-field embedding. -/
theorem IntersectionProductScaf_chart_residue_evaluation
    {Y : Scheme.{0}} (R : CommRingCat.{0}) (κ : Spec R ⟶ Y)
    [IsOpenImmersion κ] (p : Spec R) :
    (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
      (algebraMap R p.asIdeal.ResidueField)) =
      (((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫
        inv (κ.residueFieldMap p)).hom) := by
  change (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso R p).inv ≫ inv (κ.residueFieldMap p)).hom = _
  rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc]
  rfl
#print axioms IntersectionProductScaf_chart_residue_evaluation

/-- A chart over the complex base preserves the scalar map into the scheme residue field. -/
theorem IntersectionProductScaf_chart_residue_scalar
    (Y : Over (Spec ↧ℂ)) (R : CommRingCat.{0}) [Algebra ℂ R]
    (κ : Spec R ⟶ Y.left) [IsOpenImmersion κ]
    (hκ : κ ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (p : Spec R) :
    ((((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
      (algebraMap R p.asIdeal.ResidueField)).comp (algebraMap ℂ R)) =
      (((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫ Y.left.Γevaluation (κ p)).hom) := by
  rw [IntersectionProductScaf_chart_residue_evaluation]
  apply CommRingCat.hom_ext_iff.mp
  change CommRingCat.ofHom (algebraMap ℂ R) ≫ (Scheme.ΓSpecIso R).inv ≫
    (Spec R).Γevaluation p ≫ inv (κ.residueFieldMap p) = _
  apply (cancel_mono (κ.residueFieldMap p)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.Γevaluation_naturality]
  rw [← Category.assoc Y.hom.appTop, ← Scheme.Hom.comp_appTop, hκ]
  exact congrArg (fun f => f ≫ (Spec R).Γevaluation p)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ R)))
#print axioms IntersectionProductScaf_chart_residue_scalar

/-- Chart rigidity gives residue degree one for a scheme morphism whose residue field contains the coordinate ratios. -/
theorem IntersectionProductScaf_degree_one_of_chart_ratio_rigidity
    {ι : Type} {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (R : CommRingCat.{0}) [Algebra ℂ R] (κ : Spec R ⟶ X.left)
    [IsOpenImmersion κ]
    (hκ : κ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (p : Spec R) (hpos : 0 < a1p_degree f.left (κ p))
    (u : ι → R ⧸ p.asIdeal) (v t : R ⧸ p.asIdeal) (hv : v ≠ 0)
    (hu : ∀ i, ∃ k : Y.left.residueField (f.left (κ p)),
      f.left.residueFieldMap (κ p) k =
        (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv
          (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField (u i))) /
        (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv
          (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField v)))
    (ht : ∃ k : Y.left.residueField (f.left (κ p)),
      f.left.residueFieldMap (κ p) k =
        (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv
          (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField t)))
    (hrig : ∀ (E : Type) [Field E] [Algebra ℂ E]
      (φ ψ : (R ⧸ p.asIdeal) →ₐ[ℂ] E), Function.Injective φ → ∀ z : E,
      (∀ i, φ (u i) = z * ψ (u i)) → φ t = ψ t → φ = ψ) :
    a1p_degree f.left (κ p) = 1 := by
  let : p.asIdeal.IsPrime := p.isPrime
  let K := Y.left.residueField (f.left (κ p))
  let L := X.left.residueField (κ p)
  let : Algebra ℂ K :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫ Y.left.Γevaluation _).hom.toAlgebra
  let : Algebra ℂ L :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫ X.left.Γevaluation _).hom.toAlgebra
  let : Algebra K L := (f.left.residueFieldMap (κ p)).hom.toAlgebra
  let : Algebra (R ⧸ p.asIdeal) L :=
    (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
      (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)).toAlgebra
  have : IsFractionRing (R ⧸ p.asIdeal) L :=
    IntersectionProductScaf_chart_residue_quotient_fractionRing R κ p
  have : IsScalarTower ℂ K L := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap (κ p) (Y.left.Γevaluation _ (Y.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation _ ((Y.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  have : IsScalarTower ℂ (R ⧸ p.asIdeal) L := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    have h := congrArg (fun q : ℂ →+* L => q c)
      (IntersectionProductScaf_chart_residue_scalar X R κ hκ p)
    exact h.symm
  have : Module.Finite K L := Module.finite_of_finrank_pos hpos
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  exact IntersectionProductScaf_finrank_one_of_ratio_rigidity
    (R ⧸ p.asIdeal) K L u v t hv hu ht hrig
#print axioms IntersectionProductScaf_degree_one_of_chart_ratio_rigidity

open CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra Ring.toIntAlgebra AddCommGroup.toIntModule in
/-- The relative affine chart is over the complex base with its coefficient algebra. -/
theorem IntersectionProductScaf_relative_chart_over
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (j : Fin (a3s_N X + 1)) :
    (a3m_Tκ (a3s_CX X) j ≫ (a3h_e X).inv) ≫ (a3n_T X).hom =
      Spec.map (CommRingCat.ofHom (((a3s_LC X).θ j).comp
        (algebraMap ℂ (MvPolynomial (Fin (a3s_N X + 1)) (Polynomial ℂ))))) := by
  change (a3m_Tκ (a3s_CX X) j ≫ (a3h_e X).inv) ≫ (a3n_T X).hom =
    Spec.map (CommRingCat.ofHom ((a3m_Tθ (a3s_CX X) j).comp
      (algebraMap ℂ (MvPolynomial (Fin (a3s_N X + 1)) (Polynomial ℂ)))))
  rw [← Over.w (a3n_q X), ← a3h_e_fst]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, a3m_Tκ, a3m_prodChart_fst, Category.assoc, a3t_chart_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  change ((a3s_CX X).θ j (MvPolynomial.C c)) ⊗ₜ[ℤ] (1 : a3m_Away1) =
    a3m_Tθ (a3s_CX X) j (MvPolynomial.C (Polynomial.C c))
  simp [a3m_Tθ]
#print axioms IntersectionProductScaf_relative_chart_over

/-- Values on a target open chart lie in the target residue-field image on a compatible refinement. -/
theorem IntersectionProductScaf_residue_image_of_open_factorization
    {W V X Y : Scheme.{0}} (f : X ⟶ Y) (g : W ⟶ X)
    (k : V ⟶ Y) [IsOpenImmersion k] (h : W ⟶ V)
    (he : g ≫ f = h ≫ k) (w : W) (a : V.residueField (h w)) :
    ∃ b : Y.residueField (f (g w)),
      g.residueFieldMap w (f.residueFieldMap (g w) b) = h.residueFieldMap w a := by
  let e := Y.residueFieldCongr (congrArg (fun q : W ⟶ Y => q w) he)
  refine ⟨e.inv ((inv (k.residueFieldMap (h w))) a), ?_⟩
  have hr := Scheme.Hom.residueFieldMap_congr he w
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hr
  have hh := congrArg (fun q => q (e.inv ((inv (k.residueFieldMap (h w))) a))) hr
  change g.residueFieldMap w (f.residueFieldMap (g w) _) =
    h.residueFieldMap w (k.residueFieldMap (h w) (e.hom (e.inv _))) at hh
  simpa only [Iso.inv_hom_id_apply, IsIso.inv_hom_id_apply] using hh
#print axioms IntersectionProductScaf_residue_image_of_open_factorization

/-- Residue evaluation through an open chart is natural under a ring map refining that chart. -/
theorem IntersectionProductScaf_chart_residue_evaluation_pullback
    {Y : Scheme.{0}} (R A : CommRingCat.{0}) (κ : Spec R ⟶ Y)
    [IsOpenImmersion κ] (φ : R ⟶ A) (q : Spec A) (r : R) :
    (Spec.map φ ≫ κ).residueFieldMap q
      (((asIso (κ.residueFieldMap (Spec.map φ q))) ≪≫
        (Scheme.Spec.residueFieldIso R (Spec.map φ q))).inv
        (algebraMap R (Spec.map φ q).asIdeal.ResidueField r)) =
      ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation q) (φ r) := by
  have he := congrArg (fun h : R →+* Y.residueField (κ (Spec.map φ q)) => h r)
    (IntersectionProductScaf_chart_residue_evaluation R κ (Spec.map φ q))
  rw [Scheme.residueFieldMap_comp]
  change (Spec.map φ).residueFieldMap q (κ.residueFieldMap _ _) = _
  erw [he]
  simp only [CommRingCat.comp_apply, IsIso.inv_hom_id_apply]
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation _ ≫
    (Spec.map φ).residueFieldMap q) r = _
  rw [Scheme.Γevaluation_naturality, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl
#print axioms IntersectionProductScaf_chart_residue_evaluation_pullback

/-- Homogeneous scaling on a common affine refinement gives degree one from source-chart rigidity. -/
theorem IntersectionProductScaf_degree_one_of_refined_chart_rigidity
    {ι : Type} {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    (R S A : CommRingCat.{0}) [Algebra ℂ R]
    (κ : Spec R ⟶ X.left) (κT : Spec S ⟶ Y.left)
    [IsOpenImmersion κ] [IsOpenImmersion κT]
    (hκ : κ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (α : R ⟶ A) (β : S ⟶ A)
    (he : (Spec.map α ≫ κ) ≫ f.left = Spec.map β ≫ κT)
    (q : Spec A) (hpos : 0 < a1p_degree f.left (κ (Spec.map α q)))
    (u : ι → R) (v t : R) (w : ι → S) (t' : S)
    (hv : α v ∉ q.asIdeal)
    (hu : ∀ i, α (u i) = α v * β (w i)) (ht : α t = β t')
    (hrig : ∀ (E : Type) [Field E] [Algebra ℂ E]
      (φ ψ : (R ⧸ (Spec.map α q).asIdeal) →ₐ[ℂ] E),
      Function.Injective φ → ∀ z : E,
      (∀ i, φ (Ideal.Quotient.mk _ (u i)) = z * ψ (Ideal.Quotient.mk _ (u i))) →
      φ (Ideal.Quotient.mk _ t) = ψ (Ideal.Quotient.mk _ t) → φ = ψ) :
    a1p_degree f.left (κ (Spec.map α q)) = 1 := by
  let p := Spec.map α q
  let e : R →+* X.left.residueField (κ p) :=
    (((asIso (κ.residueFieldMap p)) ≪≫ (Scheme.Spec.residueFieldIso R p)).inv.hom.comp
      (algebraMap R p.asIdeal.ResidueField))
  let δ := (Spec.map α ≫ κ).residueFieldMap q
  let ε := ((Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation q).hom
  have heval (r : R) : δ (e r) = ε (α r) :=
    IntersectionProductScaf_chart_residue_evaluation_pullback R A κ α q r
  have hβ (s : S) : (Spec.map β).residueFieldMap q
      (((Scheme.ΓSpecIso S).inv ≫ (Spec S).Γevaluation (Spec.map β q)) s) = ε (β s) := by
    change ((Scheme.ΓSpecIso S).inv ≫ (Spec S).Γevaluation _ ≫
      (Spec.map β).residueFieldMap q) s = _
    rw [Scheme.Γevaluation_naturality, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  have hvε : ε (α v) ≠ 0 := by
    have h := congrArg (fun m => m (α v)) (Scheme.Spec.algebraMap_residueFieldIso_inv A q)
    change (Scheme.Spec.residueFieldIso A q).inv (algebraMap A q.asIdeal.ResidueField (α v)) =
      ε (α v) at h
    rw [← h]
    exact (map_ne_zero _).mpr (Ideal.algebraMap_residueField_eq_zero.not.mpr hv)
  apply IntersectionProductScaf_degree_one_of_chart_ratio_rigidity f R κ hκ p hpos
    (fun i => Ideal.Quotient.mk p.asIdeal (u i)) (Ideal.Quotient.mk p.asIdeal v)
    (Ideal.Quotient.mk p.asIdeal t) ?_ ?_ ?_ hrig
  · intro hz
    have hm : v ∈ p.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hv hm
  · intro i
    obtain ⟨b, hb⟩ := IntersectionProductScaf_residue_image_of_open_factorization
      f.left (Spec.map α ≫ κ) κT (Spec.map β) he q
      (((Scheme.ΓSpecIso S).inv ≫ (Spec S).Γevaluation (Spec.map β q)) (w i))
    refine ⟨b, δ.hom.injective ?_⟩
    change δ (f.left.residueFieldMap (κ p) b) = δ (e (u i) / e v)
    erw [hb, hβ, map_div₀, heval, heval]
    apply (eq_div_iff hvε).mpr
    rw [hu, map_mul, mul_comm]
  · obtain ⟨b, hb⟩ := IntersectionProductScaf_residue_image_of_open_factorization
      f.left (Spec.map α ≫ κ) κT (Spec.map β) he q
      (((Scheme.ΓSpecIso S).inv ≫ (Spec S).Γevaluation (Spec.map β q)) t')
    refine ⟨b, δ.hom.injective ?_⟩
    change δ (f.left.residueFieldMap (κ p) b) = δ (e t)
    erw [hb, hβ, heval, ht]
#print axioms IntersectionProductScaf_degree_one_of_refined_chart_rigidity

end HodgeLean.Adapters
