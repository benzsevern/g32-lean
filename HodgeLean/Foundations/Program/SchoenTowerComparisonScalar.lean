import HodgeLean.Foundations.Program.SchoenTowerFiniteLocalComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

theorem s2v_constantToIdentityCoverPresheaf_scalar (X : TopCat.{0}) (z : ℂ) :
    (Functor.const (Opens X)ᵒᵖ).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)) ≫
      s2v_constantToIdentityCoverPresheaf X =
    s2v_constantToIdentityCoverPresheaf X ≫ s2c_coverPresheafScalar (𝟙 X) z := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  apply LocallyConstant.ext
  intro x
  rfl

theorem s2v_constantIdentityCoverIso_scalar (X : TopCat.{0}) (z : ℂ) :
    (TopCat.Sheaf.constantFunctor X).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)) ≫
      (s2v_constantIdentityCoverIso X).hom =
    (s2v_constantIdentityCoverIso X).hom ≫
      (⟨s2c_coverPresheafScalar (𝟙 X) z⟩ :
        (⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩ :
          TopCat.Sheaf AddCommGrpCat.{0} X) ⟶ _) := by
  let J := Opens.grothendieckTopology X
  let S := presheafToSheaf J AddCommGrpCat.{0}
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  let q : L ⟶ L := ⟨s2c_coverPresheafScalar (𝟙 X) z⟩
  let c := (TopCat.Sheaf.constantFunctor X).map
    (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))
  let η := s2v_constantToIdentityCoverPresheaf X
  let ε := (sheafificationAdjunction J AddCommGrpCat.{0}).counit
  have hη : c ≫ S.map η = S.map η ≫ S.map q.hom := by
    change S.map ((Functor.const (Opens X)ᵒᵖ).map
      (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))) ≫ S.map η = _
    rw [← S.map_comp, ← S.map_comp]
    exact congrArg S.map (s2v_constantToIdentityCoverPresheaf_scalar X z)
  have hε : S.map q.hom ≫ ε.app L = ε.app L ≫ q := ε.naturality q
  change c ≫ (S.map η ≫ ε.app L) = (S.map η ≫ ε.app L) ≫ q
  rw [← Category.assoc, hη, Category.assoc, hε, Category.assoc]

theorem s2v_coverSheaf_pushforwardConstantIso_scalar {X E : TopCat.{0}}
    (f : X ⟶ E) (z : ℂ) :
    s2c_coverSheafScalar f z ≫ (s2v_coverSheaf_pushforwardConstantIso f).hom =
      (s2v_coverSheaf_pushforwardConstantIso f).hom ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
          ((TopCat.Sheaf.constantFunctor X).map
            (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))) := by
  let L : TopCat.Sheaf AddCommGrpCat.{0} X :=
    ⟨s2c_coverPresheaf (𝟙 X), s2v_coverPresheaf_isSheaf (𝟙 X)⟩
  let q : L ⟶ L := ⟨s2c_coverPresheafScalar (𝟙 X) z⟩
  let c := (TopCat.Sheaf.constantFunctor X).map
    (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))
  let i := s2v_constantIdentityCoverIso X
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
  let J := Opens.grothendieckTopology E
  let S := presheafToSheaf J AddCommGrpCat.{0}
  let ε := (sheafificationAdjunction J AddCommGrpCat.{0}).counit
  have hi : q ≫ i.inv = i.inv ≫ c := by
    apply i.comp_inv_eq.mpr
    rw [Category.assoc, s2v_constantIdentityCoverIso_scalar X z, i.inv_hom_id_assoc]
  have hε : S.map (P.map q).hom ≫ ε.app (P.obj L) =
      ε.app (P.obj L) ≫ P.map q := ε.naturality (P.map q)
  change S.map (P.map q).hom ≫ (ε.app (P.obj L) ≫ P.map i.inv) =
    (ε.app (P.obj L) ≫ P.map i.inv) ≫ P.map c
  rw [← Category.assoc, hε, Category.assoc, ← P.map_comp, hi, P.map_comp,
    Category.assoc]

theorem s2v_coverSheaf_pushforwardConstantIso_inv_scalar {X E : TopCat.{0}}
    (f : X ⟶ E) (z : ℂ) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map
        ((TopCat.Sheaf.constantFunctor X).map
          (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z))) ≫
      (s2v_coverSheaf_pushforwardConstantIso f).inv =
    (s2v_coverSheaf_pushforwardConstantIso f).inv ≫ s2c_coverSheafScalar f z := by
  let i := s2v_coverSheaf_pushforwardConstantIso f
  apply i.comp_inv_eq.mpr
  rw [Category.assoc, s2v_coverSheaf_pushforwardConstantIso_scalar f z,
    i.inv_hom_id_assoc]

theorem s2v_actualFiniteCover_comparison_with_coefficients
    {W B E : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B)
    (hX : ∀ (x : ComplexPoint (s2b_preimage β j))
      (U : Opens (ComplexPoint (s2b_preimage β j))), x ∈ U →
      ∃ V : Opens (ComplexPoint (s2b_preimage β j)),
        x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) : ∃ c : AlgebraicTopology.Singular.Cohomology ℂ
      (s2c_points.obj (s2b_preimage β j)) n ≃+
        Sheaf.H (s2c_coverSheaf (s2c_points.map (s2b_toExceptional β j))) n,
      ∀ (z : ℂ) v, c (z • v) =
        Sheaf.H.map (s2c_coverSheafScalar (s2c_points.map (s2b_toExceptional β j)) z) n
          (c v) := by
  let F := s2c_points.obj (s2b_preimage β j)
  let f := s2c_points.map (s2b_toExceptional β j)
  let C := (TopCat.Sheaf.constantFunctor F).obj (AddCommGrpCat.of ℂ)
  let P := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj C
  letI : CompactSpace F := s2v_pullback_points_compact β j
  letI : T2Space F := s2v_pullback_points_t2 β j
  have hfin : ∀ y, Set.Finite {x : F | f x = y} := fun y =>
    Set.finite_coe_iff.mp (s2v_preimage_point_fibre_finite β j y)
  obtain ⟨a, ha⟩ := s2v_projective_preimage_singularConstant_equiv β j hX n
  let b := s2v_proper_finiteFibres_cohomologyEquiv f
    (s2v_projective_preimage_projection_proper β j) hfin C n
  let i := s2v_coverSheaf_pushforwardConstantIso f
  let c : Sheaf.H P n ≃+ Sheaf.H (s2c_coverSheaf f) n := {
    toFun := Sheaf.H.map i.inv n
    invFun := Sheaf.H.map i.hom n
    left_inv := by
      intro v
      rw [← Sheaf.H.map_comp_apply, i.inv_hom_id, Sheaf.H.map_id_apply]
    right_inv := by
      intro v
      rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
    map_add' := by intro v w; exact map_add (Sheaf.H.map i.inv n) v w }
  refine ⟨a.trans (b.trans c), ?_⟩
  intro z v
  change Sheaf.H.map i.inv n (b (a (z • v))) =
    Sheaf.H.map (s2c_coverSheafScalar f z) n (Sheaf.H.map i.inv n (b (a v)))
  rw [ha]
  let q : C ⟶ C := fieldScalarSheaf ℂ (s2b_preimage β j) z
  have hb := s2v_proper_finiteFibres_cohomologyEquiv_naturality f
    (s2v_projective_preimage_projection_proper β j) hfin
      q n (a v)
  change b (Sheaf.H.map q n (a v)) =
    Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map q) n (b (a v)) at hb
  change Sheaf.H.map i.inv n (b (Sheaf.H.map q n (a v))) =
    Sheaf.H.map (s2c_coverSheafScalar f z) n (Sheaf.H.map i.inv n (b (a v)))
  rw [hb, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun q => Sheaf.H.map q n (b (a v)))
    (s2v_coverSheaf_pushforwardConstantIso_inv_scalar f z)


end HodgeLean.Foundations.Program
