import HodgeLean.Foundations.Program.SchoenTowerVanishingSuppliers
import HodgeLean.Foundations.Program.SchoenTowerComparison
import HodgeLean.Foundations.Program.SchoenTowerDeckOrder
import HodgeLean.Foundations.Program.SchoenTowerFiniteDerivedComparison
import HodgeLean.Foundations.Program.SchoenTowerFibreTopology
import HodgeLean.Foundations.Program.SchoenTowerProperDescent
import HodgeLean.Foundations.Program.SchoenTowerActionLemmas
import HodgeLean.Foundations.Program.SchoenTowerFiniteExtension
import HodgeLean.Foundations.Program.SchoenTowerPullbackTopology
import HodgeLean.Foundations.Program.SchoenTowerFinitePointFibres
import HodgeLean.Foundations.Program.SchoenTowerProjectorSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import HodgeLean.Foundations.SegreProjective

/-! # Fibre restriction and proper descent
Implication from a finite cover and a proper centre projection to the fibre
comparison and the descent of all-degree character vanishing.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program.V3BaseChange

private def s2v_sheafPullbackCompIso {X Y Z : TopCat.{0}}
    (p : X ⟶ Y) (q : Y ⟶ Z) :
    TopCat.Sheaf.pullback AddCommGrpCat.{0} q ⋙
      TopCat.Sheaf.pullback AddCommGrpCat.{0} p ≅
        TopCat.Sheaf.pullback AddCommGrpCat.{0} (p ≫ q) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} q).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p)).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} (p ≫ q))

private def s2v_sheafPushforwardEquivalence {X Y : TopCat.{0}} (u : X ≅ Y) :
    TopCat.Sheaf AddCommGrpCat.{0} X ≌ TopCat.Sheaf AddCommGrpCat.{0} Y :=
  CategoryTheory.Equivalence.mk
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.hom)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.inv)
    ((show TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.hom ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.inv ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{0} (u.hom ≫ u.inv) from Iso.refl _) ≪≫
      (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{0}) u.hom_inv_id)) ≪≫ (Iso.refl _)).symm
    ((show TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.inv ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{0} u.hom ≅
      TopCat.Sheaf.pushforward AddCommGrpCat.{0} (u.inv ≫ u.hom) from Iso.refl _) ≪≫
      (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{0}) u.inv_hom_id)) ≪≫ (Iso.refl _))

private def s2v_sheafPullbackHomeomorphCohomologyEquiv {X Y : TopCat.{0}} [T2Space X] [LocallyCompactSpace X]
    (u : X ≃ₜ Y) (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (n : ℕ) :
    Sheaf.H.{0,0,0,0} ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (TopCat.isoOfHomeo u).hom).obj F) n ≃+
      Sheaf.H.{0,0,0,0} F n := by
  let p := (TopCat.isoOfHomeo u).hom
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} p
  let R := TopCat.Sheaf.pushforward AddCommGrpCat.{0} p
  letI : R.IsEquivalence := (s2v_sheafPushforwardEquivalence (TopCat.isoOfHomeo u)).isEquivalence_functor
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} p
  let i : F ≅ R.obj (L.obj F) := asIso (adj.unit.app F)
  let hfin : ∀ y : Y, Set.Finite {x : X | p x = y} := fun y =>
    Set.Subsingleton.finite (by intro a ha b hb; exact u.injective (ha.trans hb.symm))
  exact (s2v_proper_finiteFibres_cohomologyEquiv p u.isProperMap hfin (L.obj F) n).trans
    (((Sheaf.functorH (Opens.grothendieckTopology Y) n).mapIso i).symm.addCommGroupIsoToAddEquiv)

private theorem s2v_projective_schemeFibre_descent (E K : Over (Spec ↧ℂ))
    [IsProjective E.hom] [IsProjective K.hom] (p : E ⟶ K)
    (F : TopCat.Sheaf AddCommGrpCat (s2c_points.obj E))
    (hF : ∀ (k : ComplexPoint K) (n : ℕ), Subsingleton
      (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s2c_points.map (pullback.fst p k))).obj F) n)) (n : ℕ) :
    Subsingleton (Sheaf.H F n) := by
  apply s2v_projective_sheaf_descent E K p F _ n
  intro k q
  let X := s2c_points.obj (pullback p k)
  let Y := TopCat.of {x : ComplexPoint E // Point.map p x = k}
  let u : X ≃ₜ Y := s2v_separatedPointFibreHomeomorph p k
  let a : X ⟶ Y := (TopCat.isoOfHomeo u).hom
  let b : Y ⟶ s2c_points.obj E := s3_fibreInclusion (s2c_points.map p) k
  have hab : a ≫ b = s2c_points.map (pullback.fst p k) := by ext; rfl
  let G := (TopCat.Sheaf.pullback AddCommGrpCat b).obj F
  let : T2Space (ComplexPoint E) := inferInstance
  let : T2Space X := (s2v_pointFibreEquiv_isEmbedding p k).t2Space
  let : CompactSpace X := s2v_schemeFibre_compact p k
  let i : (TopCat.Sheaf.pullback AddCommGrpCat a).obj G ≅
      (TopCat.Sheaf.pullback AddCommGrpCat (s2c_points.map (pullback.fst p k))).obj F :=
    (s2v_sheafPullbackCompIso a b).app F ≪≫
      (eqToIso (congrArg (fun t => (TopCat.Sheaf.pullback AddCommGrpCat t).obj F) hab))
  let e : Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat a).obj G) q ≃+
      Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat (s2c_points.map (pullback.fst p k))).obj F) q :=
    ((Sheaf.functorH (Opens.grothendieckTopology X) q).mapIso i).addCommGroupIsoToAddEquiv
  let := hF k q
  let : Subsingleton (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat a).obj G) q) :=
    e.injective.subsingleton
  exact (s2v_sheafPullbackHomeomorphCohomologyEquiv u G q).symm.injective.subsingleton
private def s2v_coverPresheafSquareMap {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) :
    s2c_coverPresheaf f ⟶
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).obj (s2c_coverPresheaf f') where
  app U := by
    exact AddCommGrpCat.ofHom (LocallyConstant.comapAddMonoidHom (Z := ℂ)
    (show C({x : X' // g (f' x) ∈ U.unop}, {x : X // f x ∈ U.unop}) from
      ⟨fun x => ⟨h x.val, by
          have he : f (h x.val) = g (f' x.val) := congrArg (fun t : X' ⟶ E => t x.val) hs
          rw [he]; exact x.property⟩,
        by fun_prop⟩))
  naturality := by
    intro U V i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply LocallyConstant.ext
    intro x
    rfl
private theorem s2v_coverPresheafSquareMap_scalar {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (z : ℂ) :
    s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (s2c_coverPresheafScalar f' z) =
      s2c_coverPresheafScalar f z ≫ s2v_coverPresheafSquareMap f f' h g hs := by
  ext s
  rfl
private theorem s2v_coverPresheafSquareMap_deck {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (d : X ⟶ X) (d' : X' ⟶ X')
    (hd : d ≫ f = f) (hd' : d' ≫ f' = f') (heq : h ≫ d = d' ≫ h) :
    s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (s2c_coverPresheafDeck f' d' hd') =
      s2c_coverPresheafDeck f d hd ≫ s2v_coverPresheafSquareMap f f' h g hs := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change LocallyConstant {x : X // f x ∈ U.unop} ℂ at s
  apply LocallyConstant.ext
  intro x
  change s ⟨h (d' x.val), _⟩ = s ⟨d (h x.val), _⟩
  congr 1
  exact Subtype.ext (congrArg (fun t : X' ⟶ X => t x.val) heq).symm
private def s2v_coverSheafSquareMap {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) :
    s2c_coverSheaf f ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj (s2c_coverSheaf f') := by
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj (s2c_coverSheaf f')
  let η := s2v_coverPresheafSquareMap f f' h g hs ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
      (toSheafify (Opens.grothendieckTopology E') (s2c_coverPresheaf f'))
  exact ⟨sheafifyLift (Opens.grothendieckTopology E) η T.property⟩
private theorem s2v_coverSheafSquareMap_unit {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) :
    toSheafify (Opens.grothendieckTopology E) (s2c_coverPresheaf f) ≫
      (s2v_coverSheafSquareMap f f' h g hs).hom =
    s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (toSheafify (Opens.grothendieckTopology E') (s2c_coverPresheaf f')) :=
  toSheafify_sheafifyLift _ _ _
private theorem s2v_coverSheafSquareMap_naturality {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g)
    (a : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f)
    (b : s2c_coverPresheaf f' ⟶ s2c_coverPresheaf f')
    (hab : s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map b =
        a ≫ s2v_coverPresheafSquareMap f f' h g hs) :
    s2v_coverSheafSquareMap f f' h g hs ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).map
        ((presheafToSheaf (Opens.grothendieckTopology E') AddCommGrpCat.{0}).map b) =
      ((presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat.{0}).map a) ≫
        s2v_coverSheafSquareMap f f' h g hs := by
  let J := Opens.grothendieckTopology E
  let J' := Opens.grothendieckTopology E'
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  let T := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} g).obj (s2c_coverSheaf f')
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ T.property
  change toSheafify J (s2c_coverPresheaf f) ≫
      (s2v_coverSheafSquareMap f f' h g hs).hom ≫ P.map (sheafifyMap J' b) =
    toSheafify J (s2c_coverPresheaf f) ≫ sheafifyMap J a ≫
      (s2v_coverSheafSquareMap f f' h g hs).hom
  rw [← Category.assoc, s2v_coverSheafSquareMap_unit, Category.assoc,
    ← P.map_comp, ← toSheafify_naturality, P.map_comp, ← Category.assoc, hab]
  rw [Category.assoc, ← s2v_coverSheafSquareMap_unit,
    ← Category.assoc, toSheafify_naturality, Category.assoc]
private def s2v_actualCoverSheafFibreMap {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0}
      (s2c_points.map (pullback.fst p k))).obj
        (s2c_coverSheaf (s2c_points.map (s2b_toExceptional β j))) ⟶
      s2c_coverSheaf (s2c_points.map (s2c_coveringFibreProjection β j p k)) := by
  let g := s2c_points.map (pullback.fst p k)
  let f := s2c_points.map (s2b_toExceptional β j)
  let f' := s2c_points.map (s2c_coveringFibreProjection β j p k)
  let h := s2c_points.map (pullback.fst (s2b_toExceptional β j ≫ p) k)
  have hs : h ≫ f = f' ≫ g := by
    dsimp only [h, f, f', g]
    rw [← s2c_points.map_comp, ← s2c_points.map_comp]
    exact congrArg s2c_points.map (pullback.lift_fst _ _ _).symm
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv _ _).symm
    (s2v_coverSheafSquareMap f f' h g hs)
private theorem s2v_coverPresheafSquareMap_stalk_evaluation {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (z : E')
    (v : (s2c_coverPresheaf f).stalk (g z))
    (x : {x : X' // f' x = z}) :
    s2v_coverStalkEvaluation f' z
      ((s2c_coverPresheaf f').stalkPushforward AddCommGrpCat g z
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)).map
          (s2v_coverPresheafSquareMap f f' h g hs) v)) x =
      s2v_coverStalkEvaluation f (g z) v
        ⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans (congrArg g x.property)⟩ := by
  obtain ⟨U, hzU, s, rfl⟩ := (s2c_coverPresheaf f).exists_germ_eq v
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hp := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat g
      (s2c_coverPresheaf f') U z hzU)
    ((s2v_coverPresheafSquareMap f f' h g hs).app (op U) s)
  rw [ConcreteCategory.comp_apply] at hp
  rw [hp]
  erw [s2v_coverStalkEvaluation_germ, s2v_coverStalkEvaluation_germ]
  rfl
private theorem s2v_coverPresheafSquareMap_stalk_isIso {X X' E E' : TopCat.{0}} [T2Space X]
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (hf : IsProperMap f) (hf' : IsProperMap f') (z : E')
    (hfin : Set.Finite {x : X | f x = g z})
    (hq : Function.Bijective (fun x : {x : X' // f' x = z} =>
      (⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans
        (congrArg g x.property)⟩ : {x : X // f x = g z}))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)).map
      (s2v_coverPresheafSquareMap f f' h g hs) ≫
        (s2c_coverPresheaf f').stalkPushforward AddCommGrpCat g z) := by
  let q : {x : X' // f' x = z} ≃ {x : X // f x = g z} :=
    Equiv.ofBijective _ hq
  let σ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)).map
      (s2v_coverPresheafSquareMap f f' h g hs) ≫
        (s2c_coverPresheaf f').stalkPushforward AddCommGrpCat g z
  have he (v : (s2c_coverPresheaf f).stalk (g z)) (x : {x : X' // f' x = z}) :
      s2v_coverStalkEvaluation f' z (σ v) x =
        s2v_coverStalkEvaluation f (g z) v (q x) :=
    s2v_coverPresheafSquareMap_stalk_evaluation f f' h g hs z v x
  apply (ConcreteCategory.isIso_iff_bijective σ).mpr
  constructor
  · intro v w hvw
    apply s2v_coverStalkEvaluation_injective f hf (g z)
    funext x
    obtain ⟨x', rfl⟩ := q.surjective x
    rw [← he v x', ← he w x', hvw]
  · intro w
    obtain ⟨v, hv⟩ := s2v_coverStalkEvaluation_surjective f hf (g z) hfin
      (fun x => s2v_coverStalkEvaluation f' z w (q.symm x))
    refine ⟨v, ?_⟩
    apply s2v_coverStalkEvaluation_injective f' hf' z
    funext x
    rw [he v x, hv]
    exact congrArg (s2v_coverStalkEvaluation f' z w) (q.symm_apply_apply x)
private theorem s2v_sheafPullback_unit_hom {X Y : TopCat.{0}} (g : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.app F).hom =
      s3_pullback_section_map g F := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g
  let B := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g) AddCommGrpCat.{0} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  let α := (TopCat.Sheaf.pullbackIso AddCommGrpCat.{0} g).app F
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  have hc := congrArg (fun t => t.hom) (Adjunction.unit_leftAdjointUniq_hom_app A B F)
  change (A.unit.app F).hom ≫ P.map α.hom.hom = (B.unit.app F).hom at hc
  apply (cancel_mono (P.map α.hom.hom)).mp
  rw [hc]
  dsimp only [s3_pullback_section_map]
  have hi : α.inv.hom ≫ α.hom.hom = 𝟙 _ :=
    congrArg (fun t => t.hom) α.inv_hom_id
  rw [Category.assoc, ← P.map_comp, Category.assoc, hi]
  erw [Category.comp_id]
  dsimp [B, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rfl
private theorem s2v_sheafPullback_mate_stalk {X Y : TopCat.{0}} (g : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (G : TopCat.Sheaf AddCommGrpCat.{0} X)
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{0} g).obj F ⟶ G) (z : X) :
    (s3_pullback_stalk_iso g F z).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} z).map a.hom =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (g z)).map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv F G) a).hom ≫
        G.presheaf.stalkPushforward AddCommGrpCat.{0} g z := by
  let η := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv F G) a
  have hη : s3_pullback_section_map g F ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map a.hom = η.hom := by
    dsimp only [η]
    rw [Adjunction.homEquiv_unit]
    change _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.app F).hom ≫ _
    rw [s2v_sheafPullback_unit_hom]
    rfl
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hzU
  have hu := congrArg (fun t => t.app (op U)) hη
  change (s3_pullback_section_map g F).app (op U) ≫ a.hom.app (op ((Opens.map g).obj U)) =
    η.hom.app (op U) at hu
  rw [← Category.assoc, ← s3_pullback_section_map_germ, Category.assoc,
    TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc, hu]
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  erw [TopCat.Presheaf.stalkPushforward_germ]
  rfl
private theorem s2v_stalkPushforward_naturality {X Y : TopCat.{0}} (g : X ⟶ Y)
    {F G : TopCat.Presheaf AddCommGrpCat.{0} X} (a : F ⟶ G) (z : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (g z)).map
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map a) ≫
        G.stalkPushforward AddCommGrpCat.{0} g z =
      F.stalkPushforward AddCommGrpCat.{0} g z ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} z).map a := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hzU
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    TopCat.Presheaf.stalkPushforward_germ]
  rw [← Category.assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl
private theorem s2v_coverSheafSquareMap_stalk_isIso {X X' E E' : TopCat.{0}} [T2Space X]
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (hf : IsProperMap f) (hf' : IsProperMap f') (z : E')
    (hfin : Set.Finite {x : X | f x = g z})
    (hq : Function.Bijective (fun x : {x : X' // f' x = z} =>
      (⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans
        (congrArg g x.property)⟩ : {x : X // f x = g z}))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)).map
      ((s2v_coverSheafSquareMap f f' h g hs).hom) ≫
        (s2c_coverSheaf f').presheaf.stalkPushforward AddCommGrpCat g z)  := by
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat z
  let τ := toSheafify (Opens.grothendieckTopology E) (s2c_coverPresheaf f)
  let τ' := toSheafify (Opens.grothendieckTopology E') (s2c_coverPresheaf f')
  let a := s2v_coverSheafSquareMap f f' h g hs
  let σ := S.map a.hom ≫ (s2c_coverSheaf f').presheaf.stalkPushforward AddCommGrpCat g z
  let σ₀ := S.map (s2v_coverPresheafSquareMap f f' h g hs) ≫
    (s2c_coverPresheaf f').stalkPushforward AddCommGrpCat g z
  have hc : S.map τ ≫ σ = σ₀ ≫ T.map τ' := by
    dsimp only [σ, σ₀]
    rw [← Category.assoc, ← S.map_comp, s2v_coverSheafSquareMap_unit,
      S.map_comp, Category.assoc]
    erw [s2v_stalkPushforward_naturality]
    exact (Category.assoc (S.map (s2v_coverPresheafSquareMap f f' h g hs))
      ((s2c_coverPresheaf f').stalkPushforward AddCommGrpCat g z) (T.map τ')).symm
  let : IsIso (S.map τ) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (g z) AddCommGrpCat _
  let : IsIso (T.map τ') :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z AddCommGrpCat _
  let : IsIso σ₀ := s2v_coverPresheafSquareMap_stalk_isIso f f' h g hs hf hf' z hfin hq
  have : IsIso (S.map τ ≫ σ) := by rw [hc]; infer_instance
  exact IsIso.of_isIso_comp_left (S.map τ) σ
private theorem s2v_coverSheafSquareMap_pullback_isIso {X X' E E' : TopCat.{0}} [T2Space X]
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (hf : IsProperMap f) (hf' : IsProperMap f')
    (hfin : ∀ z : E', Set.Finite {x : X | f x = g z})
    (hq : ∀ z : E', Function.Bijective (fun x : {x : X' // f' x = z} =>
      (⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans
        (congrArg g x.property)⟩ : {x : X // f x = g z}))) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv
      (s2c_coverSheaf f) (s2c_coverSheaf f')).symm
        (s2v_coverSheafSquareMap f f' h g hs)) := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g
  let a := (adj.homEquiv (s2c_coverSheaf f) (s2c_coverSheaf f')).symm
    (s2v_coverSheafSquareMap f f' h g hs)
  have (z : E') : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map a.hom) := by
    have he := s2v_sheafPullback_mate_stalk g (s2c_coverSheaf f) (s2c_coverSheaf f') a z
    dsimp only [a] at he
    rw [Equiv.apply_symm_apply] at he
    let e := s3_pullback_stalk_iso g (s2c_coverSheaf f) z
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (g z)).map
        (s2v_coverSheafSquareMap f f' h g hs).hom ≫
          (s2c_coverSheaf f').presheaf.stalkPushforward AddCommGrpCat g z) :=
      s2v_coverSheafSquareMap_stalk_isIso f f' h g hs hf hf' z (hfin z) (hq z)
    have : IsIso (e.hom ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map a.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso a
private theorem s2v_actualCoveringFibre_bijective {W B E K : Over (Spec ↧ℂ)} [IsSeparated K.hom]
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let f' := s2c_points.map (s2c_coveringFibreProjection β j p k)
    let h := s2c_points.map (pullback.fst (s2b_toExceptional β j ≫ p) k)
    let g := s2c_points.map (pullback.fst p k)
    ∀ (hs : h ≫ f = f' ≫ g) (z : ComplexPoint (pullback p k)),
      Function.Bijective (fun x : {x : ComplexPoint (s2b_coveringFibre β j p k) // f' x = z} =>
        (⟨h x.val, (congrArg (fun t => t x.val) hs).trans
          (congrArg g x.property)⟩ : {x : ComplexPoint (s2b_preimage β j) // f x = g z})) := by
  dsimp only
  intro hs z
  let f := s2b_toExceptional β j
  let h := pullback.fst (f ≫ p) k
  let g := pullback.fst p k
  let f' := s2c_coveringFibreProjection β j p k
  let : IsClosedImmersion h.left := s2v_schemeFibre_closedImmersion (f ≫ p) k
  let : IsClosedImmersion g.left := s2v_schemeFibre_closedImmersion p k
  have hh : Function.Injective (Point.map h) :=
    (ComplexPoint.isEmbedding_map_of_closedImmersion h).injective
  have hg : Function.Injective (Point.map g) :=
    (ComplexPoint.isEmbedding_map_of_closedImmersion g).injective
  constructor
  · intro x y he
    apply Subtype.ext
    apply hh
    exact congrArg Subtype.val he
  · intro y
    have hy : Point.map f y.val = Point.map g z := y.property
    let v : {x : ComplexPoint (s2b_preimage β j) // Point.map (f ≫ p) x = k} :=
      ⟨y.val, by
        change Point.map p (Point.map f y.val) = k
        rw [hy]
        exact (s2v_pointFibreEquiv p k z).property⟩
    let u := (s2v_pointFibreEquiv (f ≫ p) k).symm v
    have hu : Point.map h u = y.val :=
      congrArg Subtype.val ((s2v_pointFibreEquiv (f ≫ p) k).apply_symm_apply v)
    have hu' : Point.map f' u = z := by
      apply hg
      calc
        Point.map g (Point.map f' u) = Point.map f (Point.map h u) :=
          (congrArg (fun t => t u) hs).symm
        _ = Point.map g z := by rw [hu]; exact hy
    exact ⟨⟨u, hu'⟩, Subtype.ext hu⟩
private theorem s2v_actualCoverSheafFibreMap_isIso {W B E K : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom] [IsProjective K.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    IsIso (s2v_actualCoverSheafFibreMap β j p k) := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let f' := s2c_points.map (s2c_coveringFibreProjection β j p k)
  let h := s2c_points.map (pullback.fst (s2b_toExceptional β j ≫ p) k)
  let g := s2c_points.map (pullback.fst p k)
  have hs : h ≫ f = f' ≫ g := by
    dsimp only [h, f, f', g]
    rw [← s2c_points.map_comp, ← s2c_points.map_comp]
    exact congrArg s2c_points.map (pullback.lift_fst _ _ _).symm
  let : T2Space (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  let : T2Space (s2c_points.obj (s2b_preimage β j)) := s2v_pullback_points_t2 β j
  let : CompactSpace (ComplexPoint (s2b_preimage β j)) := s2v_pullback_points_compact β j
  let : CompactSpace (ComplexPoint (s2b_coveringFibre β j p k)) :=
    s2v_schemeFibre_compact (s2b_toExceptional β j ≫ p) k
  let : T2Space (ComplexPoint (pullback p k)) :=
    (s2v_pointFibreEquiv_isEmbedding p k).t2Space
  have hf' : IsProperMap f' :=
    (Point.continuousMap (s2c_coveringFibreProjection β j p k)).continuous.isProperMap
  have hfin (z : ComplexPoint (pullback p k)) : Set.Finite {x : ComplexPoint (s2b_preimage β j) | f x = g z} := by
    have hFinite : Finite {x : ComplexPoint (s2b_preimage β j) //
        Point.map (s2b_toExceptional β j) x = Point.map (pullback.fst p k) z} :=
      s2v_preimage_point_fibre_finite β j (Point.map (pullback.fst p k) z)
    change Set.Finite {x : ComplexPoint (s2b_preimage β j) |
      Point.map (s2b_toExceptional β j) x = Point.map (pullback.fst p k) z}
    exact Set.finite_coe_iff.mp hFinite
  change IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv
    (s2c_coverSheaf f) (s2c_coverSheaf f')).symm (s2v_coverSheafSquareMap f f' h g hs))
  exact s2v_coverSheafSquareMap_pullback_isIso f f' h g hs
    (s2v_projective_preimage_projection_proper β j) hf' hfin
    (s2v_actualCoveringFibre_bijective β j p k hs)
private theorem s2v_coverSheafSquareMap_pullback_naturality {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g)
    (a : s2c_coverPresheaf f ⟶ s2c_coverPresheaf f)
    (b : s2c_coverPresheaf f' ⟶ s2c_coverPresheaf f')
    (hab : s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map b =
        a ≫ s2v_coverPresheafSquareMap f f' h g hs) :
    let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} g
    let α := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv
      (s2c_coverSheaf f) (s2c_coverSheaf f')).symm (s2v_coverSheafSquareMap f f' h g hs)
    L.map ((presheafToSheaf (Opens.grothendieckTopology E) AddCommGrpCat.{0}).map a) ≫ α =
      α ≫ ((presheafToSheaf (Opens.grothendieckTopology E') AddCommGrpCat.{0}).map b) := by
  dsimp only
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply]
  exact (s2v_coverSheafSquareMap_naturality f f' h g hs a b hab).symm
private theorem s2v_coverPresheafSquareMap_deck_pow {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (d : X ⟶ X) (d' : X' ⟶ X')
    (hd : d ≫ f = f) (hd' : d' ≫ f' = f') (heq : h ≫ d = d' ≫ h) (t : ℕ) :
    s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        ((End.of (s2c_coverPresheafDeck f' d' hd')) ^ t).asHom =
      ((End.of (s2c_coverPresheafDeck f d hd)) ^ t).asHom ≫
        s2v_coverPresheafSquareMap f f' h g hs := by
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  induction t with
  | zero =>
    simp only [pow_zero, End.one_asHom, Category.id_comp]
    erw [P.map_id, Category.comp_id]
  | succ t ih =>
    simp only [pow_succ, End.mul_asHom, Functor.map_comp]
    rw [← Category.assoc, s2v_coverPresheafSquareMap_deck f f' h g hs d d' hd hd' heq,
      Category.assoc, ih, ← Category.assoc]
private theorem s2v_coverPresheafSquareMap_projector {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (d : X ⟶ X) (d' : X' ⟶ X')
    (hd : d ≫ f = f) (hd' : d' ≫ f' = f') (heq : h ≫ d = d' ≫ h)
    (m : ℕ) (ζ : ℂ) :
    s2v_coverPresheafSquareMap f f' h g hs ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map
        (s2v_characterPresheafProjector f' d' hd' m ζ) =
      s2v_characterPresheafProjector f d hd m ζ ≫
        s2v_coverPresheafSquareMap f f' h g hs := by
  let P := TopCat.Presheaf.pushforward AddCommGrpCat.{0} g
  let : P.Additive := ⟨by intros; rfl⟩
  change _ ≫ P.map _ = _
  unfold s2v_characterPresheafProjector
  rw [P.map_sum]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro t ht
  rw [P.map_comp, ← Category.assoc, s2v_coverPresheafSquareMap_scalar,
    Category.assoc, s2v_coverPresheafSquareMap_deck_pow f f' h g hs d d' hd hd' heq,
    ← Category.assoc]
private theorem s2v_coverSheafSquareMap_pullback_projector {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (d : X ⟶ X) (d' : X' ⟶ X')
    (hd : d ≫ f = f) (hd' : d' ≫ f' = f') (heq : h ≫ d = d' ≫ h)
    (m : ℕ) (ζ : ℂ) :
    let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} g
    let α := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv
      (s2c_coverSheaf f) (s2c_coverSheaf f')).symm (s2v_coverSheafSquareMap f f' h g hs)
    L.map (s2c_characterProjector f d hd m ζ) ≫ α =
      α ≫ s2c_characterProjector f' d' hd' m ζ := by
  have hc := s2v_coverSheafSquareMap_pullback_naturality f f' h g hs
    (s2v_characterPresheafProjector f d hd m ζ)
    (s2v_characterPresheafProjector f' d' hd' m ζ)
    (s2v_coverPresheafSquareMap_projector f f' h g hs d d' hd hd' heq m ζ)
  dsimp only at hc ⊢
  simpa only [s2v_characterProjector_map_presheaf] using hc
private def s2v_imageTransportIso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (a : A ⟶ A) (b : B ⟶ B) (α : L.obj A ⟶ B) [IsIso α]
    (h : L.map a ≫ α = α ≫ b) : L.obj (image a) ≅ image b :=
  (PreservesImage.iso L a).symm ≪≫ image.compIso (L.map a) α ≪≫
    image.eqToIso h ≪≫ asIso (image.preComp α b)
private def s2v_actualCharacterSheafFibreIso {W B E K : Over (Spec ↧ℂ)}
    [IsProjective W.hom] [IsProjective B.hom] [IsProjective E.hom] [IsProjective K.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (k : ComplexPoint K)
    (hδ : s2c_points.map (s2b_preimageDeck β j d hd) ≫
      s2c_points.map (s2b_toExceptional β j) = s2c_points.map (s2b_toExceptional β j))
    (hδ' : s2c_points.map (s2c_coveringFibreDeck β j p d hd k) ≫
      s2c_points.map (s2c_coveringFibreProjection β j p k) =
        s2c_points.map (s2c_coveringFibreProjection β j p k)) (m : ℕ) (ζ : ℂ) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} (s2c_points.map (pullback.fst p k))).obj
      (s2c_characterSheaf (s2c_points.map (s2b_toExceptional β j))
        (s2c_points.map (s2b_preimageDeck β j d hd)) hδ m ζ) ≅
      s2c_characterSheaf (s2c_points.map (s2c_coveringFibreProjection β j p k))
        (s2c_points.map (s2c_coveringFibreDeck β j p d hd k)) hδ' m ζ := by
  let f := s2c_points.map (s2b_toExceptional β j)
  let f' := s2c_points.map (s2c_coveringFibreProjection β j p k)
  let h := s2c_points.map (pullback.fst (s2b_toExceptional β j ≫ p) k)
  let g := s2c_points.map (pullback.fst p k)
  let δ := s2c_points.map (s2b_preimageDeck β j d hd)
  let δ' := s2c_points.map (s2c_coveringFibreDeck β j p d hd k)
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} g
  let α := s2v_actualCoverSheafFibreMap β j p k
  let : IsIso α := s2v_actualCoverSheafFibreMap_isIso β j p k
  let : PreservesFiniteLimits L := s3_pullback_preservesFiniteLimits g
  have hs : h ≫ f = f' ≫ g := by
    dsimp only [h, f, f', g]
    rw [← s2c_points.map_comp, ← s2c_points.map_comp]
    exact congrArg s2c_points.map (pullback.lift_fst _ _ _).symm
  have heq : h ≫ δ = δ' ≫ h := by
    dsimp only [h, δ, δ']
    rw [← s2c_points.map_comp, ← s2c_points.map_comp]
    exact congrArg s2c_points.map (pullback.lift_fst _ _ _).symm
  have hc := s2v_coverSheafSquareMap_pullback_projector f f' h g hs δ δ' hδ hδ' heq m ζ
  dsimp only at hc
  change L.map (s2c_characterProjector f δ hδ m ζ) ≫ α =
    α ≫ s2c_characterProjector f' δ' hδ' m ζ at hc
  exact s2v_imageTransportIso L (s2c_characterProjector f δ hδ m ζ)
    (s2c_characterProjector f' δ' hδ' m ζ) α hc
private theorem s2v_coveringFibreProjection_isPullback {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    IsPullback (pullback.fst (s2b_toExceptional β j ≫ p) k)
      (s2c_coveringFibreProjection β j p k) (s2b_toExceptional β j) (pullback.fst p k) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p k) (v₂₂ := p) (h₃₁ := k) ?_
    (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback p k)
  rw [s2c_coveringFibreProjection, pullback.lift_snd]
  exact IsPullback.of_hasPullback (s2b_toExceptional β j ≫ p) k
private theorem s2v_coveringFibreProjection_finite {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) (p : E ⟶ K) (k : ComplexPoint K) :
    IsFinite (s2c_coveringFibreProjection β j p k).left := by
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    ((s2v_coveringFibreProjection_isPullback β j p k).map (Over.forget _))
    (s2v_preimage_projection_finite β j)
private def s2v_characterSheafSquarePullbackIso {X X' E E' : TopCat.{0}} [T2Space X]
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    (hs : h ≫ f = f' ≫ g) (hf : IsProperMap f) (hf' : IsProperMap f')
    (hfin : ∀ z : E', Set.Finite {x : X | f x = g z})
    (hq : ∀ z : E', Function.Bijective (fun x : {x : X' // f' x = z} =>
      (⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans
        (congrArg g x.property)⟩ : {x : X // f x = g z})))
    (d : X ⟶ X) (d' : X' ⟶ X') (hd : d ≫ f = f) (hd' : d' ≫ f' = f')
    (heq : h ≫ d = d' ≫ h) (m : ℕ) (ζ : ℂ) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} g).obj (s2c_characterSheaf f d hd m ζ) ≅
      s2c_characterSheaf f' d' hd' m ζ := by
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{0} g
  let α := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).homEquiv
    (s2c_coverSheaf f) (s2c_coverSheaf f')).symm (s2v_coverSheafSquareMap f f' h g hs)
  let : IsIso α := s2v_coverSheafSquareMap_pullback_isIso f f' h g hs hf hf' hfin hq
  let : PreservesFiniteLimits L := s3_pullback_preservesFiniteLimits g
  have hc := s2v_coverSheafSquareMap_pullback_projector f f' h g hs d d' hd hd' heq m ζ
  dsimp only at hc
  exact s2v_imageTransportIso L (s2c_characterProjector f d hd m ζ)
    (s2c_characterProjector f' d' hd' m ζ) α hc
private theorem s2v_pointFibre_bijective_of_isIso {X X' E E' : TopCat.{0}}
    (f : X ⟶ E) (f' : X' ⟶ E') (h : X' ⟶ X) (g : E' ⟶ E)
    [IsIso h] [IsIso g] (hs : h ≫ f = f' ≫ g) (z : E') :
    Function.Bijective (fun x : {x : X' // f' x = z} =>
      (⟨h x.val, (congrArg (fun t : X' ⟶ E => t x.val) hs).trans
        (congrArg g x.property)⟩ : {x : X // f x = g z})) := by
  have hh := ConcreteCategory.bijective_of_isIso h
  have hg := ConcreteCategory.bijective_of_isIso g
  constructor
  · intro x y he
    apply Subtype.ext
    exact hh.1 (congrArg Subtype.val he)
  · intro y
    obtain ⟨x, hx⟩ := hh.2 y.val
    have hx' : f' x = z := by
      apply hg.1
      calc
        g (f' x) = f (h x) := (congrArg (fun t : X' ⟶ E => t x) hs).symm
        _ = g z := by rw [hx]; exact y.property
    exact ⟨⟨x, hx'⟩, Subtype.ext hx⟩
private def s2v_singularCohomologyIso {X Y : TopCat.{0}} (u : X ≅ Y) (n : ℕ) :
    Cohomology ℂ Y n ≃ₗ[ℂ] Cohomology ℂ X n where
  toLinearMap := cohomologyMap ℂ n u.hom
  invFun := cohomologyMap ℂ n u.inv
  left_inv v := by
    change cohomologyMap ℂ n u.inv (cohomologyMap ℂ n u.hom v) = v
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, u.inv_hom_id,
      cohomologyMap_id, LinearMap.id_apply]
  right_inv v := by
    change cohomologyMap ℂ n u.hom (cohomologyMap ℂ n u.inv v) = v
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, u.hom_inv_id,
      cohomologyMap_id, LinearMap.id_apply]
private def s2v_eigenspaceEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (T : Module.End ℂ V) (S : Module.End ℂ W)
    (he : ∀ v, e (T v) = S (e v)) (ζ : ℂ) :
    Module.End.eigenspace T ζ ≃ₗ[ℂ] Module.End.eigenspace S ζ := by
  refine e.ofSubmodules _ _ ?_
  ext w
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change S (e v) = ζ • e v
    rw [← he, Module.End.mem_eigenspace_iff.mp hv, e.map_smul]
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply e.injective
    rw [he, e.map_smul, e.apply_symm_apply]
    exact Module.End.mem_eigenspace_iff.mp hw
private theorem s2v_finite_cover_character_cohomology (W E : Over (Spec ↧ℂ))
    [IsProjective W.hom] [IsProjective E.hom]
    (β : W ⟶ E) [IsFinite β.left] (d : W ⟶ W) (hd : d ≫ β = β)
    (hδ : s2c_points.map d ≫ s2c_points.map β = s2c_points.map β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ) :
    Nonempty (Sheaf.H (s2c_characterSheaf (s2c_points.map β) (s2c_points.map d) hδ m ζ) n ≃+
      Module.End.eigenspace (cohomologyMap ℂ n (s2c_points.map d)) ζ) := by
  let P := s2b_preimage β (𝟙 E)
  let f := s2c_points.map β
  let f' := s2c_points.map (s2b_toExceptional β (𝟙 E))
  let h := s2c_points.map (pullback.fst β (𝟙 E))
  let g := 𝟙 (s2c_points.obj E)
  let δ := s2c_points.map d
  let δ' := s2c_points.map (s2b_preimageDeck β (𝟙 E) d hd)
  let u : s2c_points.obj P ≅ s2c_points.obj W :=
    s2c_points.mapIso (asIso (pullback.fst β (𝟙 E)))
  let : IsIso h := by dsimp only [h]; infer_instance
  let : T2Space (s2c_points.obj W) := inferInstanceAs (T2Space (ComplexPoint W))
  let : T2Space (s2c_points.obj E) := inferInstanceAs (T2Space (ComplexPoint E))
  let : CompactSpace (s2c_points.obj E) := inferInstanceAs (CompactSpace (ComplexPoint E))
  have hs : h ≫ f = f' ≫ g := by
    rw [Category.comp_id]
    change s2c_points.map (pullback.fst β (𝟙 E)) ≫ s2c_points.map β =
      s2c_points.map (pullback.snd β (𝟙 E))
    rw [← s2c_points.map_comp]
    exact congrArg s2c_points.map (by
      simpa only [Category.comp_id] using (pullback.condition (f := β) (g := 𝟙 E)))
  have heq : h ≫ δ = δ' ≫ h := by
    dsimp only [h, δ, δ']
    rw [← s2c_points.map_comp, ← s2c_points.map_comp]
    exact congrArg s2c_points.map (pullback.lift_fst _ _ _).symm
  have hf : IsProperMap f := (Point.continuousMap β).continuous.isProperMap
  have hfin (z : s2c_points.obj E) : Set.Finite {x : s2c_points.obj W | f x = g z} := by
    have hFinite := s2v_finite_complexPoint_fibre β z
    change Set.Finite {x : ComplexPoint W | Point.map β x = z}
    exact Set.finite_coe_iff.mp hFinite
  obtain ⟨hδ', c, hD, hS, e, hi⟩ :=
    s2d_finite_cover_comparison W E E β (𝟙 E) d hd m hm horder ζ hζ n
  let eChar := s2v_characterSheafSquarePullbackIso f f' h g hs hf
    (s2v_projective_preimage_projection_proper β (𝟙 E)) hfin
    (fun z => s2v_pointFibre_bijective_of_isIso f f' h g hs z)
    δ δ' hδ hδ' heq m ζ
  let eH₀ := s2v_sheafPullbackHomeomorphCohomologyEquiv
    (Homeomorph.refl (s2c_points.obj E)) (s2c_characterSheaf f δ hδ m ζ) n
  let eH : Sheaf.H (s2c_characterSheaf f δ hδ m ζ) n ≃+
      Sheaf.H (s2c_characterSheaf f' δ' hδ' m ζ) n :=
    eH₀.symm.trans (((Sheaf.functorH (Opens.grothendieckTopology (s2c_points.obj E)) n).mapIso
      eChar).addCommGroupIsoToAddEquiv)
  let eS := s2v_singularCohomologyIso u n
  have hc (v : Cohomology ℂ (s2c_points.obj W) n) :
      eS (cohomologyMap ℂ n δ v) = cohomologyMap ℂ n δ' (eS v) := by
    change cohomologyMap ℂ n h (cohomologyMap ℂ n δ v) =
      cohomologyMap ℂ n δ' (cohomologyMap ℂ n h v)
    exact (LinearMap.congr_fun (cohomologyMap_comp ℂ n h δ) v).symm.trans
      ((congrArg (fun q => cohomologyMap ℂ n q v) heq).trans
        (LinearMap.congr_fun (cohomologyMap_comp ℂ n δ' h) v))
  let eV := s2v_eigenspaceEquiv eS (cohomologyMap ℂ n δ) (cohomologyMap ℂ n δ') hc ζ
  exact ⟨eH.trans (e.trans eV.symm.toAddEquiv)⟩
private theorem s2d_fibre_restriction_descent_aux (W B E K : Over (Spec ↧ℂ))
    [IsProjective W.hom] [IsProjective B.hom]
    [IsProjective E.hom] [IsProjective K.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let δ := s2c_points.map (s2b_preimageDeck β j d hd)
    ∃ hδ : δ ≫ f = f,
      (∀ (k : ComplexPoint K) (n : ℕ),
        Nonempty (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
          (s2c_points.map (pullback.fst p k))).obj
            (s2c_characterSheaf f δ hδ m ζ)) n ≃+
          Module.End.eigenspace (AlgebraicTopology.Singular.cohomologyMap ℂ n
            (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))) ζ)) ∧
      ((∀ (k : ComplexPoint K) (n : ℕ)
          (v : AlgebraicTopology.Singular.Cohomology ℂ
            (s2c_points.obj (s2b_coveringFibre β j p k)) n),
          AlgebraicTopology.Singular.cohomologyMap ℂ n
            (s2c_points.map (s2c_coveringFibreDeck β j p d hd k)) v = ζ • v → v = 0) →
        ∀ n : ℕ, Subsingleton (Sheaf.H (s2c_characterSheaf f δ hδ m ζ) n)) := by
  dsimp only
  let f := s2c_points.map (s2b_toExceptional β j)
  let δ := s2c_points.map (s2b_preimageDeck β j d hd)
  let hδ : δ ≫ f = f := s2v_preimageDeck_over_exceptional β j d hd
  have hf : ∀ (k : ComplexPoint K) (n : ℕ),
      Nonempty (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s2c_points.map (pullback.fst p k))).obj
          (s2c_characterSheaf f δ hδ m ζ)) n ≃+
        Module.End.eigenspace (AlgebraicTopology.Singular.cohomologyMap ℂ n
          (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))) ζ) := by
    intro k n
    let W' := s2b_coveringFibre β j p k
    let E' := pullback p k
    let β' := s2c_coveringFibreProjection β j p k
    let d' := s2c_coveringFibreDeck β j p d hd k
    let : IsProjective (s2b_preimage β j).hom := s2v_preimage_projective β j
    let : IsProjective W'.hom := s2v_schemeFibre_projective (s2b_toExceptional β j ≫ p) k
    let : IsProjective E'.hom := s2v_schemeFibre_projective p k
    let : IsFinite β'.left := s2v_coveringFibreProjection_finite β j p k
    have hd' : d' ≫ β' = β' := s2v_coveringFibreDeck_projection β j p d hd k
    have hδ' : s2c_points.map d' ≫ s2c_points.map β' = s2c_points.map β' := by
      rw [← s2c_points.map_comp, hd']
    obtain ⟨e⟩ := s2v_finite_cover_character_cohomology W' E' β' d' hd' hδ'
      m hm (s2v_coveringFibreDeck_order β j p d hd m horder k) ζ hζ n
    let i := s2v_actualCharacterSheafFibreIso β j p d hd k hδ hδ' m ζ
    exact ⟨(((Sheaf.functorH _ n).mapIso i).addCommGroupIsoToAddEquiv).trans e⟩
  refine ⟨hδ, hf, ?_⟩
  intro hv n
  apply s2v_projective_schemeFibre_descent E K p (s2c_characterSheaf f δ hδ m ζ) _ n
  intro k q
  obtain ⟨e⟩ := hf k q
  let T := AlgebraicTopology.Singular.cohomologyMap ℂ q
    (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))
  have hz (v : Module.End.eigenspace T ζ) : v.val = 0 :=
    hv k q v.val (Module.End.mem_eigenspace_iff.mp v.property)
  let : Subsingleton ↥(Module.End.eigenspace T ζ) :=
    ⟨fun v w => Subtype.ext ((hz v).trans (hz w).symm)⟩
  exact e.injective.subsingleton

/-- The finite proper base-change comparison on the literal topological fibre.
The restriction/projector square is a sheaf-library continuation beyond B18 stage four.
Source: G32 v0.16, Lemma 4.3; Hartshorne III.8 and III.11; Iversen VII.
Example: the order-four exponent-two cover restricts to two projective lines.
HC no distance; AV milestone no distance. -/
theorem _root_.HodgeLean.Foundations.Program.s2cv3_fibre_character_comparison_aux
    (W B E K : Over (Spec ↧ℂ))
    [IsProjective W.hom] [IsProjective B.hom]
    [IsProjective E.hom] [IsProjective K.hom]
    (β : W ⟶ B) [IsFinite β.left] (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (hm : 0 < m) (horder : (End.of d) ^ m = 1)
    (k : ComplexPoint K) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (n : ℕ) :
    let f := s2c_points.map (s2b_toExceptional β j)
    let δ := s2c_points.map (s2b_preimageDeck β j d hd)
    let hδ := s2v_preimageDeck_over_exceptional β j d hd
    Nonempty (Sheaf.H ((TopCat.Sheaf.pullback AddCommGrpCat
        (s3_fibreInclusion (s2c_points.map p) k)).obj
        (s2c_characterSheaf f δ hδ m ζ)) n ≃+
      Module.End.eigenspace
        (AlgebraicTopology.Singular.cohomologyMap ℂ n
          (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))) ζ) := by
  dsimp only
  obtain ⟨hδ, hf, _⟩ := s2d_fibre_restriction_descent_aux W B E K β j p d hd m hm horder ζ hζ
  let X := s2c_points.obj (pullback p k)
  let Y := TopCat.of {x : ComplexPoint E // Point.map p x = k}
  let u : X ≃ₜ Y := s2v_separatedPointFibreHomeomorph p k
  let a : X ⟶ Y := (TopCat.isoOfHomeo u).hom
  let b : Y ⟶ s2c_points.obj E := s3_fibreInclusion (s2c_points.map p) k
  let F := s2c_characterSheaf _ _ hδ m ζ
  have hab : a ≫ b = s2c_points.map (pullback.fst p k) := by ext; rfl
  let i : (TopCat.Sheaf.pullback AddCommGrpCat a).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat b).obj F) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat (s2c_points.map (pullback.fst p k))).obj F :=
    (s2v_sheafPullbackCompIso a b).app F ≪≫
      eqToIso (congrArg (fun q => (TopCat.Sheaf.pullback AddCommGrpCat q).obj F) hab)
  letI : T2Space X := (s2v_pointFibreEquiv_isEmbedding p k).t2Space
  letI : CompactSpace X := s2v_schemeFibre_compact p k
  let eH := s2v_sheafPullbackHomeomorphCohomologyEquiv u
    ((TopCat.Sheaf.pullback AddCommGrpCat b).obj F) n
  obtain ⟨e⟩ := hf k n
  exact ⟨eH.symm.trans ((((Sheaf.functorH _ n).mapIso i).addCommGroupIsoToAddEquiv).trans e)⟩

local instance v3SquareBoolTopology : TopologicalSpace Bool := ⊥
local instance v3SquareBoolDiscrete : DiscreteTopology Bool := ⟨rfl⟩
private abbrev squareSpace := TopCat.of Bool
private def flip : squareSpace ⟶ squareSpace :=
  TopCat.ofHom ⟨Bool.not, continuous_of_discreteTopology⟩
private def squareSection : LocallyConstant
    {x : squareSpace // (𝟙 squareSpace) x ∈ (⊤ : Opens squareSpace)} ℂ :=
  ⟨fun x => if x.val then (2 : ℂ) else (1 : ℂ), IsLocallyConstant.of_discrete _⟩
private def squareResult : LocallyConstant
    {x : squareSpace // flip x ∈ (⊤ : Opens squareSpace)} ℂ :=
  (s2v_coverPresheafSquareMap (𝟙 squareSpace) (𝟙 squareSpace) flip flip
    (by simp)).app (.op ⊤) squareSection
private theorem fibre_square_example : squareResult ⟨false, by trivial⟩ = (2 : ℂ) := rfl
private theorem fibre_square_falsification : squareResult ⟨false, by trivial⟩ ≠ (1 : ℂ) := by
  rw [fibre_square_example]
  norm_num
#print axioms fibre_square_example
#print axioms fibre_square_falsification


#print axioms s2v_sheafPullbackCompIso
#print axioms s2v_sheafPushforwardEquivalence
#print axioms s2v_sheafPullbackHomeomorphCohomologyEquiv
#print axioms s2v_projective_schemeFibre_descent
#print axioms s2v_coverPresheafSquareMap
#print axioms s2v_coverPresheafSquareMap_scalar
#print axioms s2v_coverPresheafSquareMap_deck
#print axioms s2v_coverSheafSquareMap
#print axioms s2v_coverSheafSquareMap_unit
#print axioms s2v_coverSheafSquareMap_naturality
#print axioms s2v_actualCoverSheafFibreMap
#print axioms s2v_coverPresheafSquareMap_stalk_evaluation
#print axioms s2v_coverPresheafSquareMap_stalk_isIso
#print axioms s2v_sheafPullback_unit_hom
#print axioms s2v_sheafPullback_mate_stalk
#print axioms s2v_stalkPushforward_naturality
#print axioms s2v_coverSheafSquareMap_stalk_isIso
#print axioms s2v_coverSheafSquareMap_pullback_isIso
#print axioms s2v_actualCoveringFibre_bijective
#print axioms s2v_actualCoverSheafFibreMap_isIso
#print axioms s2v_coverSheafSquareMap_pullback_naturality
#print axioms s2v_coverPresheafSquareMap_deck_pow
#print axioms s2v_coverPresheafSquareMap_projector
#print axioms s2v_coverSheafSquareMap_pullback_projector
#print axioms s2v_imageTransportIso
#print axioms s2v_actualCharacterSheafFibreIso
#print axioms s2v_coveringFibreProjection_isPullback
#print axioms s2v_coveringFibreProjection_finite
#print axioms s2v_characterSheafSquarePullbackIso
#print axioms s2v_pointFibre_bijective_of_isIso
#print axioms s2v_singularCohomologyIso
#print axioms s2v_eigenspaceEquiv
#print axioms s2v_finite_cover_character_cohomology
#print axioms s2d_fibre_restriction_descent_aux
#print axioms HodgeLean.Foundations.Program.s2cv3_fibre_character_comparison_aux
#print axioms squareSpace
#print axioms flip
#print axioms squareSection
#print axioms squareResult
#print axioms fibre_square_example
#print axioms fibre_square_falsification

end HodgeLean.Foundations.Program.V3BaseChange

#print axioms HodgeLean.Foundations.Program.s2cv3_fibre_character_comparison_aux
