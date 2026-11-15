import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedUnionRelativeCap

/-! # Actual intersection coordinates through iterated support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original intersection-support suspension retains the specified recursive intersection coordinates on both sides.
Source: properCycle_real_support_suspension_support_eq; properCycle_iterated_support_intersection.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_intersection_suspension
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) (n m : ℕ) :
    let X := properCycle_real_support_space Y n
    let A := properCycle_real_normal_support Y S n
    let B := properCycle_real_point_support Y T n
    let P := properCycle_real_point_support Y (S ∩ T) n
    let hI := (properCycle_real_normal_support_isClosed Y S hS n).inter
      (properCycle_real_point_support_isClosed Y T hT n)
    let hP := properCycle_real_point_support_isClosed Y (S ∩ T) (hS.inter hT) n
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (properCycle_iterated_support_intersection_pair_iso Y S T (n+1)).inv) (m+1) ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_support_intersection_pair_iso X A B).hom) (m+1) ≫
      (properCycle_real_support_suspension_iso X (A ∩ B) hI m).hom =
      (properCycle_real_support_suspension_iso X P hP m).hom ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_iterated_support_intersection_pair_iso Y S T n).inv) m := by
  let X := properCycle_real_support_space Y n
  let A := properCycle_real_normal_support Y S n
  let B := properCycle_real_point_support Y T n
  let P := properCycle_real_point_support Y (S ∩ T) n
  let e : A ∩ B = P := properCycle_iterated_support_intersection Y S T n
  let eZ : {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ A ∩ B} =
      {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ P} :=
    congrArg (fun V : Set X => {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ V}) e
  let Z := eqToIso (congrArg (fun V : Set (ℝ × X) =>
    TopPair.ofSubset (X := TopCat.of (ℝ × X)) Vᶜ) eZ)
  let J := properCycle_iterated_support_intersection_pair_iso Y S T n
  let JU := properCycle_iterated_support_intersection_pair_iso Y S T (n+1)
  let R := properCycle_real_support_intersection_pair_iso X A B
  have hp : JU.hom = R.hom ≫ Z.hom := by
    let hU : Set.MapsTo (𝟙 (properCycle_real_support_space Y (n+1)))
        (properCycle_real_normal_support Y S (n+1) ∩
          properCycle_real_point_support Y T (n+1))ᶜ
        (properCycle_real_point_support Y (S ∩ T) (n+1))ᶜ := by
      intro z hz
      change z ∉ properCycle_real_point_support Y (S ∩ T) (n+1)
      rwa [← properCycle_iterated_support_intersection Y S T (n+1)]
    let hZ : Set.MapsTo (𝟙 (TopCat.of (ℝ × X)))
        {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ A ∩ B}ᶜ
        {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ P}ᶜ := by
      intro z hz
      change z ∉ {z : ℝ × X | z.1 = 0 ∧ z.2 ∈ P}
      rwa [← eZ]
    have hu : JU.hom = TopPair.ofSubsetHom (𝟙 _) hU :=
      properCycle_support_eq_pair_hom _ _ _
        (properCycle_iterated_support_intersection Y S T (n+1)) hU
    have hz : Z.hom = TopPair.ofSubsetHom (𝟙 _) hZ :=
      properCycle_support_eq_pair_hom _ _ _ eZ hZ
    rw [hu, hz]
    ext z : 2 <;> rfl
  have hi : JU.inv ≫ R.hom = Z.inv := by
    apply (cancel_mono Z.hom).mp
    rw [Category.assoc, ← hp, JU.inv_hom_id, Z.inv_hom_id]
    rfl
  let hI := (properCycle_real_normal_support_isClosed Y S hS n).inter
    (properCycle_real_point_support_isClosed Y T hT n)
  let hP := properCycle_real_point_support_isClosed Y (S ∩ T) (hS.inter hT) n
  let sI := properCycle_real_support_suspension_iso X (A ∩ B) hI m
  let sP := properCycle_real_support_suspension_iso X P hP m
  let HJ := (relativeHomologyFunctor ℚ m).mapIso J
  let HZ := (relativeHomologyFunctor ℚ (m+1)).mapIso Z
  have hs := properCycle_real_support_suspension_support_eq X (A ∩ B) P hI hP e m
  change HZ.hom ≫ sP.hom = sI.hom ≫ HJ.hom at hs
  have hsi : HZ.inv ≫ sI.hom = sP.hom ≫ HJ.inv := by
    apply (cancel_epi HZ.hom).mp
    calc
      _ = sI.hom := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = (sI.hom ≫ HJ.hom) ≫ HJ.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = _ := by rw [← hs]; simp only [Category.assoc]
  change HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map JU.inv) (m+1) ≫
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map R.hom) (m+1) ≫ sI.hom =
    sP.hom ≫ HJ.inv
  rw [← HomologicalComplex.homologyMap_comp_assoc, ← CategoryTheory.Functor.map_comp, hi]
  exact hsi

end HodgeLean.Foundations.QuotientDuality
