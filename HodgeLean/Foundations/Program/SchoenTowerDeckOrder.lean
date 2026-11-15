import HodgeLean.Foundations.Program.SchoenTowerActionLemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2v_preimageDeck_baseChange {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β) :
    ((Over.pullback j).map (show Over.mk β ⟶ Over.mk β from Over.homMk d hd)).left = s2b_preimageDeck β j d hd := rfl

theorem s2v_overDeck_order {W B : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (horder : (End.of d) ^ m = 1) :
    (End.of (show Over.mk β ⟶ Over.mk β from Over.homMk d hd)) ^ m = 1 := by
  let F := Over.forget B
  have hinj : Function.Injective (F.mapEnd (Over.mk β)) := by
    intro a b hab
    apply End.ext
    exact F.map_injective (congrArg End.asHom hab)
  apply hinj
  rw [map_pow, map_one]
  exact horder

theorem s2v_preimageDeck_order {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (horder : (End.of d) ^ m = 1) :
    (End.of (s2b_preimageDeck β j d hd)) ^ m = 1 := by
  let F := Over.pullback j ⋙ Over.forget E
  have h := congrArg (F.mapEnd (Over.mk β)) (s2v_overDeck_order β d hd m horder)
  rw [map_pow, map_one] at h
  exact h

theorem s2v_topCat_end_pow_apply {X : TopCat} (d : X ⟶ X) (n : ℕ) (x : X) :
    ((End.of d) ^ n).asHom x = d^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, End.mul_asHom, ConcreteCategory.comp_apply, ih,
      Function.iterate_succ_apply]

theorem s2v_preimageDeck_points_order {W B E : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (d : W ⟶ W) (hd : d ≫ β = β)
    (m : ℕ) (horder : (End.of d) ^ m = 1)
    (x : ComplexPoint (s2b_preimage β j)) :
    (s2c_points.map (s2b_preimageDeck β j d hd))^[m] x = x := by
  have h := congrArg (s2c_points.mapEnd (s2b_preimage β j))
    (s2v_preimageDeck_order β j d hd m horder)
  rw [map_pow, map_one] at h
  have he := congrArg (fun q : End (s2c_points.obj (s2b_preimage β j)) => q.asHom x) h
  change ((End.of (s2c_points.map (s2b_preimageDeck β j d hd))) ^ m).asHom x = x at he
  rw [s2v_topCat_end_pow_apply] at he
  exact he

theorem s2v_coveringFibreDeck_order {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (m : ℕ)
    (horder : (End.of d) ^ m = 1) (k : ComplexPoint K) :
    (End.of (s2c_coveringFibreDeck β j p d hd k)) ^ m = 1 :=
  s2v_preimageDeck_order (s2b_toExceptional β j ≫ p) k (s2b_preimageDeck β j d hd)
    (s2b_check_deck_base β j p d hd) m (s2v_preimageDeck_order β j d hd m horder)

theorem s2v_coveringFibreDeck_points_order {W B E K : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (j : E ⟶ B) (p : E ⟶ K)
    (d : W ⟶ W) (hd : d ≫ β = β) (m : ℕ)
    (horder : (End.of d) ^ m = 1) (k : ComplexPoint K)
    (x : ComplexPoint (s2b_coveringFibre β j p k)) :
    (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))^[m] x = x := by
  have h := congrArg (s2c_points.mapEnd (s2b_coveringFibre β j p k))
    (s2v_coveringFibreDeck_order β j p d hd m horder k)
  rw [map_pow, map_one] at h
  have he := congrArg (fun q : End (s2c_points.obj (s2b_coveringFibre β j p k)) => q.asHom x) h
  change ((End.of (s2c_points.map (s2c_coveringFibreDeck β j p d hd k))) ^ m).asHom x = x at he
  rw [s2v_topCat_end_pow_apply] at he
  exact he

end HodgeLean.Foundations.Program
