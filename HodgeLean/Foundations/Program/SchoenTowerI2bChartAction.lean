import HodgeLean.Foundations.Program.SchoenTowerI2bTransport

/-! Restriction of the retained action to a base chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A base-preserving map induces a unique action on every base change.
Source: the universal property of the scheme fibre product. -/
theorem s2v_i2b_chart_action_exists_unique
    {W B U : Scheme} (β : W ⟶ B) (u : U ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β) :
    ∃! dn : pullback β u ⟶ pullback β u,
      dn ≫ pullback.fst β u = pullback.fst β u ≫ d ∧
      dn ≫ pullback.snd β u = pullback.snd β u := by
  refine ⟨pullback.lift (pullback.fst β u ≫ d) (pullback.snd β u)
    (by rw [Category.assoc, hd]; exact pullback.condition),
    ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
  intro dn hn
  apply pullback.hom_ext
  · exact hn.1.trans (pullback.lift_fst _ _ _).symm
  · exact hn.2.trans (pullback.lift_snd _ _ _).symm

/-- The chart projection intertwines every iterate of the retained action.
Source: iteration of the first projection equation of the scheme fibre product. -/
theorem s2v_i2b_chart_action_iterate
    {W B U : Scheme} (β : W ⟶ B) (u : U ⟶ B)
    (d : W ⟶ W) (dn : pullback β u ⟶ pullback β u)
    (hdn : dn ≫ pullback.fst β u = pullback.fst β u ≫ d)
    (n : ℕ) :
    ((End.of dn) ^ n).asHom ≫ pullback.fst β u =
      pullback.fst β u ≫ ((End.of d) ^ n).asHom := by
  induction n with
  | zero => simp only [pow_zero, End.one_asHom, Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', End.mul_asHom, End.mul_asHom, Category.assoc, hdn,
      ← Category.assoc, ih, Category.assoc]

/-- A chart isomorphism identifies the action once its two projections agree.
Source: the universal property of the scheme fibre product. -/
theorem s2v_i2b_chart_action_conjugacy
    {W B U N : Scheme} (β : W ⟶ B) (u : U ⟶ B)
    (e : pullback β u ≅ N) (d : W ⟶ W)
    (dn : pullback β u ⟶ pullback β u) (g : N ⟶ N)
    (hfirst : dn ≫ pullback.fst β u = pullback.fst β u ≫ d)
    (hsecond : dn ≫ pullback.snd β u = pullback.snd β u)
    (hgfirst : (e.hom ≫ g ≫ e.inv) ≫ pullback.fst β u = pullback.fst β u ≫ d)
    (hgsecond : (e.hom ≫ g ≫ e.inv) ≫ pullback.snd β u = pullback.snd β u) :
    dn ≫ e.hom = e.hom ≫ g := by
  have he : dn = e.hom ≫ g ≫ e.inv :=
    pullback.hom_ext (hfirst.trans hgfirst.symm) (hsecond.trans hgsecond.symm)
  rw [he]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

end HodgeLean.Foundations.Program
