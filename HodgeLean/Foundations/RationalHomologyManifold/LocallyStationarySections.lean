import HodgeLean.Foundations.RationalHomologyManifold.SoftBiproduct
import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.MapOfLocalStalks

/-! Gluing actual sheaf sections whose sequences are locally stationary.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Equality of two sections on one open set persists on every smaller open set.
Source: Mathlib, Topology.Sheaves.Sheaf; functoriality of restriction.
HC no distance; AV milestone no distance.
-/
theorem restrict_sections_eq_of_le {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V W : Opens X} (hV : V ≤ U) (hW : W ≤ V) (s t : F.obj.obj (op U))
    (h : F.obj.map (homOfLE hV).op s = F.obj.map (homOfLE hV).op t) :
    F.obj.map (homOfLE (hW.trans hV)).op s = F.obj.map (homOfLE (hW.trans hV)).op t := by
  have hw := congrArg (F.obj.map (homOfLE hW).op) h
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using hw

#print axioms restrict_sections_eq_of_le
/-- A sequence of actual sections with locally stationary restrictions has a unique section with the stationary germs.
Source: Bredon, Sheaf Theory, second edition, I.1; the sheaf gluing and separation properties.
HC no distance; AV milestone no distance.
-/
theorem existsUnique_section_of_locally_stationary {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Opens X) (s : ℕ → F.obj.obj (op U))
    (hlocal : ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      F.obj.map (homOfLE hV).op (s (m + r)) = F.obj.map (homOfLE hV).op (s m)) :
    ∃! t : F.obj.obj (op U), ∀ x : U, ∃ m : ℕ, ∀ r : ℕ,
      F.presheaf.germ U x.val x.property t = F.presheaf.germ U x.val x.property (s (m + r)) := by
  choose V hV hx m hm using hlocal
  have hcover : U ≤ iSup V := by
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  let tV := fun x : U => F.obj.map (homOfLE (hV x)).op (s (m x))
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V tV := by
    intro x y
    have ha := restrict_sections_eq_of_le F (W := V x ⊓ V y) (hV x) inf_le_left
      (s (m x + m y)) (s (m x)) (hm x (m y))
    have hb := restrict_sections_eq_of_le F (W := V x ⊓ V y) (hV y) inf_le_right
      (s (m y + m x)) (s (m y)) (hm y (m x))
    rw [Nat.add_comm (m y) (m x)] at hb
    change F.obj.map (homOfLE inf_le_left).op
        (F.obj.map (homOfLE (hV x)).op (s (m x))) =
      F.obj.map (homOfLE inf_le_right).op
        (F.obj.map (homOfLE (hV y)).op (s (m y)))
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    exact ha.symm.trans hb
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' V U (fun x => homOfLE (hV x)) hcover tV hcompat
  have htp : ∀ x : U, ∃ m : ℕ, ∀ r : ℕ,
      F.presheaf.germ U x.val x.property t = F.presheaf.germ U x.val x.property (s (m + r)) := by
    intro x
    refine ⟨m x, fun r => ?_⟩
    rw [← F.presheaf.germ_res_apply (i := homOfLE (hV x)) x.val (hx x) t, ht x]
    have hr := congrArg (F.presheaf.germ (V x) x.val (hx x)) (hm x r).symm
    simpa only [tV, F.presheaf.germ_res_apply] using hr
  refine ⟨t, htp, fun t' ht' => ?_⟩
  apply TopCat.Presheaf.section_ext F
  intro x hxU
  let y : U := ⟨x, hxU⟩
  obtain ⟨a, ha⟩ := ht' y
  obtain ⟨b, hb⟩ := htp y
  exact (ha b).trans ((congrArg (fun k => F.presheaf.germ U x hxU (s k)) (Nat.add_comm a b)).trans (hb a).symm)

#print axioms existsUnique_section_of_locally_stationary
/-- Select the unique section given by actual locally stationary restrictions.
Source: Bredon, Sheaf Theory, second edition, I.1; unique sheaf gluing.
HC no distance; AV milestone no distance.
-/
def locallyStationarySectionValue {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (U : Opens X) (s : ℕ → F.obj.obj (op U))
    (hlocal : ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      F.obj.map (homOfLE hV).op (s (m + r)) = F.obj.map (homOfLE hV).op (s m)) :
    F.obj.obj (op U) :=
  (existsUnique_section_of_locally_stationary F U s hlocal).exists.choose

#print axioms locallyStationarySectionValue
/-- The glued stationary section has the actual eventual germ of the given sequence.
Source: Bredon, Sheaf Theory, second edition, I.1; the germ normalization of sheaf gluing.
HC no distance; AV milestone no distance.
-/
theorem locallyStationarySectionValue_germ_eventually {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Opens X) (s : ℕ → F.obj.obj (op U))
    (hlocal : ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      F.obj.map (homOfLE hV).op (s (m + r)) = F.obj.map (homOfLE hV).op (s m)) :
    ∀ x : U, ∃ m : ℕ, ∀ r : ℕ,
      F.presheaf.germ U x.val x.property (locallyStationarySectionValue F U s hlocal) =
        F.presheaf.germ U x.val x.property (s (m + r)) :=
  (existsUnique_section_of_locally_stationary F U s hlocal).exists.choose_spec

#print axioms locallyStationarySectionValue_germ_eventually
end HodgeLean.Foundations.RationalHomologyManifold
