import HodgeLean.Foundations.RationalHomologyManifold.LocallyStationarySections

/-! Additive maps obtained by gluing actual locally stationary section sequences.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The locally stationary values of actual additive section maps form an additive section map.
Source: Bredon, Sheaf Theory, second edition, I.1; unique gluing and stalkwise additivity.
HC no distance; AV milestone no distance.
-/
def locallyStationarySectionMap {X : TopCat.{0}} (A : AddCommGrpCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Opens X) (f : ℕ → (A ⟶ F.obj.obj (op U)))
    (hlocal : ∀ a : A, ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      F.obj.map (homOfLE hV).op (f (m + r) a) = F.obj.map (homOfLE hV).op (f m a)) :
    A ⟶ F.obj.obj (op U) :=
  AddCommGrpCat.ofHom {
    toFun a := locallyStationarySectionValue F U (fun m => f m a) (hlocal a)
    map_zero' := by
      apply TopCat.Presheaf.section_ext F
      intro x hx
      obtain ⟨m, hm⟩ := locallyStationarySectionValue_germ_eventually F U (fun m => f m 0)
        (hlocal 0) ⟨x, hx⟩
      simpa only [Nat.add_zero, map_zero] using hm 0
    map_add' := by
      intro a b
      apply TopCat.Presheaf.section_ext F
      intro x hx
      let y : U := ⟨x, hx⟩
      obtain ⟨m, hm⟩ := locallyStationarySectionValue_germ_eventually F U
        (fun j => f j (a + b)) (hlocal (a + b)) y
      obtain ⟨n, hn⟩ := locallyStationarySectionValue_germ_eventually F U
        (fun j => f j a) (hlocal a) y
      obtain ⟨k, hk⟩ := locallyStationarySectionValue_germ_eventually F U
        (fun j => f j b) (hlocal b) y
      let N := m + n + k
      have hm' := hm (N - m)
      have hn' := hn (N - n)
      have hk' := hk (N - k)
      rw [Nat.add_sub_of_le (by dsimp [N]; omega : m ≤ N)] at hm'
      rw [Nat.add_sub_of_le (by dsimp [N]; omega : n ≤ N)] at hn'
      rw [Nat.add_sub_of_le (by dsimp [N]; omega : k ≤ N)] at hk'
      calc
        _ = F.presheaf.germ U x hx (f N (a + b)) := hm'
        _ = F.presheaf.germ U x hx (f N a) + F.presheaf.germ U x hx (f N b) := by
          rw [map_add, map_add]
        _ = F.presheaf.germ U x hx
              (locallyStationarySectionValue F U (fun j => f j a) (hlocal a)) +
            F.presheaf.germ U x hx
              (locallyStationarySectionValue F U (fun j => f j b) (hlocal b)) :=
          congrArg₂ (fun a b => a + b) hn'.symm hk'.symm
        _ = _ := (map_add _ _ _).symm }

#print axioms locallyStationarySectionMap
/-- The actual glued additive map retains the eventual germs of its section-map sequence.
Source: Bredon, Sheaf Theory, second edition, I.1; the normalization of additive sheaf gluing.
HC no distance; AV milestone no distance.
-/
theorem locallyStationarySectionMap_germ_eventually {X : TopCat.{0}} (A : AddCommGrpCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Opens X) (f : ℕ → (A ⟶ F.obj.obj (op U)))
    (hlocal : ∀ a : A, ∀ x : U, ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      F.obj.map (homOfLE hV).op (f (m + r) a) = F.obj.map (homOfLE hV).op (f m a)) (a : A) :
    ∀ x : U, ∃ m : ℕ, ∀ r : ℕ,
      F.presheaf.germ U x.val x.property (locallyStationarySectionMap A F U f hlocal a) =
        F.presheaf.germ U x.val x.property (f (m + r) a) :=
  locallyStationarySectionValue_germ_eventually F U (fun m => f m a) (hlocal a)

#print axioms locallyStationarySectionMap_germ_eventually
end HodgeLean.Foundations.RationalHomologyManifold
