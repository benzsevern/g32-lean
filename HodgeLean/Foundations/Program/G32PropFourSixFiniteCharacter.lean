import HodgeLean.Foundations.Program.G32PropFourSixFiniteExample

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

theorem g32p_lifted_generators_top {G : Type*} [Group G] {k : ℕ}
    (gens : Fin k → G) (H : Subgroup G)
    (hH : Subgroup.closure (Set.range gens) = H)
    (lifted : Fin k → H) (hlifted : ∀ s, (lifted s : G) = gens s) :
    Subgroup.closure (Set.range lifted) = ⊤ := by
  have hr : H.subtype '' Set.range lifted = Set.range gens := by
    ext x
    constructor
    · rintro ⟨y, ⟨s, rfl⟩, hx⟩
      exact ⟨s, (hlifted s).symm.trans hx⟩
    · rintro ⟨s, hs⟩
      exact ⟨lifted s, ⟨s, rfl⟩, (hlifted s).trans hs⟩
  have he : (Subgroup.closure (Set.range lifted)).map H.subtype = H := by
    rw [MonoidHom.map_closure, hr, hH]
  apply eq_top_iff.mpr
  intro x _
  have hx : (x : G) ∈ (Subgroup.closure (Set.range lifted)).map H.subtype := by
    rw [he]
    exact x.property
  obtain ⟨y, hy, hxy⟩ := hx
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy

abbrev g32p_row13_subgroup : Subgroup g32p_G :=
  Subgroup.closure (Set.range g32p_row13_groupGenerators)

def g32p_row13_groupEquiv : Fin 24 ≃ g32p_row13_subgroup :=
  Classical.choose g32p_row13_groupEnumeration

theorem g32p_row13_groupEquiv_map (i : Fin 24) :
    b4b_toMatrix (g32p_row13_groupEquiv i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row13_groupNodes i)) :=
  Classical.choose_spec g32p_row13_groupEnumeration i

def g32p_row13_liftedGenerators : Fin 3 → g32p_row13_subgroup :=
  fun s => ⟨g32p_row13_groupGenerators s, Subgroup.subset_closure (Set.mem_range_self s)⟩

theorem g32p_row13_liftedGenerators_top :
    Subgroup.closure (Set.range g32p_row13_liftedGenerators) = ⊤ :=
  g32p_lifted_generators_top g32p_row13_groupGenerators g32p_row13_subgroup rfl
    g32p_row13_liftedGenerators (fun _ => rfl)

theorem g32p_row13_groupEquiv_one : g32p_row13_groupEquiv 0 = 1 := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row13_groupEquiv 0 : g32p_G) = b4b_toMatrix 1
  rw [g32p_row13_groupEquiv_map, map_one,
    show g32p_row13_groupNodes 0 = HurwitzPrymRex_mone by decide,
    HurwitzPrymRex_evM_mone, map_one]

theorem g32p_row13_groupEquiv_step (i : Fin 24) (s : Fin 3) :
    g32p_row13_groupEquiv (g32p_row13_groupNext i s) =
      g32p_row13_groupEquiv i * g32p_row13_liftedGenerators s := by
  apply Subtype.ext
  apply Subtype.val_injective
  change b4b_toMatrix (g32p_row13_groupEquiv (g32p_row13_groupNext i s) : g32p_G) =
    b4b_toMatrix ((g32p_row13_groupEquiv i : g32p_G) * g32p_row13_groupGenerators s)
  rw [map_mul, g32p_row13_groupEquiv_map, g32p_row13_groupEquiv_map,
    g32p_row13_groupGenerator_map, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  exact congrArg (fun a => HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a))
    ((of_decide_eq_true g32p_row13_groupTransition) i s).symm

theorem g32p_row13_generator_index (s : Fin 3) :
    g32p_row13_groupEquiv.symm (g32p_row13_liftedGenerators s) =
      g32p_row13_groupNext 0 s := by
  have he : g32p_row13_groupEquiv (g32p_row13_groupNext 0 s) =
      g32p_row13_liftedGenerators s := by
    rw [g32p_row13_groupEquiv_step, g32p_row13_groupEquiv_one, one_mul]
  simpa only [Equiv.symm_apply_apply] using (congrArg g32p_row13_groupEquiv.symm he).symm

def g32p_row13_characterValues : Fin 24 → Multiplicative (ZMod 12) :=
  fun i => Multiplicative.ofAdd
    (![0, 9, 4, 6, 6, 1, 3, 8, 10, 3, 10, 0, 5, 7, 2, 7, 9, 2, 4, 11, 11, 1, 8, 5] i)

theorem g32p_row13_characterTransition : ∀ i : Fin 24, ∀ s : Fin 3,
    g32p_row13_characterValues (g32p_row13_groupNext i s) =
      g32p_row13_characterValues i * g32p_row13_characterValues (g32p_row13_groupNext 0 s) := by
  decide

def g32p_row13_finiteCharacter : g32p_row13_subgroup →* Multiplicative (ZMod 12) :=
  g32p_homOfFiniteTransitions g32p_row13_liftedGenerators g32p_row13_liftedGenerators_top
    g32p_row13_groupEquiv 0 g32p_row13_groupEquiv_one
    g32p_row13_groupNext g32p_row13_groupEquiv_step g32p_row13_characterValues (by rfl)
    (fun i s => by rw [g32p_row13_generator_index]; exact g32p_row13_characterTransition i s)

theorem g32p_row13_finiteCharacter_surjective : Function.Surjective g32p_row13_finiteCharacter := by
  have hs : Function.Surjective g32p_row13_characterValues := by decide
  intro x
  obtain ⟨i, hi⟩ := hs x
  refine ⟨g32p_row13_groupEquiv i, ?_⟩
  change g32p_row13_characterValues (g32p_row13_groupEquiv.symm (g32p_row13_groupEquiv i)) = x
  simpa only [Equiv.symm_apply_apply] using hi

def g32p_row13_finiteSupplier : g32p_Supplier :=
  ⟨g32p_row13_subgroup, 12, by decide, g32p_row13_finiteCharacter,
    g32p_row13_finiteCharacter_surjective⟩

theorem g32p_row13_finiteSupplier_order : Nat.card g32p_row13_finiteSupplier.H = 24 :=
  g32p_row13_groupOrder

end HodgeLean.Foundations.Program
