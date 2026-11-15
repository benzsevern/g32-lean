import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteConnectedCover

/-! Finitely many actual connected components of Boolean polynomial realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite preconnected cover bounds the number of actual connected components of a subset.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite component extraction step. -/
theorem s2v_t11b_finite_components_of_preconnected_cover {X : Type*} [TopologicalSpace X]
    (S : Set X) {m : ℕ} (U : Fin m → Set X)
    (hU : ∀ i, IsPreconnected (U i) ∧ U i ⊆ S)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ U i) : Finite (ConnectedComponents S) := by
  classical
  let I := {i : Fin m | (U i).Nonempty}
  let r : (i : I) → U i.val := fun i => ⟨i.property.choose, i.property.choose_spec⟩
  let F : (i : Fin m) → U i → S := fun i x => ⟨x.val, (hU i).2 x.property⟩
  let g : I → ConnectedComponents S := fun i => ConnectedComponents.mk (F i.val (r i))
  apply Finite.of_surjective g
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hi⟩ := hcover x.val x.property
  let j : I := ⟨i, ⟨x.val, hi⟩⟩
  refine ⟨j, ?_⟩
  haveI : PreconnectedSpace (U i) := isPreconnected_iff_preconnectedSpace.mp (hU i).1
  have hF : Continuous (F i) := continuous_subtype_val.subtype_mk _
  have hc := isPreconnected_range hF
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact hc.subset_connectedComponent ⟨⟨x.val, hi⟩, rfl⟩ ⟨r j, rfl⟩

/-- Every actual Boolean polynomial realization has finitely many connected components.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite realization component step. -/
theorem s2v_t11b_formula_finite_components {n : ℕ} (f : s2v_t11b_Formula n) :
    Finite (ConnectedComponents f.realize) := by
  obtain ⟨m, U, hU, hcover⟩ := s2v_t11b_formula_finite_preconnected_cover n f
  exact s2v_t11b_finite_components_of_preconnected_cover f.realize U hU hcover

/-- Finiteness of actual components makes each component both open and closed in the original space.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite component separation step. -/
theorem s2v_t11b_component_clopen_of_finite {X : Type*} [TopologicalSpace X]
    [Finite (ConnectedComponents X)] (x : X) : IsClopen (connectedComponent x) := by
  letI : T1Space (ConnectedComponents X) := ⟨fun c => by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    apply ConnectedComponents.isQuotientMap_coe.isCoinducing.isClosed_preimage.mp
    simpa only [connectedComponents_preimage_singleton] using
      (isClosed_connectedComponent : IsClosed (connectedComponent y))⟩
  have ho : IsOpen ({ConnectedComponents.mk x} : Set (ConnectedComponents X)) := isOpen_discrete _
  refine ⟨isClosed_connectedComponent, ?_⟩
  simpa only [connectedComponents_preimage_singleton] using ho.preimage ConnectedComponents.continuous_coe

/-- The actual connected components give a finite disjoint connected partition of each Boolean realization.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, actual finite component partition step. -/
theorem s2v_t11b_formula_finite_component_partition {n : ℕ} (f : s2v_t11b_Formula n) :
    ∃ m : ℕ, ∃ U : Fin m → Set (EuclideanSpace ℝ (Fin n)),
      (∀ i, IsConnected (U i) ∧ U i ⊆ f.realize) ∧
      (∀ x, x ∈ f.realize → ∃ i, x ∈ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ i, ∃ x : f.realize, U i = Subtype.val '' connectedComponent x := by
  classical
  letI := s2v_t11b_formula_finite_components f
  letI := Fintype.ofFinite (ConnectedComponents f.realize)
  let E := Fintype.equivFin (ConnectedComponents f.realize)
  choose r hr using (ConnectedComponents.surjective_coe :
    Function.Surjective (ConnectedComponents.mk : f.realize → ConnectedComponents f.realize))
  let U : Fin (Fintype.card (ConnectedComponents f.realize)) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => Subtype.val '' connectedComponent (r (E.symm i))
  refine ⟨_, U, ?_, ?_, ?_, fun i => ⟨r (E.symm i), rfl⟩⟩
  · intro i
    refine ⟨isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  · intro x hx
    let y : f.realize := ⟨x, hx⟩
    refine ⟨E (ConnectedComponents.mk y), y, ?_, rfl⟩
    apply ConnectedComponents.coe_eq_coe'.mp
    rw [hr, E.symm_apply_apply]
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hval⟩
    have huv : v = u := Subtype.ext hval
    subst v
    have hi := ConnectedComponents.coe_eq_coe'.mpr hu
    have hj := ConnectedComponents.coe_eq_coe'.mpr hv
    rw [hr] at hi hj
    exact hij (E.symm.injective (hi.symm.trans hj))

end HodgeLean.Foundations.Program
