import HodgeLean.Foundations.Program.SchoenTowerT11bFiniteSimpleDegreePieces
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Incidence continuation for continuous sections in finite root arrangements.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A continuous section contained in finitely many distinct continuous graphs retains its graph label on a connected base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root incidence continuation step. -/
theorem s2v_t11b_contained_section_label {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {m : ℕ} (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ t, Function.Injective (fun i => ψ i t))
    (χ : X → ℝ) (hχ : Continuous χ) (hcontained : ∀ t, ∃ i, χ t = ψ i t)
    (a : X) (j : Fin m) (ha : χ a = ψ j a) : ∀ t, χ t = ψ j t := by
  let e := s2v_t11b_finite_graph_homeomorph ψ hψ hinj
  let f : X → {z : X × ℝ | ∃ i, z.2 = ψ i z.1} := fun t => ⟨(t, χ t), hcontained t⟩
  have hf : Continuous f := (continuous_id.prodMk hχ).subtype_mk _
  let v : X → Fin m × X := fun t => e.symm (f t)
  have hv : Continuous v := e.symm.continuous.comp hf
  have hvalue : ∀ t, (v t).2 = t ∧ ψ (v t).1 t = χ t := by
    intro t
    have he := congrArg Subtype.val (e.apply_symm_apply (f t))
    change (e (v t)).val = (t, χ t) at he
    rw [s2v_t11b_finite_graph_homeomorph_apply] at he
    have hb := congrArg Prod.fst he
    have hs := congrArg Prod.snd he
    change (v t).2 = t at hb
    change ψ (v t).1 (v t).2 = χ t at hs
    rw [hb] at hs
    exact ⟨hb, hs⟩
  have hj : (v a).1 = j := hinj a ((hvalue a).2.trans ha)
  intro t
  have hc : (v t).1 = (v a).1 := PreconnectedSpace.constant inferInstance (continuous_fst.comp hv)
  exact (hvalue t).2.symm.trans (by rw [hc, hj])


/-- Continuous enumerations of an atom's roots and a containing carrier give constant atom vanishing on every carrier section, without multiplicity restrictions.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, root incidence invariance step. -/
theorem s2v_t11b_enumerated_atom_zero_iff {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {m r : ℕ} (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ t, Function.Injective (fun i => ψ i t))
    (F : X → ℝ → ℝ) (χ : Fin r → X → ℝ) (hχ : ∀ i, Continuous (χ i))
    (hroots : ∀ t x, F t x = 0 ↔ ∃ i, x = χ i t)
    (hcontained : ∀ t x, F t x = 0 → ∃ i, x = ψ i t)
    (j : Fin m) (a b : X) : F a (ψ j a) = 0 ↔ F b (ψ j b) = 0 := by
  have hf : ∀ a b, F a (ψ j a) = 0 → F b (ψ j b) = 0 := by
    intro a b ha
    obtain ⟨i, hi⟩ := (hroots a (ψ j a)).mp ha
    have hc : ∀ t, ∃ k, χ i t = ψ k t := fun t =>
      hcontained t (χ i t) ((hroots t (χ i t)).mpr ⟨i, rfl⟩)
    have he := s2v_t11b_contained_section_label ψ hψ hinj (χ i) (hχ i) hc a j hi.symm
    exact (hroots b (ψ j b)).mpr ⟨i, (he b).symm⟩
  exact ⟨hf a b, hf b a⟩


/-- Jointly continuous atoms with continuously enumerated contained roots have constant sign on each carrier section, regardless of root multiplicities.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, enumerated atom sign step. -/
theorem s2v_t11b_enumerated_atom_sign {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {m r : ℕ} (ψ : Fin m → X → ℝ) (hψ : ∀ i, Continuous (ψ i))
    (hinj : ∀ t, Function.Injective (fun i => ψ i t))
    (F : X → ℝ → ℝ) (hF : Continuous (fun z : X × ℝ => F z.1 z.2))
    (χ : Fin r → X → ℝ) (hχ : ∀ i, Continuous (χ i))
    (hroots : ∀ t x, F t x = 0 ↔ ∃ i, x = χ i t)
    (hcontained : ∀ t x, F t x = 0 → ∃ i, x = ψ i t)
    (j : Fin m) (a b : X) : 0 ≤ F a (ψ j a) ↔ 0 ≤ F b (ψ j b) := by
  have hz := s2v_t11b_enumerated_atom_zero_iff ψ hψ hinj F χ hχ hroots hcontained j
  by_cases ha : F a (ψ j a) = 0
  · rw [ha, (hz a b).mp ha]
  · have hn : ∀ t, F t (ψ j t) ≠ 0 := fun t ht => ha ((hz a t).mpr ht)
    exact s2v_t11b_nonzero_sign Set.univ isPreconnected_univ (fun t => F t (ψ j t))
      (hF.comp (continuous_id.prodMk (hψ j))).continuousOn (fun t _ => hn t)
      a b (Set.mem_univ a) (Set.mem_univ b)

end HodgeLean.Foundations.Program
