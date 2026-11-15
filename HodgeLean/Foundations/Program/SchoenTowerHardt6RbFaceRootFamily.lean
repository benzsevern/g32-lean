import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBaseFaceGraph
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbTotalFaceSections

/-! A prepared base map constructs the entire dependent family of ordered face-root extensions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_root_family {n q : ℕ}
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (β : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hβ : ContinuousOn β L.space)
    (G : s2v_t11b_Formula (n + n))
    (hG : ∀ z, z ∈ G.realize ↔ ∃ x ∈ L.space,
      (∀ i, z (Fin.castAdd n i) = x i) ∧ (∀ i, z (Fin.natAdd n i) = β x i))
    (C : Fin q → Set (EuclideanSpace ℝ (Fin n)))
    (r : Fin q → ℕ) (ψ : (j : Fin q) → Fin (r j) → C j → ℝ)
    (hψ : ∀ j a, Continuous (ψ j a)) (hm : ∀ j x, StrictMono (fun a => ψ j a x))
    (Q : Polynomial (MvPolynomial (Fin n) ℝ)) (hQ : Q.Monic)
    (hr : ∀ j a (x : C j), Q.eval₂ (MvPolynomial.eval (fun i => x.val i)) (ψ j a x) = 0)
    (g : (j : Fin q) → Fin (r j) → s2v_t11b_Formula (n + 1))
    (hg : ∀ j a z, z ∈ (g j a).realize ↔ ∃ x : C j,
      (∀ i, z i.succ = x.val i) ∧ z 0 = ψ j a x)
    (parent : L.faces → Fin q)
    (hp : ∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)), x ∈ intrinsicInterior ℝ
      (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) → β x ∈ C (parent s)) :
    ∃ f : (s : L.faces) → Fin (r (parent s)) → EuclideanSpace ℝ (Fin n) → ℝ,
    ∃ H : (s : L.faces) → Fin (r (parent s)) → s2v_t11b_Formula (n + 1),
      (∀ (s : L.faces) (a : Fin (r (parent s))), ContinuousOn (f s a) (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))) ∧
      (∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)), x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) → Monotone (fun a => f s a x)) ∧
      (∀ (s : L.faces) (x : EuclideanSpace ℝ (Fin n)), x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) →
        StrictMono (fun a => f s a x)) ∧
      (∀ (s : L.faces) (a : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))))),
        f s a x = ψ (parent s) a ⟨β x, hp s x hx⟩) ∧
      (∀ (s : L.faces) (a : Fin (r (parent s))) (x : EuclideanSpace ℝ (Fin n)), x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))) →
        Q.eval₂ (MvPolynomial.eval (fun i => β x i)) (f s a x) = 0) ∧
      (∀ (s : L.faces) (a : Fin (r (parent s))) (z : EuclideanSpace ℝ (Fin (n + 1))), z ∈ (H s a).realize ↔ ∃ x ∈ convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n))),
        z 0 = f s a x ∧ (∀ i, z i.succ = x i)) := by
  classical
  let b : L.space → (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    fun x => ⟨β x.val, trivial⟩
  have hb : ∀ z, z ∈ G.realize ↔ ∃ x : L.space,
      (∀ i, z (Fin.castAdd n i) = x.val i) ∧
      (∀ i, z (Fin.natAdd n i) = (b x).val i) := by
    intro z
    rw [hG]
    exact ⟨fun ⟨x, hx, ha, hc⟩ => ⟨⟨x, hx⟩, ha, hc⟩,
      fun ⟨x, ha, hc⟩ => ⟨x.val, x.property, ha, hc⟩⟩
  choose K hK using fun s : L.faces =>
    s2v_hardt6rb_base_face_graph L Set.univ b G hb s.val s.property
  let k (s : L.faces) (x : convexHull ℝ (s.val : Set (EuclideanSpace ℝ (Fin n)))) := β x.val
  have hk (s : L.faces) : Continuous (k s) :=
    continuousOn_iff_continuous_restrict.mp (hβ.mono (L.convexHull_subset_space s.property))
  choose f H hf hmono hstrict hagree hroots hgraph using fun s : L.faces =>
    s2v_hardt6rb_total_face_sections s.val (L.indep s.property) (k s) (hk s)
      (C (parent s)) (ψ (parent s)) (hψ (parent s)) (hm (parent s))
      (fun x => hp s x.val x.property) Q hQ (hr (parent s)) (K s) (hK s)
      (g (parent s)) (hg (parent s))
  refine ⟨f, H, hf, hmono, hstrict, ?_, ?_, hgraph⟩
  · intro s a x hx
    exact hagree s a ⟨x, hx⟩
  · intro s a x hx
    exact hroots s a ⟨x, hx⟩

end HodgeLean.Foundations.Program
