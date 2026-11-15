import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitTopology
import HodgeLean.Foundations.Program.SchoenFiniteMorphisms

/-! Zariski openness from the retained complex-point orbit fibres. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Closed-point orbit fibres of scheme automorphisms make a finite surjection
open on all scheme points. -/
theorem s4_q3_scheme_open_of_point_orbits
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType W.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    {I : Type*} (a : I → (X ≅ X))
    (hinv : ∀ i, (a i).hom ≫ q = q)
    (horbit : ∀ x y : ComplexPoint X, Point.map q x = Point.map q y →
      ∃ i, Point.map (a i).hom x = y) : IsOpenMap q.left := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hsurj := s2_surjective_of_point_surjective q hqsurj
  intro U hU
  let O : Set X.left := ⋃ i, (a i).hom.left '' U
  have hO : IsOpen O := isOpen_iUnion fun i =>
    (a i).hom.left.isOpenEmbedding.isOpenMap U hU
  have hD : IsClosed (q.left '' Oᶜ) := q.left.isClosedMap Oᶜ hO.isClosed_compl
  let E : Set X.left := U ∩ q.left ⁻¹' (q.left '' Oᶜ)
  have hE : IsLocallyClosed E := hU.isLocallyClosed.inter
    (hD.preimage q.left.continuous).isLocallyClosed
  have hEc : E ∩ closedPoints X.left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨hxU, y, hyO, hyq⟩, hxc⟩
    let xp : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hxc) (pointOfClosedPoint_comp X.hom x hxc)
    have hxp : xp.underlying = x := pointOfClosedPoint_apply X.hom x hxc _
    have hqc : IsClosed ({q.left x} : Set W.left) := by
      have hc := q.left.isClosedMap {x} hxc
      simpa only [Set.image_singleton] using hc
    let F : Set X.left := q.left ⁻¹' {q.left x} ∩ Oᶜ
    have hF : IsClosed F := (hqc.preimage q.left.continuous).inter hO.isClosed_compl
    have hFc : F ∩ closedPoints X.left = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨⟨htq, htO⟩, htc⟩
      let tp : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom t htc) (pointOfClosedPoint_comp X.hom t htc)
      have htp : tp.underlying = t := pointOfClosedPoint_apply X.hom t htc _
      have hqt : Point.map q xp = Point.map q tp := by
        apply underlying_injective_of_locallyOfFiniteType
        simp only [Point.underlying_map, hxp, htp]
        exact htq.symm
      obtain ⟨i, hi⟩ := horbit xp tp hqt
      apply htO
      apply Set.mem_iUnion.mpr
      refine ⟨i, x, hxU, ?_⟩
      have hp := congrArg Point.underlying hi
      simpa only [Point.underlying_map, hxp, htp] using hp
    have hFe : F = ∅ := by
      have hd := JacobsonSpace.closure_inter_closedPoints_eq_closure hF.isLocallyClosed
      rw [hFc, closure_empty, hF.closure_eq] at hd
      exact hd.symm
    have hyF : y ∈ F := ⟨hyq, hyO⟩
    simpa only [hFe, Set.mem_empty_iff_false] using hyF
  have hEe : E = ∅ := by
    have hd := JacobsonSpace.closure_inter_closedPoints_eq_closure hE
    rw [hEc, closure_empty] at hd
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : x ∈ closure E := subset_closure hx
    simpa only [← hd, Set.mem_empty_iff_false] using this
  have himage : q.left '' U = (q.left '' Oᶜ)ᶜ := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩ hw
      have : x ∈ E := ⟨hx, hw⟩
      simpa only [hEe, Set.mem_empty_iff_false] using this
    · intro hw
      obtain ⟨x, rfl⟩ := hsurj w
      have hxO : x ∈ O := by
        by_contra hn
        exact hw ⟨x, hn, rfl⟩
      obtain ⟨i, u, hu, hux⟩ := Set.mem_iUnion.mp hxO
      refine ⟨u, hu, ?_⟩
      rw [← hux]
      have hi := congrArg (fun f : X ⟶ W => f.left u) (hinv i)
      exact hi.symm
  rw [himage]
  exact hD.isOpen_compl

/-- Zariski openness of the specified retained finite map follows from its
original cyclic action identities and orbit fibres. -/
theorem s4_q3_retained_schemeMap_isOpenMap (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (N : ℕ)
    [LocallyOfFiniteType (g3_power Y N).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (W : Over (Spec ↧ℂ)) [LocallyOfFiniteType W.hom]
    (q : g3_power Y N ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
      (∑ i, v i) = 0 → s2_action S Y a e N v σ ≫ q = q)
    (hqfib : ∀ x y : ComplexPoint (g3_power Y N),
      Point.map q x = Point.map q y →
        ∃ (v : Fin N → ZMod S.m) (σ : Equiv.Perm (Fin N)),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e N v σ) x = y) :
    IsOpenMap q.left := by
  let I := {v : Fin N → ZMod S.m // (∑ i, v i) = 0} × Equiv.Perm (Fin N)
  apply s4_q3_scheme_open_of_point_orbits q hqsurj
    (fun t : I => s2_coordinateActionIso S Y a e ha1
      (s4_q3_action_reverse_mul S Y a e hamul) N t.1.1 t.2)
  · intro t
    exact hqinv _ _ t.1.2
  · intro x y hxy
    obtain ⟨v, σ, hv, hxy⟩ := hqfib x y hxy
    exact ⟨(⟨v, hv⟩, σ), hxy⟩

end HodgeLean.Foundations.Program
