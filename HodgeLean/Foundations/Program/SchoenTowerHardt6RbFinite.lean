import HodgeLean.Foundations.Program.SchoenTowerHardt6
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbGraphs
import Mathlib.Analysis.Convex.Intrinsic

/-! Relative open faces for finite carriers. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_finite_triangulation {n m : ℕ}
    (f : s2v_t11b_Formula n) (hf : f.realize.Finite)
    (b : Fin m → s2v_t11b_Formula n) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ ∃ h : K.space ≃ₜ f.realize,
        (∀ j, ∃ S : Finset (Finset (EuclideanSpace ℝ (Fin n))),
          (↑S : Set _) ⊆ K.faces ∧
          f.realize ∩ (b j).realize =
            (fun x : K.space => (h x).val) ''
              {x : K.space | ∃ s ∈ S,
                x.val ∈ intrinsicInterior ℝ (convexHull ℝ (↑s : Set _))}) ∧
        ∃ g : s2v_t11b_Formula (n + n),
          (∀ z, z ∈ g.realize ↔ ∃ x : K.space,
            (∀ i, z (Fin.castAdd n i) = x.val i) ∧
            (∀ i, z (Fin.natAdd n i) = (h x).val i)) ∧
          (∀ z : EuclideanSpace ℝ (Fin (n + n)),
            WithLp.toLp 2 (fun i =>
              Fin.addCases (fun j => z (Fin.natAdd n j))
                (fun j => z (Fin.castAdd n j)) i) ∈ g.realize ↔
              ∃ y : f.realize,
                (∀ i, z (Fin.castAdd n i) = y.val i) ∧
                (∀ i, z (Fin.natAdd n i) = (h.symm y).val i)) := by
  classical
  obtain ⟨K, hK, hspace, hfaces, h, hh, hhs, hmarks, g, hg⟩ :=
    s2v_hardt6_finite_triangulation f hf b
  refine ⟨K, hK, h, ?_, g, hg, s2v_hardt6rb_inverse_graph h g hg⟩
  intro j
  obtain ⟨S, hS, hmark⟩ := hmarks j
  have hsingle (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
      ({x} : Finset _) ∈ K.faces := by
    have hxA : x ∈ f.realize := by
      have hxmark : x ∈ f.realize ∩ (b j).realize := by
        rw [hmark]
        exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, rfl⟩⟩
      exact hxmark.1
    have hxK : x ∈ K.space := hspace.symm ▸ hxA
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxK
    obtain ⟨y, hy, rfl⟩ := hfaces s hs
    have hxy : x = y := by simpa using hxs
    simpa only [hxy] using hs
  refine ⟨S.image (fun x => {x}), ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    exact hsingle x hx
  · ext y
    constructor
    · intro hy
      have hyS : y ∈ S := by
        rw [hmark] at hy
        obtain ⟨v, hy⟩ := Set.mem_iUnion.mp hy
        obtain ⟨hv, hyv⟩ := Set.mem_iUnion.mp hy
        exact (Set.mem_singleton_iff.mp hyv).symm ▸ hv
      have hyK : y ∈ K.space := hspace.symm ▸ hy.1
      refine ⟨⟨y, hyK⟩, ?_, hh _⟩
      refine ⟨{y}, Finset.mem_image.mpr ⟨y, hyS, rfl⟩, ?_⟩
      simp only [Finset.coe_singleton, convexHull_singleton,
        intrinsicInterior_singleton, Set.mem_singleton_iff]
    · rintro ⟨x, ⟨s, hs, hxs⟩, hxy⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
      have hxv : x.val = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton,
          intrinsicInterior_singleton, Set.mem_singleton_iff] using hxs
      have hvy : v = y := hxv.symm.trans ((hh x).symm.trans hxy)
      rw [hmark]
      exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv, hvy.symm⟩⟩

end HodgeLean.Foundations.Program
