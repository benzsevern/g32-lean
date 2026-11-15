import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ImageComparison
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Restriction
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Diagonal

/-! Actual Boolean relation images and dimension-controlled coordinate projections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_relation_image_formula {n q : ℕ}
    (S : s2v_t11b_Formula n) (G : s2v_t11b_Formula (n + q)) :
    ∃ F : s2v_t11b_Formula q, ∀ y : EuclideanSpace ℝ (Fin q),
      y ∈ F.realize ↔ ∃ x : S.realize,
        WithLp.toLp 2 (Fin.append (fun i => x.val i) (fun i => y i)) ∈ G.realize := by
  let u := s2v_hardt2_boundIndex q n
  let v := s2v_hardt2_freeIndex q n
  let ρ : Fin (n + q) → Fin (q + n) := Fin.addCases u v
  obtain ⟨F, hF⟩ := s2v_hardt2_repeated_projection
    (.inter (s2v_hardt1_rename u S) (s2v_hardt1_rename ρ G))
  refine ⟨F, ?_⟩
  intro y
  rw [hF]
  have hbase (x : Fin n → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert n x y (u i)) = WithLp.toLp 2 x := by
    ext i
    exact s2v_hardt2_insert_bound x y i
  have hcoords (x : Fin n → ℝ) :
      WithLp.toLp 2 (fun i => s2v_hardt2_insert n x y (ρ i)) =
        WithLp.toLp 2 (Fin.append x (fun i => y i)) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [ρ, u, v, s2v_hardt2_insert_bound, s2v_hardt2_insert_free]
  constructor
  · rintro ⟨x, hx⟩
    change _ ∧ _ at hx
    rw [s2v_hardt1_realize_rename, hbase, s2v_hardt1_realize_rename, hcoords] at hx
    exact ⟨⟨WithLp.toLp 2 x, hx.1⟩, hx.2⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x.val i, ?_⟩
    change _ ∧ _
    rw [s2v_hardt1_realize_rename, hbase, s2v_hardt1_realize_rename, hcoords]
    exact ⟨x.property, hx⟩

theorem s2v_hardt_cad5_coordinate_image_partition {n q : ℕ}
    (S : s2v_t11b_Formula n) (P : s2v_hardt_cad5_Partition S.realize)
    (r : Fin q → Fin n) :
    ∃ F : s2v_t11b_Formula q, ∃ Q : s2v_hardt_cad5_Partition F.realize,
      (∀ y : EuclideanSpace ℝ (Fin q), y ∈ F.realize ↔ ∃ x : S.realize,
        y = WithLp.toLp 2 (fun i => x.val (r i))) ∧ Q.dimension ≤ P.dimension := by
  obtain ⟨D, hD⟩ := s2v_hardt_cad5_coordinate_map_graph r
  obtain ⟨F, hF⟩ := s2v_hardt_cad5_relation_image_formula S D
  have hImage (y : EuclideanSpace ℝ (Fin q)) : y ∈ F.realize ↔
      ∃ x : S.realize, y = WithLp.toLp 2 (fun i => x.val (r i)) := by
    rw [hF]
    exact exists_congr (fun x => hD x.val y)
  obtain ⟨Q⟩ := s2v_hardt_cad5_partition_exists F
  let f : S.realize → F.realize := fun x =>
    ⟨WithLp.toLp 2 (fun i => x.val (r i)), (hImage _).mpr ⟨x, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (hImage y.val).mp y.property
    exact ⟨x, Subtype.ext hx.symm⟩
  exact ⟨F, Q, hImage, s2v_hardt_cad5_dimension_le_of_graph_surjective P Q f hf D
    (fun x y => hD x.val y)⟩

end HodgeLean.Foundations.Program
