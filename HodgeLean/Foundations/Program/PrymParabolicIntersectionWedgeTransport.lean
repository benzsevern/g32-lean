import HodgeLean.Foundations.Program.PrymParabolicIntersectionWedgeInverse

noncomputable section
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular Convexity
namespace HodgeLean.Foundations.Program

theorem hga_left_halfPlane_avoids_discs (z : ℂ) (hz : z.re < -12 - 1 / 8) :
    (z : OnePoint ℂ) ∉ ⋃ k : Fin 10, ((↑) : ℂ → OnePoint ℂ) ''
      Metric.closedBall (mr_base k) (b6t_radius mr_base) := by
  simp only [Set.mem_iUnion, not_exists]
  intro k
  rintro ⟨w, hw, he⟩
  have he' : w = z := OnePoint.coe_injective he
  subst w
  have hn : ‖z - mr_base k‖ < 1 / 8 :=
    lt_of_le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw) mr_radius_lt8
  have hr : |z.re - ((k.val : ℝ) - 12)| ≤ ‖z - mr_base k‖ := by
    simpa [mr_base] using Complex.abs_re_le_norm (z - mr_base k)
  have hk : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  linarith [neg_le_abs (z.re - ((k.val : ℝ) - 12))]

theorem hga_transport_fixed_left (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base)
    (z : ℂ) (hz : z.re < -12 - 1 / 8) :
    b6t_sphere mr_base t (z : OnePoint ℂ) = (z : OnePoint ℂ) :=
  (b6t_fixed mr_base mr_base_mem_chart t ht).2.2.2 _
    (hga_left_halfPlane_avoids_discs z hz)

theorem hga_firstWedge_centre :
    hg5_wedge (hg3_waist 0) (hg5_markRe 0) (hga_triangleRetraction 0) = (-37 / 3 : ℂ) := by
  norm_num [hg5_wedge, hg3_waist, hg5_markRe, hga_triangleRetraction_zero_weights]

open scoped Topology in
theorem hga_firstTriangle_transport_parametrization
    (t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc mr_base) :
    ∀ᶠ z : ℂ in 𝓝 0,
      b6t_sphere mr_base t
        (hg5_tri (Sum.inl (0, ()))
          (hga_triangleRetraction (hga_wedgeInverse (hg3_waist 0) (hg5_markRe 0) z))) =
        ((z - 37 / 3 : ℂ) : OnePoint ℂ) := by
  have huv : hg3_waist 0 < hg5_markRe 0 := by norm_num [hg3_waist, hg5_markRe]
  have hleft : ∀ᶠ z : ℂ in 𝓝 0, (z - 37 / 3).re < -12 - 1 / 8 :=
    (isOpen_lt (by fun_prop : Continuous (fun z : ℂ ↦ (z - 37 / 3).re))
      continuous_const).mem_nhds (by norm_num)
  filter_upwards [hga_wedgeInverse_local_parametrization _ _ huv, hleft] with z hz hzleft
  rw [hga_firstWedge_centre] at hz
  change b6t_sphere mr_base t
    ((hg5_wedge (hg3_waist 0) (hg5_markRe 0)
      (hga_triangleRetraction (hga_wedgeInverse (hg3_waist 0) (hg5_markRe 0) z)) : ℂ) :
        OnePoint ℂ) = _
  rw [hz]
  convert hga_transport_fixed_left t ht (z - 37 / 3) hzleft using 1 <;>
    congr 2 <;> ring

/-- A triangle lift written in the inverse coordinates of its finite base wedge.
Source: `hga_wedgeInverse`, the continuous triangle retraction. -/
def hga_wedgeLift {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (u v : ℝ) : C(ℂ, T) :=
  (hga_triangleExtension σ).comp ⟨hga_wedgeInverse u v, by
    unfold hga_wedgeInverse
    fun_prop⟩

theorem hga_wedgeLift_zero {T : Type} [TopologicalSpace T]
    (σ : C(StdSimplex ℝ (Fin 3), T)) (u v : ℝ) :
    hga_wedgeLift σ u v 0 = σ (hga_triangleRetraction 0) := by
  simp [hga_wedgeLift, hga_wedgeInverse, hga_triangleExtension]

open scoped Topology in
theorem hga_firstLift_projection {C : Type} [TopologicalSpace C]
    (f : C → OnePoint ℂ) (σ : C(StdSimplex ℝ (Fin 3), C))
    (hσ : ∀ a, f (σ a) = hg5_tri (Sum.inl (0, ())) a)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc mr_base) (t : V) :
    ∀ᶠ z : ℂ in 𝓝 0, b63d_projection mr_base C f V hV t
      ((b6m_coordinate mr_base C ⟨t.val, hV t.property⟩).symm
        (hga_wedgeLift σ (hg3_waist 0) (hg5_markRe 0) z)) =
      ((z - 37 / 3 : ℂ) : OnePoint ℂ) := by
  filter_upwards [hga_firstTriangle_transport_parametrization t.val (hV t.property)] with z hz
  change b6t_sphere mr_base t.val
    (f (σ (hga_triangleRetraction (hga_wedgeInverse (hg3_waist 0) (hg5_markRe 0) z)))) = _
  rw [hσ]
  exact hz

#print axioms hga_firstLift_projection

#print axioms hga_wedgeLift
#print axioms hga_wedgeLift_zero

#print axioms hga_firstTriangle_transport_parametrization

#print axioms hga_firstWedge_centre

#print axioms hga_transport_fixed_left

#print axioms hga_left_halfPlane_avoids_discs
end HodgeLean.Foundations.Program
