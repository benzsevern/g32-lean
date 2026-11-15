import HodgeLean.Foundations.Program.SchoenCycleC11SphereHelpers
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Metric Topology
namespace HodgeLean.Foundations.Program

/-- Removing one point from an inner product unit sphere gives a contractible space.
Source: Mathlib, stereographic and contractibility of real topological vector spaces. -/
theorem s2e_c11_puncturedSphere_contractible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : sphere (0 : E) 1) : ContractibleSpace ({u}ᶜ : Set (sphere (0 : E) 1)) := by
  have hu : ‖u.val‖ = 1 := by simpa using u.property
  let e := stereographic hu
  have ht : ContractibleSpace e.target := by
    change ContractibleSpace (Set.univ : Set ((ℝ ∙ u.val)ᗮ))
    exact (Homeomorph.Set.univ _).contractibleSpace
  letI := ht
  exact e.toHomeomorphSourceTarget.contractibleSpace

/-- A sphere loop avoiding one point contracts while keeping its basepoint fixed.
Source: Mathlib, stereographic contraction and SimplyConnectedSpace.paths_homotopic. -/
theorem s2e_c11_sphere_loop_avoiding_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u x : sphere (0 : E) 1) (γ : Path x x) (havoid : ∀ t, γ t ≠ u) :
    γ.Homotopic (Path.refl x) := by
  have hx : x ∈ ({u}ᶜ : Set (sphere (0 : E) 1)) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, γ.source] using havoid 0
  letI := s2e_c11_puncturedSphere_contractible u
  let α : Path (⟨x, hx⟩ : ({u}ᶜ : Set (sphere (0 : E) 1))) ⟨x, hx⟩ :=
    { toFun := fun t => ⟨γ t, havoid t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  exact (SimplyConnectedSpace.paths_homotopic α (Path.refl (⟨x, hx⟩ : ({u}ᶜ : Set (sphere (0 : E) 1))))).map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- A unit vector can avoid any finite nonempty family of proper real linear subspaces.
Source: Mathlib, the Baire theorem and the empty interior of proper linear subspaces. -/
theorem s2e_c11_sphere_avoids_finite_subspaces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι]
    (F : ι → Submodule ℝ E) (hF : ∀ i, F i ≠ ⊤) :
    ∃ u : sphere (0 : E) 1, ∀ i, u.val ∉ F i := by
  have hd : ∀ i, Dense (F i : Set E)ᶜ := by
    intro i
    apply interior_eq_empty_iff_dense_compl.mp
    exact Set.not_nonempty_iff_eq_empty.mp
      (fun h => hF i ((F i).eq_top_of_nonempty_interior' h))
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen
    (fun i => (F i).closed_of_finiteDimensional.isOpen_compl) hd).nonempty
  have hxF : ∀ i, x ∉ F i := Set.mem_iInter.mp hx
  have hx₀ : x ≠ 0 := by
    intro h
    exact hxF (Classical.arbitrary ι) (h ▸ (F _).zero_mem)
  refine ⟨s2e_c11_radialNormalize x hx₀, ?_⟩
  intro i hu
  exact hxF i (((F i).smul_mem_iff (inv_ne_zero (norm_ne_zero_iff.mpr hx₀))).mp hu)

/-- Paths avoiding a common sphere point are homotopic with fixed endpoints.
Source: Mathlib, stereographic contraction and SimplyConnectedSpace.paths_homotopic. -/
theorem s2e_c11_sphere_paths_avoiding_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u x y : sphere (0 : E) 1) (γ δ : Path x y)
    (hγ : ∀ t, γ t ≠ u) (hδ : ∀ t, δ t ≠ u) : γ.Homotopic δ := by
  have hx : x ≠ u := γ.source ▸ hγ 0
  have hy : y ≠ u := γ.target ▸ hγ 1
  letI := s2e_c11_puncturedSphere_contractible u
  let α : Path (⟨x, hx⟩ : ({u}ᶜ : Set (sphere (0 : E) 1))) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  let β : Path (⟨x, hx⟩ : ({u}ᶜ : Set (sphere (0 : E) 1))) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨δ t, hδ t⟩
      continuous_toFun := δ.continuous.subtype_mk _
      source' := Subtype.ext δ.source
      target' := Subtype.ext δ.target }
  exact (SimplyConnectedSpace.paths_homotopic α β).map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- A path in a punctured sphere has a homotopic arc contained in a three-vector span.
Source: Mathlib, stereographic projection of a straight line segment. -/
theorem s2e_c11_sphere_path_three_vector_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u x y : sphere (0 : E) 1) (γ : Path x y) (hγ : ∀ t, γ t ≠ u) :
    ∃ a : Fin 3 → E, ∃ δ : Path x y,
      γ.Homotopic δ ∧ ∀ t, (δ t).val ∈ Submodule.span ℝ (Set.range a) := by
  have hu : ‖u.val‖ = 1 := by simpa using u.property
  have hx : x.val ≠ u.val := fun h => hγ 0 (γ.source.trans (Subtype.ext h))
  have hy : y.val ≠ u.val := fun h => hγ 1 (γ.target.trans (Subtype.ext h))
  let z₀ := stereoToFun u.val x.val
  let z₁ := stereoToFun u.val y.val
  let r := Path.segment z₀ z₁
  let δ : Path x y := (r.map (continuous_stereoInvFun hu)).cast
    (stereo_left_inv hu hx).symm (stereo_left_inv hu hy).symm
  let a : Fin 3 → E := ![u.val, z₀.val, z₁.val]
  let F := Submodule.span ℝ (Set.range a)
  have h₀ : u.val ∈ F := Submodule.subset_span ⟨0, rfl⟩
  have h₁ : z₀.val ∈ F := Submodule.subset_span ⟨1, rfl⟩
  have h₂ : z₁.val ∈ F := Submodule.subset_span ⟨2, rfl⟩
  refine ⟨a, δ, s2e_c11_sphere_paths_avoiding_point u x y γ δ hγ
    (fun t => stereoInvFun_ne_north_pole hu (r t)), ?_⟩
  intro t
  change (stereoInvFun hu (r t)).val ∈ F
  rw [stereoInvFun_apply]
  apply F.smul_mem
  apply F.add_mem
  · apply F.smul_mem
    change ((Path.segment z₀ z₁) t : E) ∈ F
    rw [Path.segment_apply, AffineMap.lineMap_apply_module]
    change ((1 - (t : ℝ)) • z₀.val + (t : ℝ) • z₁.val) ∈ F
    exact F.add_mem (F.smul_mem _ h₁) (F.smul_mem _ h₂)
  · exact F.smul_mem _ h₀

/-- Concatenation preserves membership in a set containing all the constituent paths.
Source: Mathlib, Path.concat_succ and Path.trans_apply. -/
theorem s2e_c11_path_concat_mem
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (p : Fin (n + 1) → X) (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (s : Set X) (h₀ : p 0 ∈ s) (hF : ∀ i t, F i t ∈ s) :
    ∀ t, Path.concat p F t ∈ s := by
  induction n with
  | zero => simpa only [Path.concat_zero, Path.refl_apply] using fun _ : unitInterval => h₀
  | succ n ih =>
    intro t
    simp only [Path.concat_succ]
    rw [Path.trans_apply (Path.concat (p ∘ Fin.castSucc) (fun i => F i.castSucc))
      (F (Fin.last n)) t]
    split_ifs
    · exact ih (p ∘ Fin.castSucc) (fun i => F i.castSucc) h₀
        (fun i t => hF i.castSucc t) _
    · exact hF (Fin.last n) _

/-- In ambient real dimension at least four, a sphere loop can be moved off a point.
Source: Hatcher, Algebraic Topology, sphere loop approximation by finitely many chart arcs. -/
theorem s2e_c11_sphere_loop_move_off_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 3 < Module.finrank ℝ E) (x : sphere (0 : E) 1) (γ : Path x x) :
    ∃ δ : Path x x, γ.Homotopic δ ∧ ∃ u : sphere (0 : E) 1, ∀ s, δ s ≠ u := by
  classical
  obtain ⟨t, ht₀, ht, ⟨N, hN⟩, hcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun u : sphere (0 : E) 1 =>
        (isOpen_compl_singleton : IsOpen ({u}ᶜ : Set (sphere (0 : E) 1))).preimage γ.continuous)
      (fun s _ => Set.mem_iUnion.mpr ⟨-(γ s), ne_neg_of_mem_unit_sphere ℝ (γ s)⟩)
  let n := N + 1
  let T : Fin (n + 1) → unitInterval := fun i => t i.val
  have hT₀ : T 0 = 0 := ht₀
  have hTN : T (Fin.last n) = 1 := hN n (by omega)
  have hseg : ∀ j : Fin n, ∃ u : sphere (0 : E) 1,
      ∀ s, γ.subpath (T j.castSucc) (T j.succ) s ≠ u := by
    intro j
    obtain ⟨u, hu⟩ := hcover j.val
    refine ⟨u, ?_⟩
    intro s
    have hm : γ.subpath (T j.castSucc) (T j.succ) s ∈
        γ '' Set.Icc (T j.castSucc) (T j.succ) := by
      rw [← γ.range_subpath_of_le (T j.castSucc) (T j.succ)
        (show T j.castSucc ≤ T j.succ from ht (Nat.le_succ j.val))]
      exact Set.mem_range_self s
    obtain ⟨r, hr, he⟩ := hm
    exact he ▸ hu hr
  choose u hu using hseg
  choose a δ hhom hspan using fun j => s2e_c11_sphere_path_three_vector_span
    (u j) _ _ (γ.subpath (T j.castSucc) (T j.succ)) (hu j)
  let F : Fin n → Submodule ℝ E := fun j => Submodule.span ℝ (Set.range (a j))
  have hproper : ∀ j, F j ≠ ⊤ := by
    intro j he
    have hle := finrank_le_of_span_eq_top he
    have hle' : Module.finrank ℝ E ≤ 3 := by simpa using hle
    omega
  letI : NeZero n := ⟨by dsimp [n]; omega⟩
  obtain ⟨z, hz⟩ := s2e_c11_sphere_avoids_finite_subspaces F hproper
  have hδ : ∀ j s, δ j s ≠ z := by
    intro j s he
    exact hz j (he ▸ hspan j s)
  have hbase : γ (T 0) ≠ z := (δ (0 : Fin n)).source ▸ hδ 0 0
  have hconcat : ∀ s, Path.concat (γ ∘ T) δ s ≠ z :=
    s2e_c11_path_concat_mem (γ ∘ T) δ {z}ᶜ hbase hδ
  have hstart : x = γ (T 0) := by rw [hT₀, γ.source]
  have hend : x = γ (T (Fin.last n)) := by rw [hTN, γ.target]
  let β : Path x x := (Path.concat (γ ∘ T) δ).cast hstart hend
  have hsub := (Path.Homotopic.concat_subpath γ T).pathCast hstart hend
  have heq : (γ.subpath (T 0) (T (Fin.last n))).cast hstart hend = γ := by
    apply Path.ext
    funext s
    change γ (Set.Icc.convexComb (T 0) (T (Fin.last n)) s) = γ s
    rw [hT₀, hTN]
    simp
  rw [heq] at hsub
  have hreplacement := (Path.Homotopic.concat_hcomp (γ ∘ T)
    (fun j => γ.subpath (T j.castSucc) (T j.succ)) δ hhom).pathCast hstart hend
  exact ⟨β, hsub.symm.trans hreplacement, z, hconcat⟩

/-- Unit spheres in real inner product spaces of ambient dimension at least four are simply connected.
Source: Hatcher, Algebraic Topology, sphere loop approximation and stereographic contraction. -/
theorem s2e_c11_realSphere_simplyConnected
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : 3 < Module.finrank ℝ E) : SimplyConnectedSpace (sphere (0 : E) 1) := by
  have hr : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  letI : PathConnectedSpace (sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hr _ zero_le_one)
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x γ
  obtain ⟨δ, hγ, u, hδ⟩ := s2e_c11_sphere_loop_move_off_point hd x γ
  exact hγ.trans (s2e_c11_sphere_loop_avoiding_point u x δ hδ)

end HodgeLean.Foundations.Program
