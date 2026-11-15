import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousPrimeAvoidance

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_proj_positive_witness
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (x : Proj 𝒜) :
    ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ f ∉ x.asHomogeneousIdeal.toIdeal := by
  let C := Proj.affineOpenCover 𝒜
  let i := C.idx x
  have hx := C.covers x
  change x ∈ (Proj.awayι 𝒜 i.2.1 i.2.2 i.1.2).opensRange at hx
  rw [Proj.opensRange_awayι] at hx
  exact ⟨i.1, i.2, i.1.2, i.2.2, hx⟩

lemma s2v_i1ahi_proj_finite_affine_neighborhood
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Finset (Proj 𝒜)) :
    ∃ U : (Proj 𝒜).Opens, IsAffineOpen U ∧ ∀ x ∈ s, x ∈ U := by
  classical
  let t := s.image (fun x => x.asHomogeneousIdeal.toIdeal)
  obtain ⟨d, f, hd, hf, hn⟩ := s2v_i1ahi_finite_homogeneous_prime_avoidance 𝒜 t
    (fun P hP => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
      exact x.asHomogeneousIdeal.isHomogeneous)
    (fun P hP => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
      exact x.isPrime)
    (fun P hP => by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
      exact s2v_i1ahi_proj_positive_witness 𝒜 x)
  exact ⟨Proj.basicOpen 𝒜 f, Proj.isAffineOpen_basicOpen 𝒜 f hf hd,
    fun x hx => hn _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

end HodgeLean.Foundations.Program
