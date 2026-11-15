import HodgeLean.Foundations.Program.G32Native.PELConjugationFibres

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable {k : Type*} [Field k] {n : ℕ}

/-- A finite subgroup normalized by a Zariski-preconnected matrix subgroup
commutes with that subgroup. -/
theorem pel_finite_normalized_central
    (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : (H : Set (Matrix.GeneralLinearGroup (Fin n) k)).Finite)
    (hK : @IsPreconnected _ (g1_zariski k n) (K : Set _))
    (hn : ∀ g ∈ K, ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : Matrix.GeneralLinearGroup (Fin n) k) (hx : x ∈ H)
    (g : Matrix.GeneralLinearGroup (Fin n) k) (hg : g ∈ K) : Commute x g := by
  let _ := g1_zariski k n
  letI := g1_t1Space (k := k) (n := n)
  letI : Finite H := hH.to_subtype
  letI : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let f : K → H := fun a => ⟨(a : Matrix.GeneralLinearGroup (Fin n) k)⁻¹ * x * a,
    hn a a.property x hx⟩
  have hfib (y : H) : IsClosed (f ⁻¹' {y}) := by
    convert (pel_isClosed_conjugation_fibre x y).preimage
      (continuous_subtype_val : Continuous (fun a : K => (a : Matrix.GeneralLinearGroup (Fin n) k))) using 1
    ext a
    exact Subtype.ext_iff
  have hf : Continuous f := by
    apply continuous_iff_isClosed.mpr
    intro s _
    rw [← Set.biUnion_preimage_singleton]
    exact (Set.toFinite s).isClosed_biUnion (fun y _ => hfib y)
  have hi := (isPreconnected_univ.image f hf.continuousOn).subsingleton
    (Set.mem_image_of_mem f (Set.mem_univ (⟨g, hg⟩ : K)))
    (Set.mem_image_of_mem f (Set.mem_univ (1 : K)))
  have heq : g⁻¹ * x * g = x := by
    have h := congrArg Subtype.val hi
    simpa only [f, OneMemClass.coe_one, inv_one, one_mul, mul_one] using h
  change x * g = g * x
  have h := congrArg (fun z => g * z) heq
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h

/-- Noncentrality in a normalized intersection excludes finite intersections
in the actual Zariski topology. -/
theorem pel_zariski_normal_intersection_infinite
    (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hK : @IsPreconnected _ (g1_zariski k n) (K : Set _))
    (hn : ∀ g ∈ K, ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : Matrix.GeneralLinearGroup (Fin n) k) (hx : x ∈ H) (hxK : x ∈ K)
    (hnoncentral : ∃ g ∈ K, ¬ Commute x g) :
    ((H ⊓ K : Subgroup _) : Set (Matrix.GeneralLinearGroup (Fin n) k)).Infinite := by
  intro hf
  obtain ⟨g, hg, hng⟩ := hnoncentral
  apply hng
  apply pel_finite_normalized_central (H ⊓ K) K hf hK _ x ⟨hx, hxK⟩ g hg
  intro a ha y hy
  exact ⟨hn a ha y hy.1, K.mul_mem (K.mul_mem (K.inv_mem ha) hy.2) ha⟩

#print axioms pel_finite_normalized_central
#print axioms pel_zariski_normal_intersection_infinite
end HodgeLean.Foundations.Program.GeneralTypeIII
