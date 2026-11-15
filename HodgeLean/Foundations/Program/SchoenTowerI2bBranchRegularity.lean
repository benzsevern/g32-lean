import HodgeLean.Foundations.Program.SchoenTowerI2bCoordinateRegular

/-! Regularity of the actual retained branch sections.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Three distinct retained etale branch coordinates supply both selected pairs and both unpaired triples.
Source: etale transport of distinct polynomial coordinate sequences. -/
theorem s2v_i2b_retained_branch_regular_sequences
    {ι F R : Type*} [DecidableEq ι] [CommRing F] [CommRing R]
    (n : ℕ) (c : MvPolynomial (Fin n) F →+* R) (hc : c.Etale)
    (J : Finset ι) (κ : J ↪ Fin n) (z : ι → R)
    (hz : ∀ s : J, z s = c (MvPolynomial.X (κ s)))
    (a b t : J) (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    RingTheory.Sequence.IsWeaklyRegular R [z b, z a] ∧
    RingTheory.Sequence.IsWeaklyRegular R [z a, z b] ∧
    RingTheory.Sequence.IsWeaklyRegular R [z t, z b, z a] ∧
    RingTheory.Sequence.IsWeaklyRegular R [z t, z a, z b] := by
  have hkab : κ a ≠ κ b := fun he => hab (κ.injective he)
  have hkta : κ t ≠ κ a := fun he => hta (κ.injective he)
  have hktb : κ t ≠ κ b := fun he => htb (κ.injective he)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := s2v_i2b_etale_coordinate_list_weakly_regular c hc [κ b, κ a]
      (by simp [Ne.symm hkab])
    simpa only [List.map_cons, List.map_nil, ← hz a, ← hz b] using hr
  · have hr := s2v_i2b_etale_coordinate_list_weakly_regular c hc [κ a, κ b]
      (by simp [hkab])
    simpa only [List.map_cons, List.map_nil, ← hz a, ← hz b] using hr
  · have hr := s2v_i2b_etale_coordinate_list_weakly_regular c hc [κ t, κ b, κ a]
      (by simp [hkta, hktb, Ne.symm hkab])
    simpa only [List.map_cons, List.map_nil, ← hz a, ← hz b, ← hz t] using hr
  · have hr := s2v_i2b_etale_coordinate_list_weakly_regular c hc [κ t, κ a, κ b]
      (by simp [hkta, hktb, hkab])
    simpa only [List.map_cons, List.map_nil, ← hz a, ← hz b, ← hz t] using hr

end HodgeLean.Foundations.Program
