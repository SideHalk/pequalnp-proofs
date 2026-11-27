import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_7866_72
    (coverBudget : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → (∃ u v, G.Adj u v) → IsLeastAO G C → TopForm G C →
      (junk G C).Nonempty →
      ∃ (T : Finset (Fin n)) (B : Finset (Finset (Fin n))),
        (∀ e ∈ G.edgeSet, (∃ v ∈ T, v ∈ e) ∨ ∃ s ∈ B, e.toFinset ⊆ s) ∧
        G.edgeSet.ncard + (T.card + ∑ s ∈ B, s.card / 2) ≤ C.size + 1 + c * (n + 1).sqrt)
    (matchingBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n)))
      (T : Finset (Fin n)) (B : Finset (Finset (Fin n))),
      (∀ e ∈ M, e ∈ G.edgeSet) →
      (∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f) →
      (∀ e ∈ G.edgeSet, (∃ v ∈ T, v ∈ e) ∨ ∃ s ∈ B, e.toFinset ⊆ s) →
      M.card ≤ T.card + ∑ s ∈ B, s.card / 2) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (M : Finset (Sym2 (Fin n))),
      NoFourCycle G → (∃ u v, G.Adj u v) → IsLeastAO G C → TopForm G C →
      (junk G C).Nonempty → (∀ e ∈ M, e ∈ G.edgeSet) →
      (∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f) →
      G.edgeSet.ncard + M.card ≤ C.size + 1 + c * (n + 1).sqrt := by
  obtain ⟨c, cover⟩ := coverBudget
  refine ⟨c, ?_⟩
  intro n G inst C M h4 he least top dirty sub disj
  obtain ⟨T, B, hits, budget⟩ := cover n G C h4 he least top dirty
  exact (Nat.add_le_add_left (matchingBound n G M T B sub disj hits) _).trans budget
