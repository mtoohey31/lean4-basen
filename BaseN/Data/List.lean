theorem List.exists_some_eq_max?_iff [Max α] : l ≠ [] ↔ ∃ x : α, some x = l.max? where
  mp lne := by
    rcases List.ne_nil_iff_exists_cons.mp lne with ⟨_, _, rfl⟩
    rw [max?]
    exact ⟨_, rfl⟩
  mpr
    | ⟨_, eq⟩ => by
      rintro rfl
      rw [max?] at eq
      nomatch eq
