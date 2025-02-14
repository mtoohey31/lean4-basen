open Stream

class SizedStream (ρ : Type u) (α : outParam (Type v)) extends Stream ρ α where
  size : ρ → Nat
  sizeDec : ∀ {x xs xs'}, next? xs = some (x, xs') → size xs' < size xs

instance : SizedStream Substring Char where
  size ss := ss.stopPos.byteIdx - ss.startPos.byteIdx
  sizeDec eq := by
    dsimp [next?] at eq
    split at eq
    · case isTrue h =>
      rcases Prod.mk.inj <| Option.some_inj.mp eq with ⟨rfl, rfl⟩
      exact Nat.sub_lt_sub_left h <| String.lt_next ..
    · case isFalse h => nomatch eq

instance : SizedStream (List α) α where
  size := List.length
  sizeDec eq := by
    dsimp [next?] at eq
    split at eq
    · nomatch eq
    · rcases Prod.mk.inj <| Option.some_inj.mp eq with ⟨rfl, rfl⟩
      rw [List.length_cons]
      exact Nat.lt_succ_self _

instance : SizedStream (Subarray α) α where
  size := Subarray.size
  sizeDec eq := by
    dsimp [next?] at eq
    split at eq
    · case isTrue h =>
      rcases Prod.mk.inj <| Option.some_inj.mp eq with ⟨rfl, rfl⟩
      rw [Subarray.size, Subarray.size, Nat.sub_succ]
      exact Nat.pred_lt_of_lt <| Nat.sub_pos_of_lt h
    · case isFalse => nomatch eq
