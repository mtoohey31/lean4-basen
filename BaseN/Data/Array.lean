import Batteries.Data.Array

namespace Array

def Unique (a : Array α) := ∀ i j, (_ : i < a.size) → (_ : j < a.size) → i ≠ j → a[i] ≠ a[j]

def decUnique [DecidableEq α] (a : Array α) : Decidable (Unique a) := open Classical in match a with
  | ⟨[]⟩ => isTrue fun _ _ ltzero => nomatch ltzero
  | ⟨x :: a'⟩ => match decUnique ⟨a'⟩ with
    | isTrue h => match h' : a'.indexOf? x with
      | some j =>
        isFalse <| not_forall.mpr ⟨0, not_forall.mpr ⟨j.succ, not_forall.mpr ⟨
          by rw [Array.size, List.length_cons]; exact Nat.zero_lt_succ _,
          let ⟨jlt, eq, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h'
          not_forall.mpr ⟨
            by rw [Array.size, List.length_cons]; exact Nat.succ_lt_succ jlt,
            not_imp.mpr ⟨
              Nat.zero_ne_add_one _,
              by
                rw [not_not, List.getElem_toArray, List.getElem_toArray, List.getElem_cons_zero,
                    List.getElem_cons_succ]
                rw [beq_iff_eq] at eq
                symm
                exact eq
            ⟩
          ⟩
        ⟩⟩⟩
      | none =>
        isTrue <| fun i j ilt jlt inej => by
          rw [List.getElem_toArray, List.getElem_toArray]
          match i, j with
          | 0, 0 => nomatch inej
          | i' + 1, 0 =>
            rw [List.getElem_cons_zero, List.getElem_cons_succ]
            apply beq_eq_false_iff_ne.mp
            let i'lt := Nat.lt_of_succ_lt_succ ilt
            exact List.findIdx?_eq_none_iff.mp h' a'[i'] <| List.getElem_mem i'lt
          | 0, j' + 1 =>
            rw [List.getElem_cons_zero, List.getElem_cons_succ]
            symm
            apply beq_eq_false_iff_ne.mp
            let j'lt := Nat.lt_of_succ_lt_succ jlt
            exact List.findIdx?_eq_none_iff.mp h' a'[j'] <| List.getElem_mem j'lt
          | i' + 1, j' + 1 =>
            rw [List.getElem_cons_succ, List.getElem_cons_succ, ← List.getElem_toArray,
                ← List.getElem_toArray]
            exact h i' j' (Nat.lt_of_succ_lt_succ ilt) (Nat.lt_of_succ_lt_succ jlt)
              (inej <| Nat.succ_inj'.mpr ·)
    | isFalse h => isFalse <|
      let ⟨i, h'⟩ := not_forall.mp h
      let ⟨j, h''⟩ := not_forall.mp h'
      let ⟨ilt, h'''⟩ := not_forall.mp h''
      let ⟨jlt, h''''⟩ := not_forall.mp h'''
      let ⟨inej, ne⟩ := not_imp.mp h''''
      not_forall.mpr ⟨i.succ, not_forall.mpr ⟨j.succ, not_forall.mpr ⟨
        by
          rw [Array.size] at ilt ⊢
          rw [List.length_cons]
          exact Nat.succ_lt_succ ilt,
        not_forall.mpr ⟨
          by
            rw [Array.size] at ilt ⊢
            rw [List.length_cons]
            exact Nat.succ_lt_succ jlt,
          not_imp.mpr ⟨(inej <| Nat.succ_inj'.mp ·), ne⟩
        ⟩
      ⟩⟩⟩

instance [DecidableEq α] {a : Array α} : Decidable (Unique a) := decUnique a

end Array
