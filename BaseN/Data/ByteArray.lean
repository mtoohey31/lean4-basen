import BaseN.Data.Array

namespace ByteArray

abbrev Unique (a : ByteArray) := a.data.Unique

instance : Decidable (ByteArray.Unique a) := Array.decUnique a.data

instance : BEq ByteArray := ⟨(·.data == ·.data)⟩

end ByteArray
