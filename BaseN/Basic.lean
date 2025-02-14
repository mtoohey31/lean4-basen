import BaseN.Data.BitVec
import BaseN.Data.ByteArray
import BaseN.Data.List
import BaseN.Data.Stream
import BaseN.Data.SizedStream
import Mathlib.Data.Int.GCD

namespace BaseN

open Stream
open SizedStream

namespace Encoding

abbrev Base := { w : Nat // 0 < w }

namespace Base

def values (base : Base) := 2 ^ base.val

def quantum_length (base : Base) := Nat.lcm 8 base

def «8» : Base := ⟨3, Nat.succ_pos _⟩

def «16» : Base := ⟨4, Nat.succ_pos _⟩

def «32» : Base := ⟨5, Nat.succ_pos _⟩

def «64» : Base := ⟨6, Nat.succ_pos _⟩

end Base

private
inductive DecodeEntry (w : Nat) : (padding? : Option Char) → Type where
  | invalid : DecodeEntry _ _
  | valid : BitVec w → DecodeEntry _ _
  | padding : DecodeEntry _ (some _)

structure _root_.BaseN.Encoding where private mk' ::
  base : Base
  encode : Vector Char base.values
  encode_unique : encode.Unique
  encode_bound : Nat
  encode_bound_gt : ∀ c ∈ encode, c.toNat < encode_bound
  padding? : Option Char
  padding?_eq_none_of_unusable : base.val ∣ 8 → padding? = none
  strict : Bool
  decode : Vector (DecodeEntry base padding?) encode_bound

def mk (base : Base := .«64») (encode : Vector Char base.values)
  (encode_unique : encode.Unique := by decide +kernel)
  (padding? : Option Char := some '=')
  (padding?_eq_none_of_unusable : base.val ∣ 8 → padding? = none := by decide +kernel)
  (strict := false) : Encoding :=
  let encode_bound := (encode.toList.map (·.val.toNat)).max?.getD 0 + 1
  let encode_bound_gt : ∀ c ∈ encode, c.toNat < encode_bound := by
    intro c mem
    dsimp [encode_bound]
    match encode with
    | ⟨⟨[]⟩, _⟩ => nomatch mem
    | ⟨⟨c' :: encode'⟩, _⟩ =>
      rw [List.map_cons]
      let ⟨_, eq⟩ := (List.exists_some_eq_max?_iff
          (l := c'.val.toNat :: encode'.map (·.val.toNat))).mp (List.cons_ne_nil _ _)
      symm at eq
      let ⟨_, le⟩ := List.max?_eq_some_iff'.mp eq
      rw [eq, Option.getD_some]
      apply Nat.lt_succ_of_le
      apply le
      let .mk (.mk mem') := mem
      simp only at mem'
      match mem' with
      | .head _ => exact .head _
      | .tail _ mem'' => exact .tail _ <| List.mem_map.mpr ⟨_, mem'', rfl⟩
  let decode := Vector.ofFn (α := DecodeEntry base padding?) fun (i : Fin encode_bound) =>
    if h : some (Char.ofNat i) = padding? then
      by cases h; exact .padding
    else if let some b := encode.indexOf? (Char.ofNat i.val) then
      .valid b
    else
      .invalid
  {
    base,
    encode,
    encode_unique,
    encode_bound,
    encode_bound_gt,
    padding?,
    padding?_eq_none_of_unusable,
    strict,
    decode
  }

def ofString (encode : String) (base := encode.length.log2)
  (base_pos : 0 < base := by decide +kernel)
  (encode_length : encode.length = 2 ^ base := by decide +kernel)
  (encode_unique : encode.toList.toArray.Unique := by decide +kernel)
  (padding? : Option Char := some '=')
  (padding?_eq_none_of_unusable : base ∣ 8 → padding? = none := by decide +kernel)
  (strict := false) : Encoding :=
  mk ⟨base, base_pos⟩ ⟨encode.toList.toArray, encode_length⟩ encode_unique padding?
    padding?_eq_none_of_unusable strict

def «8» : Encoding := ofString "01234567"

def «16» : Encoding := ofString "0123456789ABCDEF" (padding? := none)

def «32_hex» : Encoding := ofString "0123456789ABCDEFGHIJKLMNOPQRSTUV"

def raw_32_hex : Encoding := ofString "0123456789ABCDEFGHIJKLMNOPQRSTUV" (padding? := none)

def «32» : Encoding := ofString "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

def raw_32 : Encoding := ofString "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567" (padding? := none)

def «64» : Encoding := ofString
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

def raw_64 : Encoding := ofString
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" (padding? := none)

def «64_url» : Encoding := ofString
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

def raw_64_url : Encoding := ofString
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_" (padding? := none)

def asStrict (enc : Encoding) : Encoding := { enc with strict := true }

end Encoding

def encode [ToStream α ρ] [SizedStream ρ UInt8] (bs : α) (enc : Encoding := .«64») : String :=
  go <| toStream bs
where
  go (bs : ρ) (num_unused : Fin enc.base := ⟨0, enc.base.property⟩)
    (unused : BitVec num_unused := 0) (acc : String := "") : String :=
    match h : next? bs with
    | none =>
      if num_unused.val = 0 then
        acc
      else
        let ⟨v, vlt⟩ := unused.shiftLeftZeroExtend (enc.base.val - num_unused) |>.toFin
        let vlt' : v < enc.base.values := by
          rw [← Nat.add_sub_assoc (Nat.le_of_lt num_unused.isLt), Nat.add_comm,
              Nat.add_sub_cancel] at vlt
          exact vlt
        let acc := acc.push enc.encode[v]
        if let some padding := enc.padding? then
          let gcd := Nat.gcd enc.base 8
          let m := 8 / gcd
          let r := num_unused / gcd
          let b := enc.base / gcd
          let binv := (Nat.gcdA b m).emod m
          acc.pushn '=' <| Int.toNat <| (Int.ofNat r - Int.ofNat b) * binv |>.emod m
        else
          acc
    | some (b, bs) =>
      let ready := b.toBitVec.setWidth' (Nat.le_add_left ..) ||| unused.shiftLeftZeroExtend 8
      go' bs (num_unused + 8) ready acc
  termination_by 10 * size bs + num_unused
  decreasing_by
    all_goals simp_arith
    rename SizedStream .. => inst
    rcases Nat.exists_eq_add_of_lt <| inst.sizeDec h with ⟨_, eq⟩
    rw [eq, Nat.mul_add, Nat.mul_add, Nat.add_assoc, Nat.mul_one]
    exact Nat.add_le_add_iff_left.mpr <| Nat.le_add_left ..

  go' (bs : ρ) (num_ready : Nat) (ready : BitVec num_ready) (acc : String) : String :=
    if h : num_ready < enc.base then
      go bs ⟨num_ready, h⟩ ready acc
    else
      let ⟨v, _⟩ : Fin enc.base.values := by
        have := ready.shiftRightShrink (num_ready - enc.base.val)
        rw [Nat.sub_sub_eq_min, Nat.min_eq_right (Nat.le_of_not_lt h)] at this
        exact this.toFin
      go' bs (num_ready - enc.base.val) (.ofNat _ ready.toNat) <| acc.push enc.encode[v]
  termination_by 10 * size bs + num_ready + 1
  decreasing_by
    all_goals simp
    exact Nat.sub_lt_self enc.base.property <| Nat.le_of_not_lt h

private
def assertEncodesTo (s expected : String) (enc : Encoding := .«64») : Lean.Elab.TermElabM Unit :=
  let actual := encode s.toUTF8 enc
  if actual == expected then pure () else throwError s!"expected: {expected}, got: {actual}"

-- Source: https://www.rfc-editor.org/rfc/rfc4648.html#section-9
#eval assertEncodesTo "" ""
#eval assertEncodesTo "f" "Zg=="
#eval assertEncodesTo "fo" "Zm8="
#eval assertEncodesTo "foo" "Zm9v"
#eval assertEncodesTo "foob" "Zm9vYg=="
#eval assertEncodesTo "fooba" "Zm9vYmE="
#eval assertEncodesTo "foobar" "Zm9vYmFy"
#eval assertEncodesTo "" "" .«32»
#eval assertEncodesTo "f" "MY======" .«32»
#eval assertEncodesTo "fo" "MZXQ====" .«32»
#eval assertEncodesTo "foo" "MZXW6===" .«32»
#eval assertEncodesTo "foob" "MZXW6YQ=" .«32»
#eval assertEncodesTo "fooba" "MZXW6YTB" .«32»
#eval assertEncodesTo "foobar" "MZXW6YTBOI======" .«32»
#eval assertEncodesTo "" "" .«32_hex»
#eval assertEncodesTo "f" "CO======" .«32_hex»
#eval assertEncodesTo "fo" "CPNG====" .«32_hex»
#eval assertEncodesTo "foo" "CPNMU===" .«32_hex»
#eval assertEncodesTo "foob" "CPNMUOG=" .«32_hex»
#eval assertEncodesTo "fooba" "CPNMUOJ1" .«32_hex»
#eval assertEncodesTo "foobar" "CPNMUOJ1E8======" .«32_hex»
#eval assertEncodesTo "" "" .«16»
#eval assertEncodesTo "f" "66" .«16»
#eval assertEncodesTo "fo" "666F" .«16»
#eval assertEncodesTo "foo" "666F6F" .«16»
#eval assertEncodesTo "foob" "666F6F62" .«16»
#eval assertEncodesTo "fooba" "666F6F6261" .«16»
#eval assertEncodesTo "foobar" "666F6F626172" .«16»

#eval assertEncodesTo "" "" .raw_64
#eval assertEncodesTo "f" "Zg" .raw_64
#eval assertEncodesTo "fo" "Zm8" .raw_64
#eval assertEncodesTo "foo" "Zm9v" .raw_64
#eval assertEncodesTo "foob" "Zm9vYg" .raw_64
#eval assertEncodesTo "fooba" "Zm9vYmE" .raw_64
#eval assertEncodesTo "foobar" "Zm9vYmFy" .raw_64
#eval assertEncodesTo "" "" .raw_32
#eval assertEncodesTo "f" "MY" .raw_32
#eval assertEncodesTo "fo" "MZXQ" .raw_32
#eval assertEncodesTo "foo" "MZXW6" .raw_32
#eval assertEncodesTo "foob" "MZXW6YQ" .raw_32
#eval assertEncodesTo "fooba" "MZXW6YTB" .raw_32
#eval assertEncodesTo "foobar" "MZXW6YTBOI" .raw_32
#eval assertEncodesTo "" "" .raw_32_hex
#eval assertEncodesTo "f" "CO" .raw_32_hex
#eval assertEncodesTo "fo" "CPNG" .raw_32_hex
#eval assertEncodesTo "foo" "CPNMU" .raw_32_hex
#eval assertEncodesTo "foob" "CPNMUOG" .raw_32_hex
#eval assertEncodesTo "fooba" "CPNMUOJ1" .raw_32_hex
#eval assertEncodesTo "foobar" "CPNMUOJ1E8" .raw_32_hex

inductive DecodeError : (padding strict : Bool) → Type where
  | unknownChar : Char → DecodeError _ _
  | unexpectedEnd : DecodeError true _
  | unexpectedPadding : DecodeError true _
  | expectedPadding : Char → DecodeError true _
  | nonZeroPaddingBits : DecodeError _ true
deriving BEq

instance : ToString (DecodeError padding strict) where
  toString
    | .unknownChar c => s!"unknown character {c}"
    | .unexpectedEnd => "unexpected end of input; expected padding chars to complete quantum"
    | .unexpectedPadding => "unexpected padding character at start of quantum"
    | .expectedPadding c => "unexpected character {c}; expected padding chars to complete quantum"
    | .nonZeroPaddingBits =>
      "padding bits contained non-zero entries; this may be indicative of corrupted data, a buggy encoder, or a covert channel attack"

def decode [ToStream α ρ] [SizedStream ρ Char] (cs : α) (enc : Encoding := .«64») :
  Except (DecodeError enc.padding?.isSome enc.strict) ByteArray := go <| toStream cs
where
  go (cs : ρ) (num_unused : Fin 8 := ⟨0, Nat.succ_pos _⟩) (unused : BitVec num_unused := 0)
    (acc : ByteArray := ByteArray.mkEmpty (size cs)) :=
    match h : next? cs with
    | none =>
      if num_unused == 0 then
        .ok acc
      else if h' : enc.strict && unused != 0 then by
        rw [Bool.and_eq_true_iff.mp h' |>.left]
        exact .error .nonZeroPaddingBits
      else if let some padding := enc.padding? then
        .error .unexpectedEnd
      else
        .ok acc
    | some (c, cs) =>
      if h' : c.toNat < enc.encode_bound then
        match h'' : enc.padding?, enc.decode[c.toNat] with
        | _, .invalid => .error <| .unknownChar c
        | _, .valid x =>
          let .refl _ := h''
          let unused := x.setWidth' (Nat.le_add_left ..) ||| unused.shiftLeftZeroExtend enc.base
          if h''' : num_unused.val + enc.base < 8 then
            go cs ⟨num_unused.val + enc.base, h'''⟩ unused acc
          else
            go' cs (num_unused.val + enc.base) unused acc
        | .some _, .padding =>
          if num_unused == 0 then
            .error .unexpectedPadding
          else if h' : enc.strict && unused != 0 then by
            rw [Bool.and_eq_true_iff.mp h' |>.left]
            exact .error .nonZeroPaddingBits
          else
            let gcd := Nat.gcd enc.base 8
            let m := 8 / gcd
            let r := num_unused / gcd
            let b := enc.base / gcd
            let binv := (Nat.gcdA b m).emod m
            go'' cs acc <| Int.toNat <| -(b + r) * binv |>.emod m
      else
        .error <| .unknownChar c
  termination_by (enc.base + 2) * size cs + num_unused
  decreasing_by
    · simp_arith
      rename SizedStream .. => inst
      rcases Nat.exists_eq_add_of_lt <| inst.sizeDec h with ⟨_, eq⟩
      rw [eq, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.add_assoc, Nat.add_assoc]
      apply Nat.add_le_add_iff_left.mpr
      apply Nat.le_trans _ <| Nat.le_add_left ..
      exact Nat.add_le_add_iff_left.mpr <| Nat.le.refl.step
    · simp_arith
      rename SizedStream .. => inst
      rcases Nat.exists_eq_add_of_lt <| inst.sizeDec h with ⟨_, eq⟩
      rw [eq, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.add_assoc, Nat.add_assoc]
      apply Nat.add_le_add_iff_left.mpr
      apply Nat.le_trans _ <| Nat.le_add_left ..
      exact Nat.add_le_add_iff_left.mpr <| Nat.le.refl

  go' (cs : ρ) (num_ready : Nat) (ready : BitVec num_ready) (acc : ByteArray) :=
    if h : num_ready < 8 then
      go cs ⟨num_ready, h⟩ ready acc
    else
      let b : UInt8 := by
        apply UInt8.mk
        rw [← Nat.min_eq_right (Nat.le_of_not_lt h), ← Nat.sub_sub_eq_min]
        exact ready.shiftRightShrink (num_ready - 8)
      go' cs (num_ready - 8) (.ofNat _ ready.toNat) <| acc.push b
  termination_by (enc.base + 2) * size cs + num_ready + 1

  go'' (cs : ρ) (acc : ByteArray) (n : Nat) :=
    match n, next? cs with
    | 0, _ => Except.ok acc
    | n' + 1, some (c, cs) => if some c = enc.padding? then
        go'' cs acc n'
      else
        .error <| DecodeError.expectedPadding c
    | _, none => .error .unexpectedEnd

private
def assertDecodesTo (s expected : String) (enc : Encoding := .«64») : Lean.Elab.TermElabM Unit :=
  let actual := decode s enc
  match actual with
  | .ok actual => if actual == expected.toUTF8 then
      pure ()
    else
      throwError s!"expected: {expected}, got: {actual}"
  | .error _ => throwError "decoding failed"

#eval assertDecodesTo "" ""
#eval assertDecodesTo "Zg==" "f"
#eval assertDecodesTo "Zm8=" "fo"
#eval assertDecodesTo "Zm9v" "foo"
#eval assertDecodesTo "Zm9vYg==" "foob"
#eval assertDecodesTo "Zm9vYmE=" "fooba"
#eval assertDecodesTo "Zm9vYmFy" "foobar"
#eval assertDecodesTo "" "" .«32»
#eval assertDecodesTo "MY======" "f" .«32»
#eval assertDecodesTo "MZXQ====" "fo" .«32»
#eval assertDecodesTo "MZXW6===" "foo" .«32»
#eval assertDecodesTo "MZXW6YQ=" "foob" .«32»
#eval assertDecodesTo "MZXW6YTB" "fooba" .«32»
#eval assertDecodesTo "MZXW6YTBOI======" "foobar" .«32»
#eval assertDecodesTo "" "" .«32_hex»
#eval assertDecodesTo "CO======" "f" .«32_hex»
#eval assertDecodesTo "CPNG====" "fo" .«32_hex»
#eval assertDecodesTo "CPNMU===" "foo" .«32_hex»
#eval assertDecodesTo "CPNMUOG=" "foob" .«32_hex»
#eval assertDecodesTo "CPNMUOJ1" "fooba" .«32_hex»
#eval assertDecodesTo "CPNMUOJ1E8======" "foobar" .«32_hex»
#eval assertDecodesTo "" "" .«16»
#eval assertDecodesTo "66" "f" .«16»
#eval assertDecodesTo "666F" "fo" .«16»
#eval assertDecodesTo "666F6F" "foo" .«16»
#eval assertDecodesTo "666F6F62" "foob" .«16»
#eval assertDecodesTo "666F6F6261" "fooba" .«16»
#eval assertDecodesTo "666F6F626172" "foobar" .«16»

#eval assertDecodesTo "" "" .raw_64
#eval assertDecodesTo "Zg" "f" .raw_64
#eval assertDecodesTo "Zm8" "fo" .raw_64
#eval assertDecodesTo "Zm9v" "foo" .raw_64
#eval assertDecodesTo "Zm9vYg" "foob" .raw_64
#eval assertDecodesTo "Zm9vYmE" "fooba" .raw_64
#eval assertDecodesTo "Zm9vYmFy" "foobar" .raw_64
#eval assertDecodesTo "" "" .raw_32
#eval assertDecodesTo "MY" "f" .raw_32
#eval assertDecodesTo "MZXQ" "fo" .raw_32
#eval assertDecodesTo "MZXW6" "foo" .raw_32
#eval assertDecodesTo "MZXW6YQ" "foob" .raw_32
#eval assertDecodesTo "MZXW6YTB" "fooba" .raw_32
#eval assertDecodesTo "MZXW6YTBOI" "foobar" .raw_32
#eval assertDecodesTo "" "" .raw_32_hex
#eval assertDecodesTo "CO" "f" .raw_32_hex
#eval assertDecodesTo "CPNG" "fo" .raw_32_hex
#eval assertDecodesTo "CPNMU" "foo" .raw_32_hex
#eval assertDecodesTo "CPNMUOG" "foob" .raw_32_hex
#eval assertDecodesTo "CPNMUOJ1" "fooba" .raw_32_hex
#eval assertDecodesTo "CPNMUOJ1E8" "foobar" .raw_32_hex

private
def assertDecodeFailsWith (s : String) (enc : Encoding := .«64»)
  (expected : DecodeError enc.padding?.isSome enc.strict) : Lean.Elab.TermElabM Unit :=
  let actual := decode s enc
  match actual with
  | .ok _ => throwError "decoding succeeded"
  | .error actual => if actual == expected then
      pure ()
    else
      throwError s!"expected: {expected}, got: {actual}"

#eval assertDecodeFailsWith "Z+" (.asStrict .«64») .nonZeroPaddingBits
#eval assertDecodeFailsWith "MY" .«32» .unexpectedEnd
#eval assertDecodeFailsWith "666F6F626Z72" .«16» <| .unknownChar 'Z'
#eval assertDecodeFailsWith "CPNMUOJ1=" .«32_hex» .unexpectedPadding
#eval assertDecodeFailsWith "Z+==" (.asStrict .«64») .nonZeroPaddingBits
#eval assertDecodeFailsWith "ず" .«64_url» <| .unknownChar 'ず'
#eval assertDecodeFailsWith "CPNMU=U=" .«32_hex» <| .expectedPadding 'U'
#eval assertDecodeFailsWith "MZXW6YTBOI=====" .«32» .unexpectedEnd

end BaseN
