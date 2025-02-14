def BitVec.shiftRightShrink (x : BitVec n) (s : Nat) : BitVec (n - s) := x.toNat >>> s
