instance : ToStream ByteArray (Subarray UInt8) where
  toStream := (·.data.toSubarray)
