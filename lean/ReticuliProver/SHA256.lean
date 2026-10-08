/-
# SHA-256 (FIPS PUB 180-4) and the proof-of-work target condition

Self-contained: imports nothing beyond the Lean core prelude (`Nat`, `UInt8`, `UInt32`,
`Array`, `ByteArray`, `List`, `String`). Every definition is computable, and every
theorem below is checked by the kernel (`decide +kernel`), so the file adds no axiom.

Part 1 transcribes FIPS 180-4 (NIST, August 2015) clause by clause; each definition's
docstring names the clause it transcribes. Part 2 states the Bitcoin proof-of-work
condition on top of it, with each decoding rule cited to its source. Nothing is stated
about mining beyond the condition itself.

Conventions. A "word" is a `UInt32` (§2.2.2, w = 32). Bit strings of the standard are
byte strings here: the standard only hashes messages whose length is a multiple of 8
(§5.1.1 handles arbitrary bit lengths; ByteArray messages are the byte-aligned case).
Loops over 64 rounds and over blocks are written with `Nat.fold` / `List.foldl`
(structural recursion), so that the kernel can evaluate them.
-/

namespace ReticuliProver.SHA256

/-! ## §3.2 Operations on words -/

/-- §3.2 (3): `SHRⁿ(x) = x >> n`, the right shift by `n` bits. -/
def SHR (n : UInt32) (x : UInt32) : UInt32 := x >>> n

/-- §3.2 (4): `ROTRⁿ(x) = (x >> n) ∨ (x << (w − n))`, the rotate-right (circular right
shift) by `n` bits, `0 ≤ n < w = 32`. -/
def ROTR (n : UInt32) (x : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-! ## §4.1.2 SHA-224 and SHA-256 functions, equations (4.2)–(4.7) -/

/-- (4.2) `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- (4.3) `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- (4.4) `Σ₀^{256}(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def «Σ₀» (x : UInt32) : UInt32 := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x

/-- (4.5) `Σ₁^{256}(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def «Σ₁» (x : UInt32) : UInt32 := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x

/-- (4.6) `σ₀^{256}(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def σ₀ (x : UInt32) : UInt32 := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x

/-- (4.7) `σ₁^{256}(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def σ₁ (x : UInt32) : UInt32 := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-! ## §4.2.2 SHA-224 and SHA-256 constants -/

/-- §4.2.2: the sixty-four constant 32-bit words `K₀^{256}, …, K₆₃^{256}` (the first
thirty-two bits of the fractional parts of the cube roots of the first sixty-four primes),
in the order of the standard's table. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-! ## §5.1.1 Padding the message -/

/-- §5.1.1: the number `k` of zero bits appended after the `1` bit so that
`ℓ + 1 + k ≡ 448 (mod 512)`, `k` the smallest non-negative solution; `ℓ` is the message
length in bits. -/
def paddingZeros (ℓ : Nat) : Nat := (448 + 512 - (ℓ + 1) % 512) % 512

/-- §5.1.1: the 64-bit block equal to `ℓ` in binary, most significant byte first (the
standard's bit strings are written big-endian; §3.1 (1)). -/
def lengthBlock (ℓ : Nat) : ByteArray :=
  Nat.fold 8 (fun i _ acc => acc.push ((ℓ >>> (8 * (7 - i))) % 256).toUInt8) ByteArray.empty

/-- §5.1.1: the padded message `M ∥ 1 ∥ 0ᵏ ∥ ⟨ℓ⟩₆₄`. For a byte-aligned message the
appended `1` bit and the first seven zero bits form the byte `0x80`, followed by
`(k − 7) / 8` zero bytes (`k ≡ 7 (mod 8)` since `ℓ ≡ 0 (mod 8)`). The result has length
a multiple of 512 bits. -/
def pad (M : ByteArray) : ByteArray :=
  let ℓ := 8 * M.size
  let k := paddingZeros ℓ
  let withOne := M.push 0x80
  let withZeros := Nat.fold ((k - 7) / 8) (fun _ _ acc => acc.push 0) withOne
  Nat.fold 8 (fun i _ acc => acc.push ((lengthBlock ℓ).get! i)) withZeros

/-! ## §5.2.1 Parsing the message -/

/-- §5.2.1 with §3.1: the 32-bit word whose big-endian byte representation starts at
byte offset `o` of `P` (out-of-range bytes read as `0`; never exercised on padded input). -/
def wordAt (P : ByteArray) (o : Nat) : UInt32 :=
  ((P.data.getD o 0).toUInt32 <<< 24) ||| ((P.data.getD (o + 1) 0).toUInt32 <<< 16) |||
    ((P.data.getD (o + 2) 0).toUInt32 <<< 8) ||| (P.data.getD (o + 3) 0).toUInt32

/-- §5.2.1: `M_t^{(i)}`, the `t`-th 32-bit word (`0 ≤ t ≤ 15`) of the `i`-th 512-bit
block `M^{(i)}` (`1 ≤ i ≤ N` in the standard; here blocks are numbered from `0`) of the
padded message `P`. -/
def M (P : ByteArray) (i t : Nat) : UInt32 := wordAt P (64 * i + 4 * t)

/-- §5.2.1: the number `N` of 512-bit blocks of the padded message. -/
def N (P : ByteArray) : Nat := P.size / 64

/-! ## §5.3.3 SHA-256 initial hash value -/

/-- §5.3.3: the initial hash value `H^{(0)}`, eight 32-bit words `H₀^{(0)}, …, H₇^{(0)}`
(the first thirty-two bits of the fractional parts of the square roots of the first eight
primes). -/
def «H⁰» : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## §6.2.2 SHA-256 hash computation -/

/-- §6.2.2 step 1: the message schedule `W₀, …, W₆₃` of a block given by its words
`M_t`: `W_t = M_t` for `0 ≤ t ≤ 15` and
`W_t = σ₁^{256}(W_{t−2}) + W_{t−7} + σ₀^{256}(W_{t−15}) + W_{t−16}` for `16 ≤ t ≤ 63`
(addition modulo 2³² is `UInt32` addition, §3.2 (1)). -/
def W (Mt : Nat → UInt32) : Array UInt32 :=
  Nat.fold 64 (fun t _ W =>
    W.push (if t < 16 then Mt t
      else σ₁ (W.getD (t - 2) 0) + W.getD (t - 7) 0 + σ₀ (W.getD (t - 15) 0) + W.getD (t - 16) 0))
    #[]

/-- §6.2.2 step 2: the eight working variables `a, b, c, d, e, f, g, h`. -/
structure Working where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- §6.2.2 step 2: initialise the working variables with the `(i−1)`-st hash value,
`a = H₀^{(i−1)}, …, h = H₇^{(i−1)}`. -/
def Working.init (H : Array UInt32) : Working :=
  ⟨H.getD 0 0, H.getD 1 0, H.getD 2 0, H.getD 3 0, H.getD 4 0, H.getD 5 0, H.getD 6 0, H.getD 7 0⟩

/-- §6.2.2 step 3, one iteration `t`:
`T₁ = h + Σ₁^{256}(e) + Ch(e, f, g) + K_t^{256} + W_t`, `T₂ = Σ₀^{256}(a) + Maj(a, b, c)`,
`h = g`, `g = f`, `f = e`, `e = d + T₁`, `d = c`, `c = b`, `b = a`, `a = T₁ + T₂`. -/
def round (W : Array UInt32) (t : Nat) (v : Working) : Working :=
  let T₁ := v.h + «Σ₁» v.e + Ch v.e v.f v.g + K.getD t 0 + W.getD t 0
  let T₂ := «Σ₀» v.a + Maj v.a v.b v.c
  ⟨T₁ + T₂, v.a, v.b, v.c, v.d + T₁, v.e, v.f, v.g⟩

/-- §6.2.2 step 3: the sixty-four iterations `t = 0, …, 63`. -/
def rounds (W : Array UInt32) (v : Working) : Working :=
  Nat.fold 64 (fun t _ v => round W t v) v

/-- §6.2.2 step 4: the `i`-th intermediate hash value
`H_j^{(i)} = (working variable j) + H_j^{(i−1)}`, `j = 0, …, 7`. -/
def intermediate (H : Array UInt32) (v : Working) : Array UInt32 :=
  #[v.a + H.getD 0 0, v.b + H.getD 1 0, v.c + H.getD 2 0, v.d + H.getD 3 0,
    v.e + H.getD 4 0, v.f + H.getD 5 0, v.g + H.getD 6 0, v.h + H.getD 7 0]

/-- §6.2.2 steps 1–4 for one block: the compression function taking `H^{(i−1)}` and the
words `M_t^{(i)}` of block `i` to `H^{(i)}`. -/
def compress (H : Array UInt32) (Mt : Nat → UInt32) : Array UInt32 :=
  intermediate H (rounds (W Mt) (Working.init H))

/-- §6.2.2, the outer loop `for i = 1 to N`: iterated hashing of the padded message,
starting from `H^{(0)}`; the result is the final hash value `H^{(N)}`. -/
def hashBlocks (P : ByteArray) : Array UInt32 :=
  (List.range (N P)).foldl (fun H i => compress H (M P i)) «H⁰»

/-- §6.2.2, closing sentence: the 256-bit message digest
`H₀^{(N)} ∥ H₁^{(N)} ∥ … ∥ H₇^{(N)}`, each word big-endian (§3.1). -/
def digest (H : Array UInt32) : ByteArray :=
  H.foldl (fun acc (w : UInt32) =>
    (((acc.push (w >>> 24).toUInt8).push (w >>> 16).toUInt8).push (w >>> 8).toUInt8).push w.toUInt8)
    ByteArray.empty

/-- SHA-256 of a byte string: §5.1.1 padding, §5.2.1 parsing, §6.2.2 hash computation. -/
def sha256 (Msg : ByteArray) : ByteArray := digest (hashBlocks (pad Msg))

/-! ## Test vectors (FIPS 180-4 §6.2 / NIST CSRC "SHA-256 examples", CAVP) -/

/-- Decode a hexadecimal string (even length, lowercase or uppercase) to bytes; used only to
write the expected digests legibly. -/
def ofHex (s : String) : ByteArray :=
  let nib (c : Char) : Nat :=
    if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc => go rest (acc.push (16 * nib hi + nib lo).toUInt8)
    | _, acc => acc
  go s.toList ByteArray.empty

/-- The ASCII bytes of a string (all test-vector messages are ASCII). -/
def ascii (s : String) : ByteArray := s.toUTF8

/-- NIST CAVP SHA-256 short-message vector, 0-bit message. -/
theorem sha256_empty :
    sha256 (ascii "") =
      ofHex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide +kernel

/-- FIPS 180-4 example (NIST "SHA-256 example" document, example 1): the 24-bit, one-block
message "abc". -/
theorem sha256_abc :
    sha256 (ascii "abc") =
      ofHex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide +kernel

/-- FIPS 180-4 example (NIST "SHA-256 example" document, example 2): the 448-bit, two-block
message "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq". -/
theorem sha256_two_block :
    sha256 (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
      ofHex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" := by
  decide +kernel

end ReticuliProver.SHA256

/-! ## Part 2: the proof-of-work target condition -/

namespace ReticuliProver.Mining

open ReticuliProver.SHA256

/-- `SHA256d`: SHA-256 applied twice (Bitcoin's block hash,
`CBlockHeader::GetHash = SerializeHash` with `CHash256`, `src/hash.h`). -/
def doubleSHA256 (x : ByteArray) : ByteArray := sha256 (sha256 x)

/-- The exponent ("size") byte of a compact target: `nSize = nCompact >> 24`
(`arith_uint256::SetCompact`, `src/arith_uint256.cpp`). -/
def compactSize (nBits : UInt32) : Nat := (nBits >>> 24).toNat

/-- The mantissa of a compact target: the low 23 bits, `nWord = nCompact & 0x007fffff`
(`arith_uint256::SetCompact`). -/
def compactMantissa (nBits : UInt32) : Nat := (nBits &&& 0x007fffff).toNat

/-- Sign bit 0x00800000 of the compact encoding: `*pfNegative = nWord != 0 && (nCompact &
0x00800000) != 0` (`arith_uint256::SetCompact`). Consensus rejects a negative target
(`CheckProofOfWork`, `src/pow.cpp`: `if (fNegative || bnTarget == 0 || fOverflow || …)
return false`). -/
def compactNegative (nBits : UInt32) : Bool :=
  compactMantissa nBits != 0 && (nBits &&& 0x00800000) != 0

/-- Overflow of the 256-bit target: `*pfOverflow = nWord != 0 && ((nSize > 34) || (nWord >
0xff && nSize > 33) || (nWord > 0xffff && nSize > 32))` (`arith_uint256::SetCompact`);
rejected by `CheckProofOfWork`. Recorded for completeness; `targetOfCompact` below is the raw
arithmetic value and does not truncate to 256 bits. -/
def compactOverflow (nBits : UInt32) : Bool :=
  let nSize := compactSize nBits
  let nWord := compactMantissa nBits
  nWord != 0 && (nSize > 34 || (nWord > 0xff && nSize > 33) || (nWord > 0xffff && nSize > 32))

/-- The raw ("clamp-free") target encoded by `nBits`, `mantissa · 256^(size − 3)`:
`if (nSize <= 3) nWord >>= 8 * (3 - nSize) else nWord <<= 8 * (nSize - 3)`
(`arith_uint256::SetCompact`; Bitcoin developer reference, "Target nBits": "the first byte
is the exponent, the next three bytes the mantissa, in base 256"). The negative case is
mapped to `0` (an unmeetable target, as in `SetCompact`'s sign handling: the magnitude is
stored and the sign flag separately rejects the block). No clamping to `powLimit`
(`0x1d00ffff` on mainnet, `chainparams.cpp`) is applied here: `CheckProofOfWork`
additionally requires `bnTarget ≤ UintToArith256(params.powLimit)`, which is a validity
rule on `nBits`, not part of the arithmetic decoding. -/
def targetOfCompact (nBits : UInt32) : Nat :=
  let nSize := compactSize nBits
  let nWord := compactMantissa nBits
  if compactNegative nBits then 0
  else if nSize ≤ 3 then nWord >>> (8 * (3 - nSize))
  else nWord <<< (8 * (nSize - 3))

/-- The 256-bit integer value of a 32-byte hash read little-endian, i.e. byte `0` least
significant: `UintToArith256(uint256)` reads the `uint256` byte array as little-endian 32-bit
limbs (`src/arith_uint256.cpp`), which is how `CheckProofOfWork` compares
`UintToArith256(hash) > bnTarget`. -/
def natOfLE (b : ByteArray) : Nat := b.data.foldr (fun byte acc => acc * 256 + byte.toNat) 0

/-- The proof-of-work condition on a serialized 80-byte block header
(`CheckProofOfWork(block.GetHash(), block.nBits, params)`, `src/pow.cpp`, final test
`UintToArith256(hash) > bnTarget → false`): the little-endian value of `SHA256d(header)` is
at most the decoded target. -/
def meetsTarget (header : ByteArray) (nBits : UInt32) : Prop :=
  natOfLE (doubleSHA256 header) ≤ targetOfCompact nBits

instance (header : ByteArray) (nBits : UInt32) : Decidable (meetsTarget header nBits) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The validity conditions `CheckProofOfWork` imposes on `nBits` besides the hash
comparison: not negative, not zero, no overflow, and at most the mainnet `powLimit`
(the target decoded from `0x1d00ffff`). Stated separately from `meetsTarget`. -/
def validCompact (nBits : UInt32) : Prop :=
  compactNegative nBits = false ∧ compactOverflow nBits = false ∧
    0 < targetOfCompact nBits ∧ targetOfCompact nBits ≤ targetOfCompact 0x1d00ffff

instance (nBits : UInt32) : Decidable (validCompact nBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The 80 serialized bytes of the Bitcoin mainnet genesis block header (block 0):
`nVersion = 1` (LE `01000000`), `hashPrevBlock = 0`, `hashMerkleRoot`
(`4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b`, serialized reversed),
`nTime = 1231006505` (LE `29ab5f49`), `nBits = 0x1d00ffff` (LE `ffff001d`),
`nNonce = 2083236893` (LE `1dac2b7c`). -/
def genesisHeader : ByteArray := ofHex
  ("01000000" ++
   "0000000000000000000000000000000000000000000000000000000000000000" ++
   "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a" ++
   "29ab5f49" ++ "ffff001d" ++ "1dac2b7c")

/-- The genesis block hash
`000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f` (displayed big-endian),
as the little-endian byte string `SHA256d(header)` produces. -/
theorem genesis_doubleSHA256 :
    doubleSHA256 genesisHeader =
      ofHex "6fe28c0ab6f1b372c1a6a246ae63f74f931e8365e15a089c68d6190000000000" := by
  decide +kernel

/-- The genesis block's `nBits` decodes to the mainnet `powLimit`
`0x00000000ffff0000…0000`. -/
theorem genesis_target :
    targetOfCompact 0x1d00ffff = 0xffff * 2 ^ 208 := by
  decide +kernel

/-- Sanity check: the genesis block header meets its own target. -/
theorem genesis_meetsTarget : meetsTarget genesisHeader 0x1d00ffff := by
  decide +kernel

theorem genesis_validCompact : validCompact 0x1d00ffff := by
  decide +kernel

end ReticuliProver.Mining
