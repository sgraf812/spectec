(* Definitions of SpecTec functions that the specification leaves to prose
   (`hint(builtin)`), and of integer operations whose clauses call a function that the
   middle passes turn into a relation. The printer emits `prelude` after the preamble and,
   for every function `f` in `bodies`, the definition `def f : <signature> := <body>` in
   place of an opaque constant. Review both as specification text: they are the only
   hand-written meaning in the generated file. *)

let prelude = {|
/- Integer built-ins of WebAssembly 3.0, chapter 4.3 "Numerics", on `BitVec`.
   Adapted from factoidal-core (https://github.com/danbri/factoidal-core), file
   formal/lean4/L4Factoidal/WasmVM/Spec/Builtins.lean, Apache License 2.0. -/
namespace Builtins

/-- `signed_N(i) = i` if `0 ≤ i < 2^(N-1)`, else `i - 2^N`. -/
def signed_ (N : Nat) (i : Nat) : Int :=
  if i < 2 ^ (N - 1) then (i : Int) else (i : Int) - 2 ^ N

/-- The inverse of `signed_N`. -/
def inv_signed_ (N : Nat) (i : Int) : Nat :=
  if 0 ≤ i then i.toNat else (i + 2 ^ N).toNat

/-- `sat_u_N(i)` clamps `i` to between `0` and `2^N-1`. -/
def sat_u_ (N : Nat) (i : Int) : Nat :=
  if i < 0 then 0 else if i > 2 ^ N - 1 then 2 ^ N - 1 else i.toNat

/-- `sat_s_N(i)` clamps `i` to between `-2^(N-1)` and `2^(N-1)-1`. -/
def sat_s_ (N : Nat) (i : Int) : Int :=
  if i < -2 ^ (N - 1) then -2 ^ (N - 1)
  else if i > 2 ^ (N - 1) - 1 then 2 ^ (N - 1) - 1 else i

/-- `$bool(b)`: `1` for true, `0` for false. -/
def bool (b : Bool) : Nat := if b then 1 else 0

/-- `$truncz(q)`: `q` rounded towards zero. -/
def truncz (q : Rat) : Int := if 0 ≤ q then q.floor else q.ceil

/-- `ibits_N(i)`: the `N` bits of `i`, most significant first. -/
def ibits_ {n : Nat} (i : BitVec n) : List Bool := (List.range n).map fun k => i.getMsbD k

/-- The inverse of `ibits_N`. -/
def inv_ibits_ (n : Nat) (ds : List Bool) : BitVec n :=
  BitVec.ofNat n (ds.foldl (fun acc d => 2 * acc + (if d then 1 else 0)) 0)

/-- `ibytes_N(i)`: the `N/8` bytes of `i`, least significant first (little endian). -/
def ibytes_ {n : Nat} (i : BitVec n) : List (BitVec 8) :=
  (List.range (n / 8)).map fun k => i.extractLsb' (8 * k) 8

/-- The inverse of `ibytes_N`. -/
def inv_ibytes_ (n : Nat) (bs : List (BitVec 8)) : BitVec n :=
  BitVec.ofNat n (bs.foldr (fun b acc => b.toNat + 256 * acc) 0)

def inot_ {n : Nat} (i : BitVec n) : BitVec n := ~~~i
def iand_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ &&& i₂
def iandnot_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := iand_ i₁ (inot_ i₂)
def ior_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ ||| i₂
def ixor_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ ^^^ i₂
def irev_ {n : Nat} (i : BitVec n) : BitVec n := i.reverse
/-- `ibitselect_N(i_1, i_2, i_3) = ior_N(iand_N(i_1, i_3), iand_N(i_2, inot_N(i_3)))`. -/
def ibitselect_ {n : Nat} (i₁ i₂ i₃ : BitVec n) : BitVec n := ior_ (iand_ i₁ i₃) (iand_ i₂ (inot_ i₃))

/-- Shifts and rotations count modulo `N`. A signed right shift extends the sign bit. -/
def ishl_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁ <<< (i₂ % n)
def ishr_ {n : Nat} (signed : Bool) (i₁ : BitVec n) (i₂ : Nat) : BitVec n :=
  if signed then i₁.sshiftRight (i₂ % n) else i₁ >>> (i₂ % n)
def irotl_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁.rotateLeft (i₂ % n)
def irotr_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁.rotateRight (i₂ % n)

/-- Leading and trailing zero bits (`N` for `0`), and the count of one bits. -/
def iclz_ {n : Nat} (i : BitVec n) : BitVec n := i.clz
def ictz_ {n : Nat} (i : BitVec n) : BitVec n := i.ctz
def ipopcnt_ {n : Nat} (i : BitVec n) : BitVec n := i.cpop

/-- `$iavgr_(N, U, i_1, i_2) = truncz((i_1 + i_2 + 1) / 2)`. -/
def iavgr_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := BitVec.ofNat n ((i₁.toNat + i₂.toNat + 1) / 2)

/-- `$iq15mulr_sat_(N, S, i_1, i_2) = inv_signed_N(sat_s_N((signed_N(i_1) · signed_N(i_2) + 2^14) >> 15))`,
    with an arithmetic shift. -/
def iq15mulr_sat_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n :=
  BitVec.ofNat n (inv_signed_ n (sat_s_ n ((signed_ n i₁.toNat * signed_ n i₂.toNat + 2 ^ 14) >>> 15)))

/-- `wrap_(M,N)(i) = i mod 2^N`; `extend_u_(M,N)(i) = i`;
    `extend_s_(M,N)(i) = inv_signed_N(signed_M(i))`;
    `narrow_u_(M,N)(i) = sat_u_N(signed_M(i))`;
    `narrow_s_(M,N)(i) = inv_signed_N(sat_s_N(signed_M(i)))`. -/
def wrap_ {m : Nat} (n : Nat) (i : BitVec m) : BitVec n := i.setWidth n
def extend_ {m : Nat} (n : Nat) (signed : Bool) (i : BitVec m) : BitVec n :=
  if signed then i.signExtend n else i.setWidth n
def narrow_ {m : Nat} (n : Nat) (signed : Bool) (i : BitVec m) : BitVec n :=
  if signed then BitVec.ofNat n (inv_signed_ n (sat_s_ n (signed_ m i.toNat)))
  else BitVec.ofNat n (sat_u_ n (signed_ m i.toNat))

/- The operations on `Nat`, the representation of `iN` in the generated file: an argument is
   read as `BitVec.ofNat N`, and a result is returned as `toNat`. -/
namespace OnNat
def un (f : ∀ {n : Nat}, BitVec n → BitVec n) (N i : Nat) : Nat := (f (BitVec.ofNat N i)).toNat
def bin (f : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n) (N i₁ i₂ : Nat) : Nat :=
  (f (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def ibitselect_ (N i₁ i₂ i₃ : Nat) : Nat :=
  (Builtins.ibitselect_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂) (BitVec.ofNat N i₃)).toNat
def ishl_ (N i₁ i₂ : Nat) : Nat := (Builtins.ishl_ (BitVec.ofNat N i₁) i₂).toNat
def ishr_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat := (Builtins.ishr_ signed (BitVec.ofNat N i₁) i₂).toNat
def irotl_ (N i₁ i₂ : Nat) : Nat := (Builtins.irotl_ (BitVec.ofNat N i₁) i₂).toNat
def irotr_ (N i₁ i₂ : Nat) : Nat := (Builtins.irotr_ (BitVec.ofNat N i₁) i₂).toNat
def wrap_ (M N i : Nat) : Nat := (Builtins.wrap_ N (BitVec.ofNat M i)).toNat
def extend_ (M N : Nat) (signed : Bool) (i : Nat) : Nat := (Builtins.extend_ N signed (BitVec.ofNat M i)).toNat
def narrow_ (M N : Nat) (signed : Bool) (i : Nat) : Nat := (Builtins.narrow_ N signed (BitVec.ofNat M i)).toNat
def ibits_ (N i : Nat) : List Nat := (Builtins.ibits_ (BitVec.ofNat N i)).map bool
def inv_ibits_ (N : Nat) (ds : List Nat) : Nat := (Builtins.inv_ibits_ N (ds.map fun d => d != 0)).toNat
def ibytes_ (N i : Nat) : List Nat := (Builtins.ibytes_ (BitVec.ofNat N i)).map BitVec.toNat
def inv_ibytes_ (N : Nat) (bs : List Nat) : Nat := (Builtins.inv_ibytes_ N (bs.map (BitVec.ofNat 8))).toNat
end OnNat

end Builtins
|}

(* The body of each function, against the signature that the printer gives it. `iN` is `uN`, a
   `Nat` behind `mk_uN`; `sx` is `U` or `S`. A clause cited as `3.1:n` is line `n` of
   `3.1-numerics.scalar.spectec`. *)
let un f = "fun v_N i => .mk_uN (Builtins.OnNat.un Builtins." ^ f ^ " v_N (proj_uN_0 i))"
let bin f = "fun v_N i j => .mk_uN (Builtins.OnNat.bin Builtins." ^ f ^ " v_N (proj_uN_0 i) (proj_uN_0 j))"
let signed = "(decide (v_sx = .S))"
let p = "proj_uN_0"

let bodies = [
  "truncz", "fun q => Builtins.truncz q";
  "ceilz", "fun q => q.ceil";
  "inot_", un "inot_";
  "irev_", un "irev_";
  "iclz_", un "iclz_";
  "ictz_", un "ictz_";
  "ipopcnt_", un "ipopcnt_";
  "iand_", bin "iand_";
  "iandnot_", bin "iandnot_";
  "ior_", bin "ior_";
  "ixor_", bin "ixor_";
  "ibitselect_", "fun v_N i j k => .mk_uN (Builtins.OnNat.ibitselect_ v_N (" ^ p ^ " i) (" ^ p ^ " j) (" ^ p ^ " k))";
  "ishl_", "fun v_N i j => .mk_uN (Builtins.OnNat.ishl_ v_N (" ^ p ^ " i) (" ^ p ^ " j))";
  "ishr_", "fun v_N v_sx i j => .mk_uN (Builtins.OnNat.ishr_ v_N " ^ signed ^ " (" ^ p ^ " i) (" ^ p ^ " j))";
  "irotl_", "fun v_N i j => .mk_uN (Builtins.OnNat.irotl_ v_N (" ^ p ^ " i) (" ^ p ^ " j))";
  "irotr_", "fun v_N i j => .mk_uN (Builtins.OnNat.irotr_ v_N (" ^ p ^ " i) (" ^ p ^ " j))";
  (* 3.1:201 leaves `iavgr_` to prose, which defines the unsigned form; the signed form
     takes the same value. *)
  "iavgr_", "fun v_N v_sx i j => .mk_uN (Builtins.OnNat.bin Builtins.iavgr_ v_N (" ^ p ^ " i) (" ^ p ^ " j))";
  (* 3.1:199 leaves `iq15mulr_sat_` to prose, which defines the signed form; the unsigned
     form takes the same value. *)
  "iq15mulr_sat_", "fun v_N v_sx i j => .mk_uN (Builtins.OnNat.bin Builtins.iq15mulr_sat_ v_N (" ^ p ^ " i) (" ^ p ^ " j))";
  (* 3.1:149-150 *)
  "iabs_", "fun v_N i => if 0 ≤ Builtins.signed_ v_N (" ^ p ^ " i) then i else .mk_uN ((2 ^ v_N - " ^ p ^ " i) % 2 ^ v_N)";
  (* 3.1:183-186 *)
  "imin_", "fun v_N v_sx i j => match v_sx with\n    | .U => if " ^ p ^ " i ≤ " ^ p ^ " j then i else j\n    | .S => if Builtins.signed_ v_N (" ^ p ^ " i) ≤ Builtins.signed_ v_N (" ^ p ^ " j) then i else j";
  (* 3.1:188-191 *)
  "imax_", "fun v_N v_sx i j => match v_sx with\n    | .U => if " ^ p ^ " i ≥ " ^ p ^ " j then i else j\n    | .S => if Builtins.signed_ v_N (" ^ p ^ " i) ≥ Builtins.signed_ v_N (" ^ p ^ " j) then i else j";
  (* 3.1:193-194 *)
  "iadd_sat_", "fun v_N v_sx i j => match v_sx with\n    | .U => .mk_uN (Builtins.sat_u_ v_N (Int.ofNat (" ^ p ^ " i + " ^ p ^ " j)))\n    | .S => .mk_uN (Builtins.inv_signed_ v_N (Builtins.sat_s_ v_N (Builtins.signed_ v_N (" ^ p ^ " i) + Builtins.signed_ v_N (" ^ p ^ " j))))";
  (* 3.1:196-197 *)
  "isub_sat_", "fun v_N v_sx i j => match v_sx with\n    | .U => .mk_uN (Builtins.sat_u_ v_N (Int.ofNat (" ^ p ^ " i) - Int.ofNat (" ^ p ^ " j)))\n    | .S => .mk_uN (Builtins.inv_signed_ v_N (Builtins.sat_s_ v_N (Builtins.signed_ v_N (" ^ p ^ " i) - Builtins.signed_ v_N (" ^ p ^ " j))))";
  (* 3.1:227-237 *)
  "ilt_", "fun v_N v_sx i j => .mk_uN (Builtins.bool (match v_sx with | .U => decide (" ^ p ^ " i < " ^ p ^ " j) | .S => decide (Builtins.signed_ v_N (" ^ p ^ " i) < Builtins.signed_ v_N (" ^ p ^ " j))))";
  "igt_", "fun v_N v_sx i j => .mk_uN (Builtins.bool (match v_sx with | .U => decide (" ^ p ^ " i > " ^ p ^ " j) | .S => decide (Builtins.signed_ v_N (" ^ p ^ " i) > Builtins.signed_ v_N (" ^ p ^ " j))))";
  "ile_", "fun v_N v_sx i j => .mk_uN (Builtins.bool (match v_sx with | .U => decide (" ^ p ^ " i ≤ " ^ p ^ " j) | .S => decide (Builtins.signed_ v_N (" ^ p ^ " i) ≤ Builtins.signed_ v_N (" ^ p ^ " j))))";
  "ige_", "fun v_N v_sx i j => .mk_uN (Builtins.bool (match v_sx with | .U => decide (" ^ p ^ " i ≥ " ^ p ^ " j) | .S => decide (Builtins.signed_ v_N (" ^ p ^ " i) ≥ Builtins.signed_ v_N (" ^ p ^ " j))))";
  "wrap__", "fun v_M v_N i => .mk_uN (Builtins.OnNat.wrap_ v_M v_N (" ^ p ^ " i))";
  "extend__", "fun v_M v_N v_sx i => .mk_uN (Builtins.OnNat.extend_ v_M v_N " ^ signed ^ " (" ^ p ^ " i))";
  "narrow__", "fun v_M v_N v_sx i => .mk_uN (Builtins.OnNat.narrow_ v_M v_N " ^ signed ^ " (" ^ p ^ " i))";
  "ibits_", "fun v_N i => (Builtins.OnNat.ibits_ v_N (" ^ p ^ " i)).map .mk_bit";
  "inv_ibits_", "fun v_N ds => .mk_uN (Builtins.OnNat.inv_ibits_ v_N (ds.map fun | .mk_bit d => d))";
  "ibytes_", "fun v_N i => (Builtins.OnNat.ibytes_ v_N (" ^ p ^ " i)).map .mk_byte";
  "inv_ibytes_", "fun v_N bs => .mk_uN (Builtins.OnNat.inv_ibytes_ v_N (bs.map proj_byte_0))";
  (* `bytes_t(c)` is `ibytes_N(c)` for an integer and `fbytes_N(c)` for a float of size `N`. *)
  "nbytes_", "fun nt c => match c with\n    | .mk_num__0 _ i => ibytes_ (size nt) i\n    | .mk_num__1 _ f => fbytes_ (size nt) f";
]
