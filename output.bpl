
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;

// The location of an uninitialized mutation. Using this to make sure that the location
// will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
function {:constructor} $Uninitialized(): $Location;

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) && p#$Mutation(parent) == p#$Mutation(child)
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/64/128
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 256;
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 18446744073709551616;
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 340282366920938463463374607431768211456;
}

// We don't need to know the size of destination, so no $ShrU8, etc.
procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}



//==================================
// Begin Translation



// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }

// spec fun at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:12:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
}

// fun signer::address_of [baseline] at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:12:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:12:5+1
    assume {:print "$at(5,389,390)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:13:10+17
    assume {:print "$at(5,443,460)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(5,443,460)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(5,465,466)"} true;
L1:

    // return $t1 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(5,465,466)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
L2:

    // abort($t2) at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(5,465,466)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct MoveCoin::Balance<OddCoin::OddCoin> at ./sources/MoveCoin.move:16:5+77
type {:datatype} $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin';
function {:constructor} $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($coin: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'): $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin';
function {:inline} $Update'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''_coin(s: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin', x: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'): $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin' {
    $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'(x)
}
function $IsValid'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''(s: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'): bool {
    $IsValid'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'(s))
}
function {:inline} $IsEqual'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''(s1: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin', s2: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'): bool {
    s1 == s2
}
var $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory: $Memory $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin';

// struct MoveCoin::Balance<#0> at ./sources/MoveCoin.move:16:5+77
type {:datatype} $eeee_MoveCoin_Balance'#0';
function {:constructor} $eeee_MoveCoin_Balance'#0'($coin: $eeee_MoveCoin_Coin'#0'): $eeee_MoveCoin_Balance'#0';
function {:inline} $Update'$eeee_MoveCoin_Balance'#0''_coin(s: $eeee_MoveCoin_Balance'#0', x: $eeee_MoveCoin_Coin'#0'): $eeee_MoveCoin_Balance'#0' {
    $eeee_MoveCoin_Balance'#0'(x)
}
function $IsValid'$eeee_MoveCoin_Balance'#0''(s: $eeee_MoveCoin_Balance'#0'): bool {
    $IsValid'$eeee_MoveCoin_Coin'#0''($coin#$eeee_MoveCoin_Balance'#0'(s))
}
function {:inline} $IsEqual'$eeee_MoveCoin_Balance'#0''(s1: $eeee_MoveCoin_Balance'#0', s2: $eeee_MoveCoin_Balance'#0'): bool {
    s1 == s2
}
var $eeee_MoveCoin_Balance'#0'_$memory: $Memory $eeee_MoveCoin_Balance'#0';

// struct MoveCoin::Coin<OddCoin::OddCoin> at ./sources/MoveCoin.move:12:5+66
type {:datatype} $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
function {:constructor} $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($value: int): $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
function {:inline} $Update'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''_value(s: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin', x: int): $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin' {
    $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'(x)
}
function $IsValid'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''(s: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'): bool {
    $IsValid'u64'($value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'(s))
}
function {:inline} $IsEqual'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''(s1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin', s2: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'): bool {
    s1 == s2
}

// struct MoveCoin::Coin<#0> at ./sources/MoveCoin.move:12:5+66
type {:datatype} $eeee_MoveCoin_Coin'#0';
function {:constructor} $eeee_MoveCoin_Coin'#0'($value: int): $eeee_MoveCoin_Coin'#0';
function {:inline} $Update'$eeee_MoveCoin_Coin'#0''_value(s: $eeee_MoveCoin_Coin'#0', x: int): $eeee_MoveCoin_Coin'#0' {
    $eeee_MoveCoin_Coin'#0'(x)
}
function $IsValid'$eeee_MoveCoin_Coin'#0''(s: $eeee_MoveCoin_Coin'#0'): bool {
    $IsValid'u64'($value#$eeee_MoveCoin_Coin'#0'(s))
}
function {:inline} $IsEqual'$eeee_MoveCoin_Coin'#0''(s1: $eeee_MoveCoin_Coin'#0', s2: $eeee_MoveCoin_Coin'#0'): bool {
    s1 == s2
}

// fun MoveCoin::balance_of<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:53:5+136
procedure {:inline 1} $eeee_MoveCoin_balance_of'$eeee_OddCoin_OddCoin'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin';
    var $t2: int;
    var $t3: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at ./sources/MoveCoin.move:53:5+1
    assume {:print "$at(2,1720,1721)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:54:9+13
    assume {:print "$at(2,1800,1813)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,1800,1813)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:54:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:54:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:54:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
L1:

    // return $t4 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:55:5+1
L2:

    // abort($t2) at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::balance_of<#0> [baseline] at ./sources/MoveCoin.move:53:5+136
procedure {:inline 1} $eeee_MoveCoin_balance_of'#0'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $eeee_MoveCoin_Balance'#0';
    var $t2: int;
    var $t3: $eeee_MoveCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at ./sources/MoveCoin.move:53:5+1
    assume {:print "$at(2,1720,1721)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:54:9+13
    assume {:print "$at(2,1800,1813)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,1800,1813)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:54:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'#0'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:54:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:54:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
L1:

    // return $t4 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:55:5+1
L2:

    // abort($t2) at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::balance_of [verification] at ./sources/MoveCoin.move:53:5+136
procedure {:timeLimit 40} $eeee_MoveCoin_balance_of$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $eeee_MoveCoin_Balance'#0';
    var $t2: int;
    var $t3: $eeee_MoveCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $eeee_MoveCoin_Balance'#0'_$memory#0: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:53:5+1
    assume {:print "$at(2,1720,1721)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:53:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // @0 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:53:5+1
    $eeee_MoveCoin_Balance'#0'_$memory#0 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[owner]($t0) at ./sources/MoveCoin.move:53:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:54:9+13
    assume {:print "$at(2,1800,1813)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,1800,1813)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:54:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'#0'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:54:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:54:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
L1:

    // assert Not(Not(exists[@0]<MoveCoin::Balance<#0>>($t0))) at ./sources/MoveCoin.move:59:9+44
    assume {:print "$at(2,1924,1968)"} true;
    assert {:msg "assert_failed(2,1924,1968): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#0, $t0);

    // return $t4 at ./sources/MoveCoin.move:59:9+44
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(2,1855,1856)"} true;
L2:

    // assert Not(exists[@0]<MoveCoin::Balance<#0>>($t0)) at ./sources/MoveCoin.move:57:5+112
    assume {:print "$at(2,1862,1974)"} true;
    assert {:msg "assert_failed(2,1862,1974): abort not covered by any of the `aborts_if` clauses"}
      !$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#0, $t0);

    // abort($t2) at ./sources/MoveCoin.move:57:5+112
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:108:5+295
procedure {:inline 1} $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'': $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t5, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t5 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0))));

    // assume Identical($t6, select MoveCoin::Coin.value($t1)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$at(2,3968,3969)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t7 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:109:23+26
    assume {:print "$at(2,4068,4094)"} true;
    call $t7 := $eeee_MoveCoin_balance_of'$eeee_OddCoin_OddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,4068,4094)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[balance]($t7) at ./sources/MoveCoin.move:109:13+7
    assume {:print "$track_local(1,1,2):", $t7} $t7 == $t7;

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:110:32+17
    assume {:print "$at(2,4127,4144)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,4127,4144)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:110:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:110:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:110:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:111:13+14
    assume {:print "$at(2,4194,4208)"} true;
    $t12 := $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // trace_local[value]($t12) at ./sources/MoveCoin.move:111:20+5
    assume {:print "$track_local(1,1,4):", $t12} $t12 == $t12;

    // $t13 := +($t7, $t12) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:112:32+1
    assume {:print "$at(2,4249,4250)"} true;
    call $t13 := $AddU64($t7, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,4249,4250)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t11, $t13) at ./sources/MoveCoin.move:112:9+30
    $t11 := $UpdateMutation($t11, $t13);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:112:9+30
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:112:9+30
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:112:9+30
    $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L1 at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
L1:

    // return () at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:113:5+1
L2:

    // abort($t8) at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit<#0> [baseline] at ./sources/MoveCoin.move:108:5+295
procedure {:inline 1} $eeee_MoveCoin_deposit'#0'(_$t0: int, _$t1: $eeee_MoveCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'#0';
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t5, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t5 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assume Identical($t6, select MoveCoin::Coin.value($t1)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'#0'($t1));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$at(2,3968,3969)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t7 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:109:23+26
    assume {:print "$at(2,4068,4094)"} true;
    call $t7 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,4068,4094)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[balance]($t7) at ./sources/MoveCoin.move:109:13+7
    assume {:print "$track_local(1,1,2):", $t7} $t7 == $t7;

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:110:32+17
    assume {:print "$at(2,4127,4144)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,4127,4144)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:110:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:110:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:110:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:111:13+14
    assume {:print "$at(2,4194,4208)"} true;
    $t12 := $value#$eeee_MoveCoin_Coin'#0'($t1);

    // trace_local[value]($t12) at ./sources/MoveCoin.move:111:20+5
    assume {:print "$track_local(1,1,4):", $t12} $t12 == $t12;

    // $t13 := +($t7, $t12) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:112:32+1
    assume {:print "$at(2,4249,4250)"} true;
    call $t13 := $AddU64($t7, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,4249,4250)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t11, $t13) at ./sources/MoveCoin.move:112:9+30
    $t11 := $UpdateMutation($t11, $t13);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:112:9+30
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:112:9+30
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:112:9+30
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L1 at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
L1:

    // return () at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:113:5+1
L2:

    // abort($t8) at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit [verification] at ./sources/MoveCoin.move:108:5+295
procedure {:timeLimit 40} $eeee_MoveCoin_deposit$verify(_$t0: int, _$t1: $eeee_MoveCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'#0';
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $eeee_MoveCoin_Balance'#0'_$memory#4: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$at(2,3968,3969)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:108:5+1
    assume $IsValid'$eeee_MoveCoin_Coin'#0''($t1);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:108:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // assume Identical($t5, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t5 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assume Identical($t6, select MoveCoin::Coin.value($t1)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'#0'($t1));

    // @4 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$at(2,3968,3969)"} true;
    $eeee_MoveCoin_Balance'#0'_$memory#4 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:108:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t7 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:109:23+26
    assume {:print "$at(2,4068,4094)"} true;
    call $t7 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,4068,4094)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[balance]($t7) at ./sources/MoveCoin.move:109:13+7
    assume {:print "$track_local(1,1,2):", $t7} $t7 == $t7;

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:110:32+17
    assume {:print "$at(2,4127,4144)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,4127,4144)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:110:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:110:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:110:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:111:13+14
    assume {:print "$at(2,4194,4208)"} true;
    $t12 := $value#$eeee_MoveCoin_Coin'#0'($t1);

    // trace_local[value]($t12) at ./sources/MoveCoin.move:111:20+5
    assume {:print "$track_local(1,1,4):", $t12} $t12 == $t12;

    // $t13 := +($t7, $t12) on_abort goto L2 with $t8 at ./sources/MoveCoin.move:112:32+1
    assume {:print "$at(2,4249,4250)"} true;
    call $t13 := $AddU64($t7, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,4249,4250)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(1,1):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t11, $t13) at ./sources/MoveCoin.move:112:9+30
    $t11 := $UpdateMutation($t11, $t13);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:112:9+30
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:112:9+30
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:112:9+30
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L1 at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
L1:

    // assume Identical($t14, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:122:9+67
    assume {:print "$at(2,4502,4569)"} true;
    assume ($t14 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assert Not(Not(exists[@4]<MoveCoin::Balance<#0>>($t0))) at ./sources/MoveCoin.move:119:9+43
    assume {:print "$at(2,4398,4441)"} true;
    assert {:msg "assert_failed(2,4398,4441): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#4, $t0);

    // assert Not(Gt(Add($t5, $t6), 18446744073709551615)) at ./sources/MoveCoin.move:120:9+42
    assume {:print "$at(2,4450,4492)"} true;
    assert {:msg "assert_failed(2,4450,4492): function does not abort under this condition"}
      !(($t5 + $t6) > 18446744073709551615);

    // assert Eq<u64>($t14, Add($t5, $t6)) at ./sources/MoveCoin.move:123:9+46
    assume {:print "$at(2,4578,4624)"} true;
    assert {:msg "assert_failed(2,4578,4624): post-condition does not hold"}
      $IsEqual'u64'($t14, ($t5 + $t6));

    // return () at ./sources/MoveCoin.move:123:9+46
    return;

    // label L2 at ./sources/MoveCoin.move:113:5+1
    assume {:print "$at(2,4262,4263)"} true;
L2:

    // assert Or(Not(exists[@4]<MoveCoin::Balance<#0>>($t0)), Gt(Add($t5, $t6), 18446744073709551615)) at ./sources/MoveCoin.move:115:5+361
    assume {:print "$at(2,4269,4630)"} true;
    assert {:msg "assert_failed(2,4269,4630): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#4, $t0) || (($t5 + $t6) > 18446744073709551615));

    // abort($t8) at ./sources/MoveCoin.move:115:5+361
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun MoveCoin::mint<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:44:5+244
procedure {:inline 1} $eeee_MoveCoin_mint'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: int, _$t2: $eeee_OddCoin_OddCoin) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t0: int;
    var $t1: int;
    var $t2: $eeee_OddCoin_OddCoin;
    var $temp_0'$eeee_OddCoin_OddCoin': $eeee_OddCoin_OddCoin;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // assume Identical($t3, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:129:9+57
    assume {:print "$at(2,4726,4783)"} true;
    assume ($t3 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0))));

    // trace_local[mint_addr]($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$at(2,1380,1381)"} true;
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t4 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:46:28+32
    assume {:print "$at(2,1584,1616)"} true;
    $t4 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // assume Identical($t5, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t5 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0))));

    // assume Identical($t6, select MoveCoin::Coin.value($t4)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t4));

    // MoveCoin::deposit<#0>($t0, $t4) on_abort goto L2 with $t7 at ./sources/MoveCoin.move:46:9+52
    assume {:print "$at(2,1565,1617)"} true;
    call $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'($t0, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,1565,1617)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(1,2):", $t7} $t7 == $t7;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(2,1623,1624)"} true;
L1:

    // return () at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(2,1623,1624)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:47:5+1
L2:

    // abort($t7) at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(2,1623,1624)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun MoveCoin::mint [verification] at ./sources/MoveCoin.move:44:5+244
procedure {:timeLimit 40} $eeee_MoveCoin_mint$verify(_$t0: int, _$t1: int, _$t2: #0) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: $eeee_MoveCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t0: int;
    var $t1: int;
    var $t2: #0;
    var $temp_0'#0': #0;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $eeee_MoveCoin_Balance'#0'_$memory#8: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$at(2,1380,1381)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:44:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at ./sources/MoveCoin.move:44:5+1
    assume $IsValid'#0'($t2);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:44:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // assume Identical($t3, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:129:9+57
    assume {:print "$at(2,4726,4783)"} true;
    assume ($t3 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // @8 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$at(2,1380,1381)"} true;
    $eeee_MoveCoin_Balance'#0'_$memory#8 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[mint_addr]($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t4 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:46:28+32
    assume {:print "$at(2,1584,1616)"} true;
    $t4 := $eeee_MoveCoin_Coin'#0'($t1);

    // assume Identical($t5, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t5 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assume Identical($t6, select MoveCoin::Coin.value($t4)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'#0'($t4));

    // MoveCoin::deposit<#0>($t0, $t4) on_abort goto L2 with $t7 at ./sources/MoveCoin.move:46:9+52
    assume {:print "$at(2,1565,1617)"} true;
    call $eeee_MoveCoin_deposit'#0'($t0, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,1565,1617)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(1,2):", $t7} $t7 == $t7;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(2,1623,1624)"} true;
L1:

    // assume Identical($t8, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:134:9+67
    assume {:print "$at(2,4892,4959)"} true;
    assume ($t8 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assert Not(Not(exists[@8]<MoveCoin::Balance<#0>>($t0))) at ./sources/MoveCoin.move:131:9+43
    assume {:print "$at(2,4793,4836)"} true;
    assert {:msg "assert_failed(2,4793,4836): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#8, $t0);

    // assert Not(Gt(Add($t3, $t1), 18446744073709551615)) at ./sources/MoveCoin.move:132:9+37
    assume {:print "$at(2,4845,4882)"} true;
    assert {:msg "assert_failed(2,4845,4882): function does not abort under this condition"}
      !(($t3 + $t1) > 18446744073709551615);

    // assert Eq<u64>($t8, Add($t3, $t1)) at ./sources/MoveCoin.move:135:9+41
    assume {:print "$at(2,4968,5009)"} true;
    assert {:msg "assert_failed(2,4968,5009): post-condition does not hold"}
      $IsEqual'u64'($t8, ($t3 + $t1));

    // return () at ./sources/MoveCoin.move:135:9+41
    return;

    // label L2 at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(2,1623,1624)"} true;
L2:

    // assert Or(Not(exists[@8]<MoveCoin::Balance<#0>>($t0)), Gt(Add($t3, $t1), 18446744073709551615)) at ./sources/MoveCoin.move:49:5+84
    assume {:print "$at(2,1630,1714)"} true;
    assert {:msg "assert_failed(2,1630,1714): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#8, $t0) || (($t3 + $t1) > 18446744073709551615));

    // abort($t7) at ./sources/MoveCoin.move:49:5+84
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun MoveCoin::publish_balance<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:20:5+278
procedure {:inline 1} $eeee_MoveCoin_publish_balance'$eeee_OddCoin_OddCoin'(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t9: $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin';
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[account]($t0) at ./sources/MoveCoin.move:20:5+1
    assume {:print "$at(2,489,490)"} true;
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t2 := signer::address_of($t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:22:44+27
    assume {:print "$at(2,643,670)"} true;
    call $t2 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,643,670)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := exists<MoveCoin::Balance<#0>>($t2) at ./sources/MoveCoin.move:22:18+6
    $t4 := $ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t2);

    // $t5 := !($t4) at ./sources/MoveCoin.move:22:17+1
    call $t5 := $Not($t4);

    // if ($t5) goto L0 else goto L1 at ./sources/MoveCoin.move:22:9+86
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:22:9+86
L1:

    // $t6 := 2 at ./sources/MoveCoin.move:22:74+20
    assume {:print "$at(2,673,693)"} true;
    $t6 := 2;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/MoveCoin.move:22:9+86
    assume {:print "$at(2,608,694)"} true;
    assume {:print "$track_abort(1,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/MoveCoin.move:22:9+86
    $t3 := $t6;

    // goto L3 at ./sources/MoveCoin.move:22:9+86
    goto L3;

    // label L0 at ./sources/MoveCoin.move:23:17+7
    assume {:print "$at(2,712,719)"} true;
L0:

    // $t7 := 0 at ./sources/MoveCoin.move:21:50+1
    assume {:print "$at(2,595,596)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack MoveCoin::Coin<#0>($t7) at ./sources/MoveCoin.move:21:26+27
    $t8 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t7);

    // $t9 := pack MoveCoin::Balance<#0>($t8) at ./sources/MoveCoin.move:23:26+38
    assume {:print "$at(2,721,759)"} true;
    $t9 := $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($t8);

    // move_to<MoveCoin::Balance<#0>>($t9, $t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:23:9+7
    if ($ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(2,704,711)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(2,766,767)"} true;
L2:

    // return () at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(2,766,767)"} true;
    return;

    // label L3 at ./sources/MoveCoin.move:24:5+1
L3:

    // abort($t3) at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(2,766,767)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun MoveCoin::publish_balance [verification] at ./sources/MoveCoin.move:20:5+278
procedure {:timeLimit 40} $eeee_MoveCoin_publish_balance$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $eeee_MoveCoin_Coin'#0';
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: $eeee_MoveCoin_Coin'#0';
    var $t9: $eeee_MoveCoin_Balance'#0';
    var $t10: int;
    var $t0: $signer;
    var $temp_0'signer': $signer;
    var $eeee_MoveCoin_Balance'#0'_$memory#6: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:20:5+1
    assume {:print "$at(2,489,490)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:20:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // @6 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:20:5+1
    $eeee_MoveCoin_Balance'#0'_$memory#6 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[account]($t0) at ./sources/MoveCoin.move:20:5+1
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t2 := signer::address_of($t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:22:44+27
    assume {:print "$at(2,643,670)"} true;
    call $t2 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,643,670)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := exists<MoveCoin::Balance<#0>>($t2) at ./sources/MoveCoin.move:22:18+6
    $t4 := $ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t2);

    // $t5 := !($t4) at ./sources/MoveCoin.move:22:17+1
    call $t5 := $Not($t4);

    // if ($t5) goto L0 else goto L1 at ./sources/MoveCoin.move:22:9+86
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:22:9+86
L1:

    // $t6 := 2 at ./sources/MoveCoin.move:22:74+20
    assume {:print "$at(2,673,693)"} true;
    $t6 := 2;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/MoveCoin.move:22:9+86
    assume {:print "$at(2,608,694)"} true;
    assume {:print "$track_abort(1,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/MoveCoin.move:22:9+86
    $t3 := $t6;

    // goto L3 at ./sources/MoveCoin.move:22:9+86
    goto L3;

    // label L0 at ./sources/MoveCoin.move:23:17+7
    assume {:print "$at(2,712,719)"} true;
L0:

    // $t7 := 0 at ./sources/MoveCoin.move:21:50+1
    assume {:print "$at(2,595,596)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack MoveCoin::Coin<#0>($t7) at ./sources/MoveCoin.move:21:26+27
    $t8 := $eeee_MoveCoin_Coin'#0'($t7);

    // $t9 := pack MoveCoin::Balance<#0>($t8) at ./sources/MoveCoin.move:23:26+38
    assume {:print "$at(2,721,759)"} true;
    $t9 := $eeee_MoveCoin_Balance'#0'($t8);

    // move_to<MoveCoin::Balance<#0>>($t9, $t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:23:9+7
    if ($ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(2,704,711)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(2,766,767)"} true;
L2:

    // assume Identical($t10, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>(signer::$address_of($t0))))) at ./sources/MoveCoin.move:37:9+67
    assume {:print "$at(2,1089,1156)"} true;
    assume ($t10 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $1_signer_$address_of($t0)))));

    // assert Not(exists[@6]<MoveCoin::Balance<#0>>(signer::$address_of[]($t0))) at ./sources/MoveCoin.move:34:9+42
    assume {:print "$at(2,988,1030)"} true;
    assert {:msg "assert_failed(2,988,1030): function does not abort under this condition"}
      !$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#6, $1_signer_$address_of($t0));

    // assert exists<MoveCoin::Balance<#0>>(signer::$address_of($t0)) at ./sources/MoveCoin.move:36:9+40
    assume {:print "$at(2,1040,1080)"} true;
    assert {:msg "assert_failed(2,1040,1080): post-condition does not hold"}
      $ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $1_signer_$address_of($t0));

    // assert Eq<u64>($t10, 0) at ./sources/MoveCoin.move:39:9+31
    assume {:print "$at(2,1166,1197)"} true;
    assert {:msg "assert_failed(2,1166,1197): post-condition does not hold"}
      $IsEqual'u64'($t10, 0);

    // return () at ./sources/MoveCoin.move:39:9+31
    return;

    // label L3 at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(2,766,767)"} true;
L3:

    // assert exists[@6]<MoveCoin::Balance<#0>>(signer::$address_of[]($t0)) at ./sources/MoveCoin.move:26:5+117
    assume {:print "$at(2,773,890)"} true;
    assert {:msg "assert_failed(2,773,890): abort not covered by any of the `aborts_if` clauses"}
      $ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#6, $1_signer_$address_of($t0));

    // abort($t3) at ./sources/MoveCoin.move:26:5+117
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun MoveCoin::transfer<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:64:5+315
procedure {:inline 1} $eeee_MoveCoin_transfer'$eeee_OddCoin_OddCoin'(_$t0: $signer, _$t1: int, _$t2: int, _$t3: $eeee_OddCoin_OddCoin) returns ()
{
    // declare local variables
    var $t4: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t15: int;
    var $t16: int;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: $eeee_OddCoin_OddCoin;
    var $temp_0'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'': $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'$eeee_OddCoin_OddCoin': $eeee_OddCoin_OddCoin;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // assume Identical($t6, signer::$address_of($t0)) at ./sources/MoveCoin.move:72:9+41
    assume {:print "$at(2,2514,2555)"} true;
    assume ($t6 == $1_signer_$address_of($t0));

    // assume Identical($t7, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t6)))) at ./sources/MoveCoin.move:74:9+67
    assume {:print "$at(2,2565,2632)"} true;
    assume ($t7 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t6))));

    // assume Identical($t8, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t1)))) at ./sources/MoveCoin.move:75:9+58
    assume {:print "$at(2,2641,2699)"} true;
    assume ($t8 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t1))));

    // trace_local[from]($t0) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$at(2,2169,2170)"} true;
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t9 := signer::address_of($t0) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:65:25+24
    assume {:print "$at(2,2309,2333)"} true;
    call $t9 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,2309,2333)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[from_addr]($t9) at ./sources/MoveCoin.move:65:13+9
    assume {:print "$track_local(1,4,5):", $t9} $t9 == $t9;

    // $t11 := !=($t9, $t1) at ./sources/MoveCoin.move:66:27+2
    assume {:print "$at(2,2361,2363)"} true;
    $t11 := !$IsEqual'address'($t9, $t1);

    // if ($t11) goto L0 else goto L1 at ./sources/MoveCoin.move:66:9+37
    if ($t11) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:66:34+11
L1:

    // $t12 := 4 at ./sources/MoveCoin.move:66:34+11
    assume {:print "$at(2,2368,2379)"} true;
    $t12 := 4;
    assume $IsValid'u64'($t12);

    // trace_abort($t12) at ./sources/MoveCoin.move:66:9+37
    assume {:print "$at(2,2343,2380)"} true;
    assume {:print "$track_abort(1,4):", $t12} $t12 == $t12;

    // $t10 := move($t12) at ./sources/MoveCoin.move:66:9+37
    $t10 := $t12;

    // goto L3 at ./sources/MoveCoin.move:66:9+37
    goto L3;

    // label L0 at ./sources/MoveCoin.move:67:40+9
    assume {:print "$at(2,2421,2430)"} true;
L0:

    // assume Identical($t13, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t9)))) at ./sources/MoveCoin.move:98:9+57
    assume {:print "$at(2,3623,3680)"} true;
    assume ($t13 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t9))));

    // $t14 := MoveCoin::withdraw<#0>($t9, $t2) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:67:21+37
    assume {:print "$at(2,2402,2439)"} true;
    call $t14 := $eeee_MoveCoin_withdraw'$eeee_OddCoin_OddCoin'($t9, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,2402,2439)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[check]($t14) at ./sources/MoveCoin.move:67:13+5
    assume {:print "$track_local(1,4,4):", $t14} $t14 == $t14;

    // assume Identical($t15, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t1)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t15 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t1))));

    // assume Identical($t16, select MoveCoin::Coin.value($t14)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t16 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t14));

    // MoveCoin::deposit<#0>($t1, $t14) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:68:9+28
    assume {:print "$at(2,2449,2477)"} true;
    call $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'($t1, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,2449,2477)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:69:5+1
    assume {:print "$at(2,2483,2484)"} true;
L2:

    // return () at ./sources/MoveCoin.move:69:5+1
    assume {:print "$at(2,2483,2484)"} true;
    return;

    // label L3 at ./sources/MoveCoin.move:69:5+1
L3:

    // abort($t10) at ./sources/MoveCoin.move:69:5+1
    assume {:print "$at(2,2483,2484)"} true;
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun MoveCoin::transfer [verification] at ./sources/MoveCoin.move:64:5+315
procedure {:timeLimit 40} $eeee_MoveCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int, _$t3: #0) returns ()
{
    // declare local variables
    var $t4: $eeee_MoveCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: $eeee_MoveCoin_Coin'#0';
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: #0;
    var $temp_0'#0': #0;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    var $eeee_MoveCoin_Balance'#0'_$memory#10: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$at(2,2169,2170)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at ./sources/MoveCoin.move:64:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/MoveCoin.move:64:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at ./sources/MoveCoin.move:64:5+1
    assume $IsValid'#0'($t3);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:64:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // assume Identical($t6, signer::$address_of($t0)) at ./sources/MoveCoin.move:72:9+41
    assume {:print "$at(2,2514,2555)"} true;
    assume ($t6 == $1_signer_$address_of($t0));

    // assume Identical($t7, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t6)))) at ./sources/MoveCoin.move:74:9+67
    assume {:print "$at(2,2565,2632)"} true;
    assume ($t7 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t6))));

    // assume Identical($t8, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t1)))) at ./sources/MoveCoin.move:75:9+58
    assume {:print "$at(2,2641,2699)"} true;
    assume ($t8 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t1))));

    // @10 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$at(2,2169,2170)"} true;
    $eeee_MoveCoin_Balance'#0'_$memory#10 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[from]($t0) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at ./sources/MoveCoin.move:64:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t9 := signer::address_of($t0) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:65:25+24
    assume {:print "$at(2,2309,2333)"} true;
    call $t9 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,2309,2333)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[from_addr]($t9) at ./sources/MoveCoin.move:65:13+9
    assume {:print "$track_local(1,4,5):", $t9} $t9 == $t9;

    // $t11 := !=($t9, $t1) at ./sources/MoveCoin.move:66:27+2
    assume {:print "$at(2,2361,2363)"} true;
    $t11 := !$IsEqual'address'($t9, $t1);

    // if ($t11) goto L0 else goto L1 at ./sources/MoveCoin.move:66:9+37
    if ($t11) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:66:34+11
L1:

    // $t12 := 4 at ./sources/MoveCoin.move:66:34+11
    assume {:print "$at(2,2368,2379)"} true;
    $t12 := 4;
    assume $IsValid'u64'($t12);

    // trace_abort($t12) at ./sources/MoveCoin.move:66:9+37
    assume {:print "$at(2,2343,2380)"} true;
    assume {:print "$track_abort(1,4):", $t12} $t12 == $t12;

    // $t10 := move($t12) at ./sources/MoveCoin.move:66:9+37
    $t10 := $t12;

    // goto L3 at ./sources/MoveCoin.move:66:9+37
    goto L3;

    // label L0 at ./sources/MoveCoin.move:67:40+9
    assume {:print "$at(2,2421,2430)"} true;
L0:

    // assume Identical($t13, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t9)))) at ./sources/MoveCoin.move:98:9+57
    assume {:print "$at(2,3623,3680)"} true;
    assume ($t13 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t9))));

    // $t14 := MoveCoin::withdraw<#0>($t9, $t2) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:67:21+37
    assume {:print "$at(2,2402,2439)"} true;
    call $t14 := $eeee_MoveCoin_withdraw'#0'($t9, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,2402,2439)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[check]($t14) at ./sources/MoveCoin.move:67:13+5
    assume {:print "$track_local(1,4,4):", $t14} $t14 == $t14;

    // assume Identical($t15, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t1)))) at ./sources/MoveCoin.move:116:9+57
    assume {:print "$at(2,4292,4349)"} true;
    assume ($t15 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t1))));

    // assume Identical($t16, select MoveCoin::Coin.value($t14)) at ./sources/MoveCoin.move:117:9+30
    assume {:print "$at(2,4358,4388)"} true;
    assume ($t16 == $value#$eeee_MoveCoin_Coin'#0'($t14));

    // MoveCoin::deposit<#0>($t1, $t14) on_abort goto L3 with $t10 at ./sources/MoveCoin.move:68:9+28
    assume {:print "$at(2,2449,2477)"} true;
    call $eeee_MoveCoin_deposit'#0'($t1, $t14);
    if ($abort_flag) {
        assume {:print "$at(2,2449,2477)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(1,4):", $t10} $t10 == $t10;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:69:5+1
    assume {:print "$at(2,2483,2484)"} true;
L2:

    // assume Identical($t17, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t6)))) at ./sources/MoveCoin.move:76:9+77
    assume {:print "$at(2,2708,2785)"} true;
    assume ($t17 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t6))));

    // assume Identical($t18, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t1)))) at ./sources/MoveCoin.move:77:9+68
    assume {:print "$at(2,2794,2862)"} true;
    assume ($t18 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t1))));

    // assert Not(Not(exists[@10]<MoveCoin::Balance<#0>>($t6))) at ./sources/MoveCoin.move:79:9+48
    assume {:print "$at(2,2872,2920)"} true;
    assert {:msg "assert_failed(2,2872,2920): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#10, $t6);

    // assert Not(Not(exists[@10]<MoveCoin::Balance<#0>>($t1))) at ./sources/MoveCoin.move:80:9+41
    assume {:print "$at(2,2929,2970)"} true;
    assert {:msg "assert_failed(2,2929,2970): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#10, $t1);

    // assert Not(Lt($t7, $t2)) at ./sources/MoveCoin.move:81:9+32
    assume {:print "$at(2,2979,3011)"} true;
    assert {:msg "assert_failed(2,2979,3011): function does not abort under this condition"}
      !($t7 < $t2);

    // assert Not(Gt(Add($t8, $t2), 18446744073709551615)) at ./sources/MoveCoin.move:82:9+40
    assume {:print "$at(2,3020,3060)"} true;
    assert {:msg "assert_failed(2,3020,3060): function does not abort under this condition"}
      !(($t8 + $t2) > 18446744073709551615);

    // assert Not(Eq<address>($t6, $t1)) at ./sources/MoveCoin.move:83:9+26
    assume {:print "$at(2,3069,3095)"} true;
    assert {:msg "assert_failed(2,3069,3095): function does not abort under this condition"}
      !$IsEqual'address'($t6, $t1);

    // assert Eq<u64>($t17, Sub($t7, $t2)) at ./sources/MoveCoin.move:85:9+51
    assume {:print "$at(2,3105,3156)"} true;
    assert {:msg "assert_failed(2,3105,3156): post-condition does not hold"}
      $IsEqual'u64'($t17, ($t7 - $t2));

    // assert Eq<u64>($t18, Add($t8, $t2)) at ./sources/MoveCoin.move:86:9+47
    assume {:print "$at(2,3165,3212)"} true;
    assert {:msg "assert_failed(2,3165,3212): post-condition does not hold"}
      $IsEqual'u64'($t18, ($t8 + $t2));

    // return () at ./sources/MoveCoin.move:86:9+47
    return;

    // label L3 at ./sources/MoveCoin.move:69:5+1
    assume {:print "$at(2,2483,2484)"} true;
L3:

    // assert Or(Or(Or(Or(Not(exists[@10]<MoveCoin::Balance<#0>>($t6)), Not(exists[@10]<MoveCoin::Balance<#0>>($t1))), Lt($t7, $t2)), Gt(Add($t8, $t2), 18446744073709551615)), Eq<address>($t6, $t1)) at ./sources/MoveCoin.move:71:5+728
    assume {:print "$at(2,2490,3218)"} true;
    assert {:msg "assert_failed(2,2490,3218): abort not covered by any of the `aborts_if` clauses"}
      ((((!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#10, $t6) || !$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#10, $t1)) || ($t7 < $t2)) || (($t8 + $t2) > 18446744073709551615)) || $IsEqual'address'($t6, $t1));

    // abort($t10) at ./sources/MoveCoin.move:71:5+728
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:89:5+369
procedure {:inline 1} $eeee_MoveCoin_withdraw'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'': $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t4, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:98:9+57
    assume {:print "$at(2,3623,3680)"} true;
    assume ($t4 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0))));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$at(2,3224,3225)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:90:23+26
    assume {:print "$at(2,3333,3359)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'$eeee_OddCoin_OddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,3333,3359)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:90:13+7
    assume {:print "$track_local(1,5,2):", $t5} $t5 == $t5;

    // $t7 := >=($t5, $t1) at ./sources/MoveCoin.move:91:25+2
    assume {:print "$at(2,3385,3387)"} true;
    call $t7 := $Ge($t5, $t1);

    // if ($t7) goto L0 else goto L1 at ./sources/MoveCoin.move:91:9+49
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:91:36+21
L1:

    // $t8 := 1 at ./sources/MoveCoin.move:91:36+21
    assume {:print "$at(2,3396,3417)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./sources/MoveCoin.move:91:9+49
    assume {:print "$at(2,3369,3418)"} true;
    assume {:print "$track_abort(1,5):", $t8} $t8 == $t8;

    // $t6 := move($t8) at ./sources/MoveCoin.move:91:9+49
    $t6 := $t8;

    // goto L3 at ./sources/MoveCoin.move:91:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:92:69+4
    assume {:print "$at(2,3488,3492)"} true;
L0:

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:92:32+17
    assume {:print "$at(2,3451,3468)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,3451,3468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:92:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:92:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:92:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := -($t5, $t1) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:93:32+1
    assume {:print "$at(2,3537,3538)"} true;
    call $t12 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,3537,3538)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // write_ref($t11, $t12) at ./sources/MoveCoin.move:93:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:93:9+31
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:93:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:93:9+31
    $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$at(2,3555,3587)"} true;
    $t13 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // trace_return[0]($t13) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$track_return(1,5,0):", $t13} $t13 == $t13;

    // label L2 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
L2:

    // return $t13 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
    $ret0 := $t13;
    return;

    // label L3 at ./sources/MoveCoin.move:95:5+1
L3:

    // abort($t6) at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw<#0> [baseline] at ./sources/MoveCoin.move:89:5+369
procedure {:inline 1} $eeee_MoveCoin_withdraw'#0'(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $eeee_MoveCoin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t4, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:98:9+57
    assume {:print "$at(2,3623,3680)"} true;
    assume ($t4 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$at(2,3224,3225)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:90:23+26
    assume {:print "$at(2,3333,3359)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,3333,3359)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:90:13+7
    assume {:print "$track_local(1,5,2):", $t5} $t5 == $t5;

    // $t7 := >=($t5, $t1) at ./sources/MoveCoin.move:91:25+2
    assume {:print "$at(2,3385,3387)"} true;
    call $t7 := $Ge($t5, $t1);

    // if ($t7) goto L0 else goto L1 at ./sources/MoveCoin.move:91:9+49
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:91:36+21
L1:

    // $t8 := 1 at ./sources/MoveCoin.move:91:36+21
    assume {:print "$at(2,3396,3417)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./sources/MoveCoin.move:91:9+49
    assume {:print "$at(2,3369,3418)"} true;
    assume {:print "$track_abort(1,5):", $t8} $t8 == $t8;

    // $t6 := move($t8) at ./sources/MoveCoin.move:91:9+49
    $t6 := $t8;

    // goto L3 at ./sources/MoveCoin.move:91:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:92:69+4
    assume {:print "$at(2,3488,3492)"} true;
L0:

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:92:32+17
    assume {:print "$at(2,3451,3468)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,3451,3468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:92:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:92:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:92:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := -($t5, $t1) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:93:32+1
    assume {:print "$at(2,3537,3538)"} true;
    call $t12 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,3537,3538)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // write_ref($t11, $t12) at ./sources/MoveCoin.move:93:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:93:9+31
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:93:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:93:9+31
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$at(2,3555,3587)"} true;
    $t13 := $eeee_MoveCoin_Coin'#0'($t1);

    // trace_return[0]($t13) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$track_return(1,5,0):", $t13} $t13 == $t13;

    // label L2 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
L2:

    // return $t13 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
    $ret0 := $t13;
    return;

    // label L3 at ./sources/MoveCoin.move:95:5+1
L3:

    // abort($t6) at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw [verification] at ./sources/MoveCoin.move:89:5+369
procedure {:timeLimit 40} $eeee_MoveCoin_withdraw$verify(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t10: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $eeee_MoveCoin_Coin'#0';
    var $t14: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $eeee_MoveCoin_Balance'#0'_$memory#2: $Memory $eeee_MoveCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$at(2,3224,3225)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:89:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:89:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // assume Identical($t4, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:98:9+57
    assume {:print "$at(2,3623,3680)"} true;
    assume ($t4 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // @2 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$at(2,3224,3225)"} true;
    $eeee_MoveCoin_Balance'#0'_$memory#2 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:89:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:90:23+26
    assume {:print "$at(2,3333,3359)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,3333,3359)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:90:13+7
    assume {:print "$track_local(1,5,2):", $t5} $t5 == $t5;

    // $t7 := >=($t5, $t1) at ./sources/MoveCoin.move:91:25+2
    assume {:print "$at(2,3385,3387)"} true;
    call $t7 := $Ge($t5, $t1);

    // if ($t7) goto L0 else goto L1 at ./sources/MoveCoin.move:91:9+49
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:91:36+21
L1:

    // $t8 := 1 at ./sources/MoveCoin.move:91:36+21
    assume {:print "$at(2,3396,3417)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./sources/MoveCoin.move:91:9+49
    assume {:print "$at(2,3369,3418)"} true;
    assume {:print "$track_abort(1,5):", $t8} $t8 == $t8;

    // $t6 := move($t8) at ./sources/MoveCoin.move:91:9+49
    $t6 := $t8;

    // goto L3 at ./sources/MoveCoin.move:91:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:92:69+4
    assume {:print "$at(2,3488,3492)"} true;
L0:

    // $t9 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:92:32+17
    assume {:print "$at(2,3451,3468)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,3451,3468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t10 := borrow_field<MoveCoin::Balance<#0>>.coin($t9) at ./sources/MoveCoin.move:92:32+47
    $t10 := $ChildMutation($t9, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t9)));

    // $t11 := borrow_field<MoveCoin::Coin<#0>>.value($t10) at ./sources/MoveCoin.move:92:27+58
    $t11 := $ChildMutation($t10, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t10)));

    // trace_local[balance_ref]($t11) at ./sources/MoveCoin.move:92:13+11
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t12 := -($t5, $t1) on_abort goto L3 with $t6 at ./sources/MoveCoin.move:93:32+1
    assume {:print "$at(2,3537,3538)"} true;
    call $t12 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,3537,3538)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,5):", $t6} $t6 == $t6;
        goto L3;
    }

    // write_ref($t11, $t12) at ./sources/MoveCoin.move:93:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at ./sources/MoveCoin.move:93:9+31
    $t10 := $UpdateMutation($t10, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (MoveCoin::Coin<#0>)]($t10) at ./sources/MoveCoin.move:93:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[MoveCoin::Balance<#0>@]($t9) at ./sources/MoveCoin.move:93:9+31
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$at(2,3555,3587)"} true;
    $t13 := $eeee_MoveCoin_Coin'#0'($t1);

    // trace_return[0]($t13) at ./sources/MoveCoin.move:94:9+32
    assume {:print "$track_return(1,5,0):", $t13} $t13 == $t13;

    // label L2 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
L2:

    // assume Identical($t14, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<#0>>($t0)))) at ./sources/MoveCoin.move:103:9+67
    assume {:print "$at(2,3779,3846)"} true;
    assume ($t14 == $value#$eeee_MoveCoin_Coin'#0'($coin#$eeee_MoveCoin_Balance'#0'($ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0))));

    // assert Not(Not(exists[@2]<MoveCoin::Balance<#0>>($t0))) at ./sources/MoveCoin.move:100:9+43
    assume {:print "$at(2,3690,3733)"} true;
    assert {:msg "assert_failed(2,3690,3733): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#2, $t0);

    // assert Not(Lt($t4, $t1)) at ./sources/MoveCoin.move:101:9+27
    assume {:print "$at(2,3742,3769)"} true;
    assert {:msg "assert_failed(2,3742,3769): function does not abort under this condition"}
      !($t4 < $t1);

    // assert Eq<MoveCoin::Coin<#0>>($t13, pack MoveCoin::Coin<#0>($t1)) at ./sources/MoveCoin.move:104:9+51
    assume {:print "$at(2,3855,3906)"} true;
    assert {:msg "assert_failed(2,3855,3906): post-condition does not hold"}
      $IsEqual'$eeee_MoveCoin_Coin'#0''($t13, $eeee_MoveCoin_Coin'#0'($t1));

    // assert Eq<u64>($t14, Sub($t4, $t1)) at ./sources/MoveCoin.move:105:9+41
    assume {:print "$at(2,3915,3956)"} true;
    assert {:msg "assert_failed(2,3915,3956): post-condition does not hold"}
      $IsEqual'u64'($t14, ($t4 - $t1));

    // return $t13 at ./sources/MoveCoin.move:105:9+41
    $ret0 := $t13;
    return;

    // label L3 at ./sources/MoveCoin.move:95:5+1
    assume {:print "$at(2,3592,3593)"} true;
L3:

    // assert Or(Not(exists[@2]<MoveCoin::Balance<#0>>($t0)), Lt($t4, $t1)) at ./sources/MoveCoin.move:97:5+363
    assume {:print "$at(2,3599,3962)"} true;
    assert {:msg "assert_failed(2,3599,3962): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#2, $t0) || ($t4 < $t1));

    // abort($t6) at ./sources/MoveCoin.move:97:5+363
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// struct OddCoin::OddCoin at ./sources/OddCoin.move:7:5+26
type {:datatype} $eeee_OddCoin_OddCoin;
function {:constructor} $eeee_OddCoin_OddCoin($dummy_field: bool): $eeee_OddCoin_OddCoin;
function {:inline} $Update'$eeee_OddCoin_OddCoin'_dummy_field(s: $eeee_OddCoin_OddCoin, x: bool): $eeee_OddCoin_OddCoin {
    $eeee_OddCoin_OddCoin(x)
}
function $IsValid'$eeee_OddCoin_OddCoin'(s: $eeee_OddCoin_OddCoin): bool {
    $IsValid'bool'($dummy_field#$eeee_OddCoin_OddCoin(s))
}
function {:inline} $IsEqual'$eeee_OddCoin_OddCoin'(s1: $eeee_OddCoin_OddCoin, s2: $eeee_OddCoin_OddCoin): bool {
    s1 == s2
}

// fun OddCoin::transfer [verification] at ./sources/OddCoin.move:16:5+210
procedure {:timeLimit 40} $eeee_OddCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: bool;
    var $t10: $eeee_OddCoin_OddCoin;
    var $t11: int;
    var $t12: int;
    var $t13: int;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/OddCoin.move:16:5+1
    assume {:print "$at(24,452,453)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at ./sources/OddCoin.move:16:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/OddCoin.move:16:5+1
    assume $IsValid'u64'($t2);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<OddCoin::OddCoin>>(): WellFormed($rsc) at ./sources/OddCoin.move:16:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''($rsc))));

    // trace_local[from]($t0) at ./sources/OddCoin.move:16:5+1
    assume {:print "$track_local(2,1,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/OddCoin.move:16:5+1
    assume {:print "$track_local(2,1,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/OddCoin.move:16:5+1
    assume {:print "$track_local(2,1,2):", $t2} $t2 == $t2;

    // $t3 := 2 at ./sources/OddCoin.move:18:26+1
    assume {:print "$at(24,571,572)"} true;
    $t3 := 2;
    assume $IsValid'u64'($t3);

    // $t4 := %($t2, $t3) on_abort goto L3 with $t5 at ./sources/OddCoin.move:18:24+1
    call $t4 := $Mod($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(24,569,570)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,1):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t6 := 1 at ./sources/OddCoin.move:18:31+1
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t4, $t6) at ./sources/OddCoin.move:18:28+2
    $t7 := $IsEqual'u64'($t4, $t6);

    // if ($t7) goto L0 else goto L1 at ./sources/OddCoin.move:18:9+34
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./sources/OddCoin.move:18:9+34
L1:

    // $t8 := 0 at ./sources/OddCoin.move:18:34+8
    assume {:print "$at(24,579,587)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./sources/OddCoin.move:18:9+34
    assume {:print "$at(24,554,588)"} true;
    assume {:print "$track_abort(2,1):", $t8} $t8 == $t8;

    // $t5 := move($t8) at ./sources/OddCoin.move:18:9+34
    $t5 := $t8;

    // goto L3 at ./sources/OddCoin.move:18:9+34
    goto L3;

    // label L0 at ./sources/OddCoin.move:19:37+4
    assume {:print "$at(24,626,630)"} true;
L0:

    // $t9 := false at ./sources/OddCoin.move:19:55+10
    assume {:print "$at(24,644,654)"} true;
    $t9 := false;
    assume $IsValid'bool'($t9);

    // $t10 := pack OddCoin::OddCoin($t9) at ./sources/OddCoin.move:19:55+10
    $t10 := $eeee_OddCoin_OddCoin($t9);

    // assume Identical($t11, signer::$address_of($t0)) at ./sources/MoveCoin.move:72:9+41
    assume {:print "$at(2,2514,2555)"} true;
    assume ($t11 == $1_signer_$address_of($t0));

    // assume Identical($t12, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<OddCoin::OddCoin>>($t11)))) at ./sources/MoveCoin.move:74:9+67
    assume {:print "$at(2,2565,2632)"} true;
    assume ($t12 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t11))));

    // assume Identical($t13, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<OddCoin::OddCoin>>($t1)))) at ./sources/MoveCoin.move:75:9+58
    assume {:print "$at(2,2641,2699)"} true;
    assume ($t13 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t1))));

    // MoveCoin::transfer<OddCoin::OddCoin>($t0, $t1, $t2, $t10) on_abort goto L3 with $t5 at ./sources/OddCoin.move:19:9+57
    assume {:print "$at(24,598,655)"} true;
    call $eeee_MoveCoin_transfer'$eeee_OddCoin_OddCoin'($t0, $t1, $t2, $t10);
    if ($abort_flag) {
        assume {:print "$at(24,598,655)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,1):", $t5} $t5 == $t5;
        goto L3;
    }

    // label L2 at ./sources/OddCoin.move:20:5+1
    assume {:print "$at(24,661,662)"} true;
L2:

    // return () at ./sources/OddCoin.move:20:5+1
    assume {:print "$at(24,661,662)"} true;
    return;

    // label L3 at ./sources/OddCoin.move:20:5+1
L3:

    // abort($t5) at ./sources/OddCoin.move:20:5+1
    assume {:print "$at(24,661,662)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun OddCoin::setup_and_mint [verification] at ./sources/OddCoin.move:11:5+199
procedure {:timeLimit 40} $eeee_OddCoin_setup_and_mint$verify(_$t0: $signer, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: $eeee_OddCoin_OddCoin;
    var $t6: int;
    var $t0: $signer;
    var $t1: int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/OddCoin.move:11:5+1
    assume {:print "$at(24,247,248)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at ./sources/OddCoin.move:11:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<OddCoin::OddCoin>>(): WellFormed($rsc) at ./sources/OddCoin.move:11:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''($rsc))));

    // trace_local[account]($t0) at ./sources/OddCoin.move:11:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/OddCoin.move:11:5+1
    assume {:print "$track_local(2,0,1):", $t1} $t1 == $t1;

    // MoveCoin::publish_balance<OddCoin::OddCoin>($t0) on_abort goto L2 with $t2 at ./sources/OddCoin.move:12:9+43
    assume {:print "$at(24,314,357)"} true;
    call $eeee_MoveCoin_publish_balance'$eeee_OddCoin_OddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(24,314,357)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := signer::address_of($t0) on_abort goto L2 with $t2 at ./sources/OddCoin.move:13:33+27
    assume {:print "$at(24,391,418)"} true;
    call $t3 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(24,391,418)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t4 := false at ./sources/OddCoin.move:13:70+10
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := pack OddCoin::OddCoin($t4) at ./sources/OddCoin.move:13:70+10
    $t5 := $eeee_OddCoin_OddCoin($t4);

    // assume Identical($t6, select MoveCoin::Coin.value(select MoveCoin::Balance.coin(global<MoveCoin::Balance<OddCoin::OddCoin>>($t3)))) at ./sources/MoveCoin.move:129:9+57
    assume {:print "$at(2,4726,4783)"} true;
    assume ($t6 == $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t3))));

    // MoveCoin::mint<OddCoin::OddCoin>($t3, $t1, $t5) on_abort goto L2 with $t2 at ./sources/OddCoin.move:13:9+72
    assume {:print "$at(24,367,439)"} true;
    call $eeee_MoveCoin_mint'$eeee_OddCoin_OddCoin'($t3, $t1, $t5);
    if ($abort_flag) {
        assume {:print "$at(24,367,439)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at ./sources/OddCoin.move:14:5+1
    assume {:print "$at(24,445,446)"} true;
L1:

    // return () at ./sources/OddCoin.move:14:5+1
    assume {:print "$at(24,445,446)"} true;
    return;

    // label L2 at ./sources/OddCoin.move:14:5+1
L2:

    // abort($t2) at ./sources/OddCoin.move:14:5+1
    assume {:print "$at(24,445,446)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
