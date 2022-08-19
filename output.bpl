
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
    assume {:print "$at(4,389,390)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:13:10+17
    assume {:print "$at(4,443,460)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(4,443,460)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(4,465,466)"} true;
L1:

    // return $t1 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(4,465,466)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
L2:

    // abort($t2) at /Users/admin/.move/https___github_com_move-language_move_git_main/language/move-stdlib/nursery/../sources/signer.move:14:5+1
    assume {:print "$at(4,465,466)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct MoveCoin::Balance<OddCoin::OddCoin> at ./sources/MoveCoin.move:14:5+77
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

// struct MoveCoin::Balance<#0> at ./sources/MoveCoin.move:14:5+77
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

// struct MoveCoin::Coin<OddCoin::OddCoin> at ./sources/MoveCoin.move:10:5+66
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

// struct MoveCoin::Coin<#0> at ./sources/MoveCoin.move:10:5+66
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

// fun MoveCoin::balance_of<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:33:5+136
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
    // trace_local[owner]($t0) at ./sources/MoveCoin.move:33:5+1
    assume {:print "$at(20,1274,1275)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:34:9+13
    assume {:print "$at(20,1354,1367)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(20,1354,1367)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:34:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:34:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:34:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
L1:

    // return $t4 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:35:5+1
L2:

    // abort($t2) at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::balance_of<#0> [baseline] at ./sources/MoveCoin.move:33:5+136
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
    // trace_local[owner]($t0) at ./sources/MoveCoin.move:33:5+1
    assume {:print "$at(20,1274,1275)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:34:9+13
    assume {:print "$at(20,1354,1367)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(20,1354,1367)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:34:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'#0'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:34:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:34:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
L1:

    // return $t4 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:35:5+1
L2:

    // abort($t2) at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::balance_of [verification] at ./sources/MoveCoin.move:33:5+136
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
    // assume WellFormed($t0) at ./sources/MoveCoin.move:33:5+1
    assume {:print "$at(20,1274,1275)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:33:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // @0 := save_mem(MoveCoin::Balance<#0>) at ./sources/MoveCoin.move:33:5+1
    $eeee_MoveCoin_Balance'#0'_$memory#0 := $eeee_MoveCoin_Balance'#0'_$memory;

    // trace_local[owner]($t0) at ./sources/MoveCoin.move:33:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at ./sources/MoveCoin.move:34:9+13
    assume {:print "$at(20,1354,1367)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(20,1354,1367)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<MoveCoin::Balance<#0>>.coin($t1) at ./sources/MoveCoin.move:34:9+44
    $t3 := $coin#$eeee_MoveCoin_Balance'#0'($t1);

    // $t4 := get_field<MoveCoin::Coin<#0>>.value($t3) at ./sources/MoveCoin.move:34:9+50
    $t4 := $value#$eeee_MoveCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at ./sources/MoveCoin.move:34:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
L1:

    // assert Not(Not(exists[@0]<MoveCoin::Balance<#0>>($t0))) at ./sources/MoveCoin.move:39:9+44
    assume {:print "$at(20,1478,1522)"} true;
    assert {:msg "assert_failed(20,1478,1522): function does not abort under this condition"}
      !!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#0, $t0);

    // return $t4 at ./sources/MoveCoin.move:39:9+44
    $ret0 := $t4;
    return;

    // label L2 at ./sources/MoveCoin.move:35:5+1
    assume {:print "$at(20,1409,1410)"} true;
L2:

    // assert Not(exists[@0]<MoveCoin::Balance<#0>>($t0)) at ./sources/MoveCoin.move:37:5+112
    assume {:print "$at(20,1416,1528)"} true;
    assert {:msg "assert_failed(20,1416,1528): abort not covered by any of the `aborts_if` clauses"}
      !$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory#0, $t0);

    // abort($t2) at ./sources/MoveCoin.move:37:5+112
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:57:5+295
procedure {:inline 1} $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin');
    var $t8: $Mutation ($eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'': $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$at(20,2338,2339)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:58:23+26
    assume {:print "$at(20,2438,2464)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'$eeee_OddCoin_OddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2438,2464)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:58:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:59:32+17
    assume {:print "$at(20,2497,2514)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2497,2514)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<MoveCoin::Balance<#0>>.coin($t7) at ./sources/MoveCoin.move:59:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($Dereference($t7)));

    // $t9 := borrow_field<MoveCoin::Coin<#0>>.value($t8) at ./sources/MoveCoin.move:59:27+58
    $t9 := $ChildMutation($t8, 0, $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at ./sources/MoveCoin.move:59:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:60:13+14
    assume {:print "$at(20,2564,2578)"} true;
    $t10 := $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // trace_local[value]($t10) at ./sources/MoveCoin.move:60:20+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:61:32+1
    assume {:print "$at(20,2619,2620)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(20,2619,2620)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at ./sources/MoveCoin.move:61:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at ./sources/MoveCoin.move:61:9+30
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (MoveCoin::Coin<#0>)]($t8) at ./sources/MoveCoin.move:61:9+30
    $t7 := $UpdateMutation($t7, $Update'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[MoveCoin::Balance<#0>@]($t7) at ./sources/MoveCoin.move:61:9+30
    $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
L1:

    // return () at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:62:5+1
L2:

    // abort($t6) at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit<#0> [baseline] at ./sources/MoveCoin.move:57:5+295
procedure {:inline 1} $eeee_MoveCoin_deposit'#0'(_$t0: int, _$t1: $eeee_MoveCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t8: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'#0';
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$at(20,2338,2339)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:58:23+26
    assume {:print "$at(20,2438,2464)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2438,2464)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:58:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:59:32+17
    assume {:print "$at(20,2497,2514)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2497,2514)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<MoveCoin::Balance<#0>>.coin($t7) at ./sources/MoveCoin.move:59:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t7)));

    // $t9 := borrow_field<MoveCoin::Coin<#0>>.value($t8) at ./sources/MoveCoin.move:59:27+58
    $t9 := $ChildMutation($t8, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at ./sources/MoveCoin.move:59:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:60:13+14
    assume {:print "$at(20,2564,2578)"} true;
    $t10 := $value#$eeee_MoveCoin_Coin'#0'($t1);

    // trace_local[value]($t10) at ./sources/MoveCoin.move:60:20+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:61:32+1
    assume {:print "$at(20,2619,2620)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(20,2619,2620)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at ./sources/MoveCoin.move:61:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at ./sources/MoveCoin.move:61:9+30
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (MoveCoin::Coin<#0>)]($t8) at ./sources/MoveCoin.move:61:9+30
    $t7 := $UpdateMutation($t7, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[MoveCoin::Balance<#0>@]($t7) at ./sources/MoveCoin.move:61:9+30
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
L1:

    // return () at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:62:5+1
L2:

    // abort($t6) at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::deposit [verification] at ./sources/MoveCoin.move:57:5+295
procedure {:timeLimit 40} $eeee_MoveCoin_deposit$verify(_$t0: int, _$t1: $eeee_MoveCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t8: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $eeee_MoveCoin_Coin'#0';
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$at(20,2338,2339)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:57:5+1
    assume $IsValid'$eeee_MoveCoin_Coin'#0''($t1);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:57:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at ./sources/MoveCoin.move:57:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := MoveCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:58:23+26
    assume {:print "$at(20,2438,2464)"} true;
    call $t5 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2438,2464)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at ./sources/MoveCoin.move:58:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:59:32+17
    assume {:print "$at(20,2497,2514)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2497,2514)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<MoveCoin::Balance<#0>>.coin($t7) at ./sources/MoveCoin.move:59:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t7)));

    // $t9 := borrow_field<MoveCoin::Coin<#0>>.value($t8) at ./sources/MoveCoin.move:59:27+58
    $t9 := $ChildMutation($t8, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at ./sources/MoveCoin.move:59:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:60:13+14
    assume {:print "$at(20,2564,2578)"} true;
    $t10 := $value#$eeee_MoveCoin_Coin'#0'($t1);

    // trace_local[value]($t10) at ./sources/MoveCoin.move:60:20+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:61:32+1
    assume {:print "$at(20,2619,2620)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(20,2619,2620)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at ./sources/MoveCoin.move:61:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at ./sources/MoveCoin.move:61:9+30
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (MoveCoin::Coin<#0>)]($t8) at ./sources/MoveCoin.move:61:9+30
    $t7 := $UpdateMutation($t7, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[MoveCoin::Balance<#0>@]($t7) at ./sources/MoveCoin.move:61:9+30
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
L1:

    // return () at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:62:5+1
L2:

    // abort($t6) at ./sources/MoveCoin.move:62:5+1
    assume {:print "$at(20,2632,2633)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::mint<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:28:5+244
procedure {:inline 1} $eeee_MoveCoin_mint'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: int, _$t2: $eeee_OddCoin_OddCoin) returns ()
{
    // declare local variables
    var $t3: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t4: int;
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
    // trace_local[mint_addr]($t0) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$at(20,1024,1025)"} true;
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t3 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:30:28+32
    assume {:print "$at(20,1228,1260)"} true;
    $t3 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // MoveCoin::deposit<#0>($t0, $t3) on_abort goto L2 with $t4 at ./sources/MoveCoin.move:30:9+52
    call $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'($t0, $t3);
    if ($abort_flag) {
        assume {:print "$at(20,1209,1261)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
L1:

    // return () at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:31:5+1
L2:

    // abort($t4) at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun MoveCoin::mint [verification] at ./sources/MoveCoin.move:28:5+244
procedure {:timeLimit 40} $eeee_MoveCoin_mint$verify(_$t0: int, _$t1: int, _$t2: #0) returns ()
{
    // declare local variables
    var $t3: $eeee_MoveCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $t1: int;
    var $t2: #0;
    var $temp_0'#0': #0;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$at(20,1024,1025)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:28:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at ./sources/MoveCoin.move:28:5+1
    assume $IsValid'#0'($t2);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:28:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // trace_local[mint_addr]($t0) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at ./sources/MoveCoin.move:28:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t3 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:30:28+32
    assume {:print "$at(20,1228,1260)"} true;
    $t3 := $eeee_MoveCoin_Coin'#0'($t1);

    // MoveCoin::deposit<#0>($t0, $t3) on_abort goto L2 with $t4 at ./sources/MoveCoin.move:30:9+52
    call $eeee_MoveCoin_deposit'#0'($t0, $t3);
    if ($abort_flag) {
        assume {:print "$at(20,1209,1261)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
L1:

    // return () at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:31:5+1
L2:

    // abort($t4) at ./sources/MoveCoin.move:31:5+1
    assume {:print "$at(20,1267,1268)"} true;
    $abort_code := $t4;
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
    assume {:print "$at(20,569,570)"} true;
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t2 := signer::address_of($t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:22:44+27
    assume {:print "$at(20,723,750)"} true;
    call $t2 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(20,723,750)"} true;
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
    assume {:print "$at(20,753,773)"} true;
    $t6 := 2;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/MoveCoin.move:22:9+86
    assume {:print "$at(20,688,774)"} true;
    assume {:print "$track_abort(1,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/MoveCoin.move:22:9+86
    $t3 := $t6;

    // goto L3 at ./sources/MoveCoin.move:22:9+86
    goto L3;

    // label L0 at ./sources/MoveCoin.move:23:17+7
    assume {:print "$at(20,792,799)"} true;
L0:

    // $t7 := 0 at ./sources/MoveCoin.move:21:50+1
    assume {:print "$at(20,675,676)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack MoveCoin::Coin<#0>($t7) at ./sources/MoveCoin.move:21:26+27
    $t8 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t7);

    // $t9 := pack MoveCoin::Balance<#0>($t8) at ./sources/MoveCoin.move:23:26+38
    assume {:print "$at(20,801,839)"} true;
    $t9 := $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($t8);

    // move_to<MoveCoin::Balance<#0>>($t9, $t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:23:9+7
    if ($ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(20,784,791)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
L2:

    // return () at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
    return;

    // label L3 at ./sources/MoveCoin.move:24:5+1
L3:

    // abort($t3) at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
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
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:20:5+1
    assume {:print "$at(20,569,570)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:20:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // trace_local[account]($t0) at ./sources/MoveCoin.move:20:5+1
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t2 := signer::address_of($t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:22:44+27
    assume {:print "$at(20,723,750)"} true;
    call $t2 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(20,723,750)"} true;
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
    assume {:print "$at(20,753,773)"} true;
    $t6 := 2;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/MoveCoin.move:22:9+86
    assume {:print "$at(20,688,774)"} true;
    assume {:print "$track_abort(1,3):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/MoveCoin.move:22:9+86
    $t3 := $t6;

    // goto L3 at ./sources/MoveCoin.move:22:9+86
    goto L3;

    // label L0 at ./sources/MoveCoin.move:23:17+7
    assume {:print "$at(20,792,799)"} true;
L0:

    // $t7 := 0 at ./sources/MoveCoin.move:21:50+1
    assume {:print "$at(20,675,676)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack MoveCoin::Coin<#0>($t7) at ./sources/MoveCoin.move:21:26+27
    $t8 := $eeee_MoveCoin_Coin'#0'($t7);

    // $t9 := pack MoveCoin::Balance<#0>($t8) at ./sources/MoveCoin.move:23:26+38
    assume {:print "$at(20,801,839)"} true;
    $t9 := $eeee_MoveCoin_Balance'#0'($t8);

    // move_to<MoveCoin::Balance<#0>>($t9, $t0) on_abort goto L3 with $t3 at ./sources/MoveCoin.move:23:9+7
    if ($ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(20,784,791)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,3):", $t3} $t3 == $t3;
        goto L3;
    }

    // label L2 at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
L2:

    // return () at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
    return;

    // label L3 at ./sources/MoveCoin.move:24:5+1
L3:

    // abort($t3) at ./sources/MoveCoin.move:24:5+1
    assume {:print "$at(20,846,847)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun MoveCoin::transfer<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:44:5+233
procedure {:inline 1} $eeee_MoveCoin_transfer'$eeee_OddCoin_OddCoin'(_$t0: $signer, _$t1: int, _$t2: int, _$t3: $eeee_OddCoin_OddCoin) returns ()
{
    // declare local variables
    var $t4: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t5: int;
    var $t6: int;
    var $t7: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
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
    // trace_local[from]($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$at(20,1724,1725)"} true;
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t5 := signer::address_of($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:45:40+24
    assume {:print "$at(20,1879,1903)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(20,1879,1903)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := MoveCoin::withdraw<#0>($t5, $t2) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:45:21+52
    call $t7 := $eeee_MoveCoin_withdraw'$eeee_OddCoin_OddCoin'($t5, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,1860,1912)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[check]($t7) at ./sources/MoveCoin.move:45:13+5
    assume {:print "$track_local(1,4,4):", $t7} $t7 == $t7;

    // MoveCoin::deposit<#0>($t1, $t7) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:46:9+28
    assume {:print "$at(20,1922,1950)"} true;
    call $eeee_MoveCoin_deposit'$eeee_OddCoin_OddCoin'($t1, $t7);
    if ($abort_flag) {
        assume {:print "$at(20,1922,1950)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
L1:

    // return () at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:47:5+1
L2:

    // abort($t6) at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::transfer [verification] at ./sources/MoveCoin.move:44:5+233
procedure {:timeLimit 40} $eeee_MoveCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int, _$t3: #0) returns ()
{
    // declare local variables
    var $t4: $eeee_MoveCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: $eeee_MoveCoin_Coin'#0';
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: #0;
    var $temp_0'#0': #0;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$at(20,1724,1725)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at ./sources/MoveCoin.move:44:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/MoveCoin.move:44:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at ./sources/MoveCoin.move:44:5+1
    assume $IsValid'#0'($t3);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:44:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // trace_local[from]($t0) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at ./sources/MoveCoin.move:44:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t5 := signer::address_of($t0) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:45:40+24
    assume {:print "$at(20,1879,1903)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(20,1879,1903)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := MoveCoin::withdraw<#0>($t5, $t2) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:45:21+52
    call $t7 := $eeee_MoveCoin_withdraw'#0'($t5, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,1860,1912)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[check]($t7) at ./sources/MoveCoin.move:45:13+5
    assume {:print "$track_local(1,4,4):", $t7} $t7 == $t7;

    // MoveCoin::deposit<#0>($t1, $t7) on_abort goto L2 with $t6 at ./sources/MoveCoin.move:46:9+28
    assume {:print "$at(20,1922,1950)"} true;
    call $eeee_MoveCoin_deposit'#0'($t1, $t7);
    if ($abort_flag) {
        assume {:print "$at(20,1922,1950)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
L1:

    // return () at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
    return;

    // label L2 at ./sources/MoveCoin.move:47:5+1
L2:

    // abort($t6) at ./sources/MoveCoin.move:47:5+1
    assume {:print "$at(20,1956,1957)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw<OddCoin::OddCoin> [baseline] at ./sources/MoveCoin.move:49:5+369
procedure {:inline 1} $eeee_MoveCoin_withdraw'$eeee_OddCoin_OddCoin'(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin');
    var $t9: $Mutation ($eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'': $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$at(20,1963,1964)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:50:23+26
    assume {:print "$at(20,2072,2098)"} true;
    call $t4 := $eeee_MoveCoin_balance_of'$eeee_OddCoin_OddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2072,2098)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_local[balance]($t4) at ./sources/MoveCoin.move:50:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at ./sources/MoveCoin.move:51:25+2
    assume {:print "$at(20,2124,2126)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L0 else goto L1 at ./sources/MoveCoin.move:51:9+49
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:51:36+21
L1:

    // $t7 := 1 at ./sources/MoveCoin.move:51:36+21
    assume {:print "$at(20,2135,2156)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at ./sources/MoveCoin.move:51:9+49
    assume {:print "$at(20,2108,2157)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at ./sources/MoveCoin.move:51:9+49
    $t5 := $t7;

    // goto L3 at ./sources/MoveCoin.move:51:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:52:69+4
    assume {:print "$at(20,2227,2231)"} true;
L0:

    // $t8 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:52:32+17
    assume {:print "$at(20,2190,2207)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2190,2207)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t9 := borrow_field<MoveCoin::Balance<#0>>.coin($t8) at ./sources/MoveCoin.move:52:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'($Dereference($t8)));

    // $t10 := borrow_field<MoveCoin::Coin<#0>>.value($t9) at ./sources/MoveCoin.move:52:27+58
    $t10 := $ChildMutation($t9, 0, $value#$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at ./sources/MoveCoin.move:52:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:53:32+1
    assume {:print "$at(20,2276,2277)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,2276,2277)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // write_ref($t10, $t11) at ./sources/MoveCoin.move:53:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at ./sources/MoveCoin.move:53:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (MoveCoin::Coin<#0>)]($t9) at ./sources/MoveCoin.move:53:9+31
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[MoveCoin::Balance<#0>@]($t8) at ./sources/MoveCoin.move:53:9+31
    $eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'$eeee_OddCoin_OddCoin'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$at(20,2294,2326)"} true;
    $t12 := $eeee_MoveCoin_Coin'$eeee_OddCoin_OddCoin'($t1);

    // trace_return[0]($t12) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L2 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
L2:

    // return $t12 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $ret0 := $t12;
    return;

    // label L3 at ./sources/MoveCoin.move:55:5+1
L3:

    // abort($t5) at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw<#0> [baseline] at ./sources/MoveCoin.move:49:5+369
procedure {:inline 1} $eeee_MoveCoin_withdraw'#0'(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t9: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $eeee_MoveCoin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$at(20,1963,1964)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:50:23+26
    assume {:print "$at(20,2072,2098)"} true;
    call $t4 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2072,2098)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_local[balance]($t4) at ./sources/MoveCoin.move:50:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at ./sources/MoveCoin.move:51:25+2
    assume {:print "$at(20,2124,2126)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L0 else goto L1 at ./sources/MoveCoin.move:51:9+49
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:51:36+21
L1:

    // $t7 := 1 at ./sources/MoveCoin.move:51:36+21
    assume {:print "$at(20,2135,2156)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at ./sources/MoveCoin.move:51:9+49
    assume {:print "$at(20,2108,2157)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at ./sources/MoveCoin.move:51:9+49
    $t5 := $t7;

    // goto L3 at ./sources/MoveCoin.move:51:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:52:69+4
    assume {:print "$at(20,2227,2231)"} true;
L0:

    // $t8 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:52:32+17
    assume {:print "$at(20,2190,2207)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2190,2207)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t9 := borrow_field<MoveCoin::Balance<#0>>.coin($t8) at ./sources/MoveCoin.move:52:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t8)));

    // $t10 := borrow_field<MoveCoin::Coin<#0>>.value($t9) at ./sources/MoveCoin.move:52:27+58
    $t10 := $ChildMutation($t9, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at ./sources/MoveCoin.move:52:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:53:32+1
    assume {:print "$at(20,2276,2277)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,2276,2277)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // write_ref($t10, $t11) at ./sources/MoveCoin.move:53:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at ./sources/MoveCoin.move:53:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (MoveCoin::Coin<#0>)]($t9) at ./sources/MoveCoin.move:53:9+31
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[MoveCoin::Balance<#0>@]($t8) at ./sources/MoveCoin.move:53:9+31
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$at(20,2294,2326)"} true;
    $t12 := $eeee_MoveCoin_Coin'#0'($t1);

    // trace_return[0]($t12) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L2 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
L2:

    // return $t12 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $ret0 := $t12;
    return;

    // label L3 at ./sources/MoveCoin.move:55:5+1
L3:

    // abort($t5) at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun MoveCoin::withdraw [verification] at ./sources/MoveCoin.move:49:5+369
procedure {:timeLimit 40} $eeee_MoveCoin_withdraw$verify(_$t0: int, _$t1: int) returns ($ret0: $eeee_MoveCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($eeee_MoveCoin_Balance'#0');
    var $t9: $Mutation ($eeee_MoveCoin_Coin'#0');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $eeee_MoveCoin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $temp_0'$eeee_MoveCoin_Coin'#0'': $eeee_MoveCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$at(20,1963,1964)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/MoveCoin.move:49:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<MoveCoin::Balance<#0>>(): WellFormed($rsc) at ./sources/MoveCoin.move:49:5+1
    assume (forall $a_0: int :: {$ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$eeee_MoveCoin_Balance'#0''($rsc))));

    // trace_local[addr]($t0) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/MoveCoin.move:49:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := MoveCoin::balance_of<#0>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:50:23+26
    assume {:print "$at(20,2072,2098)"} true;
    call $t4 := $eeee_MoveCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,2072,2098)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_local[balance]($t4) at ./sources/MoveCoin.move:50:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at ./sources/MoveCoin.move:51:25+2
    assume {:print "$at(20,2124,2126)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L0 else goto L1 at ./sources/MoveCoin.move:51:9+49
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at ./sources/MoveCoin.move:51:36+21
L1:

    // $t7 := 1 at ./sources/MoveCoin.move:51:36+21
    assume {:print "$at(20,2135,2156)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at ./sources/MoveCoin.move:51:9+49
    assume {:print "$at(20,2108,2157)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at ./sources/MoveCoin.move:51:9+49
    $t5 := $t7;

    // goto L3 at ./sources/MoveCoin.move:51:9+49
    goto L3;

    // label L0 at ./sources/MoveCoin.move:52:69+4
    assume {:print "$at(20,2227,2231)"} true;
L0:

    // $t8 := borrow_global<MoveCoin::Balance<#0>>($t0) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:52:32+17
    assume {:print "$at(20,2190,2207)"} true;
    if (!$ResourceExists($eeee_MoveCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($eeee_MoveCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(20,2190,2207)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t9 := borrow_field<MoveCoin::Balance<#0>>.coin($t8) at ./sources/MoveCoin.move:52:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$eeee_MoveCoin_Balance'#0'($Dereference($t8)));

    // $t10 := borrow_field<MoveCoin::Coin<#0>>.value($t9) at ./sources/MoveCoin.move:52:27+58
    $t10 := $ChildMutation($t9, 0, $value#$eeee_MoveCoin_Coin'#0'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at ./sources/MoveCoin.move:52:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L3 with $t5 at ./sources/MoveCoin.move:53:32+1
    assume {:print "$at(20,2276,2277)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,2276,2277)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // write_ref($t10, $t11) at ./sources/MoveCoin.move:53:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at ./sources/MoveCoin.move:53:9+31
    $t9 := $UpdateMutation($t9, $Update'$eeee_MoveCoin_Coin'#0''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (MoveCoin::Coin<#0>)]($t9) at ./sources/MoveCoin.move:53:9+31
    $t8 := $UpdateMutation($t8, $Update'$eeee_MoveCoin_Balance'#0''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[MoveCoin::Balance<#0>@]($t8) at ./sources/MoveCoin.move:53:9+31
    $eeee_MoveCoin_Balance'#0'_$memory := $ResourceUpdate($eeee_MoveCoin_Balance'#0'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack MoveCoin::Coin<#0>($t1) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$at(20,2294,2326)"} true;
    $t12 := $eeee_MoveCoin_Coin'#0'($t1);

    // trace_return[0]($t12) at ./sources/MoveCoin.move:54:9+32
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L2 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
L2:

    // return $t12 at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $ret0 := $t12;
    return;

    // label L3 at ./sources/MoveCoin.move:55:5+1
L3:

    // abort($t5) at ./sources/MoveCoin.move:55:5+1
    assume {:print "$at(20,2331,2332)"} true;
    $abort_code := $t5;
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

    // MoveCoin::transfer<OddCoin::OddCoin>($t0, $t1, $t2, $t10) on_abort goto L3 with $t5 at ./sources/OddCoin.move:19:9+57
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

    // MoveCoin::mint<OddCoin::OddCoin>($t3, $t1, $t5) on_abort goto L2 with $t2 at ./sources/OddCoin.move:13:9+72
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
