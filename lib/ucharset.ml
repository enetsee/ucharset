(* A sorted list of disjoint, non-adjacent inclusive ranges *)
type t = { ivals : int array } [@@unboxed]

(* [Stdlib.max] is a polymorphic function; at [int] this one compiles to a
   compare and a branch. *)
let[@inline] max (a : int) b = if a >= b then a else b

(* Every [Invalid_argument] this module raises is built here, so the library
   name the message carries is written once instead of once per raise site. *)
let fail ?fn msg =
  match fn with
  | None -> invalid_arg ("Ucharset: " ^ msg)
  | Some fn -> invalid_arg ("Ucharset." ^ fn ^ ": " ^ msg)
;;

(* [Builder.build] packs a (lo, hi) pair into a single int and sorts on the
   42-bit key, which needs a 63-bit int. OCaml's int is 31 bits on 32-bit native
   targets and 32 under js_of_ocaml; there the key wraps, the radix sort's digit
   extraction is on an unspecified shift, and sets come back silently wrong —
   [of_intervals [ 0x10FFFF, 0x10FFFF ]] yields a millionfold set rather than a
   singleton. Refuse to run instead. Not an [assert]: [-noassert] would strip it
   and restore the corruption. *)
let () =
  if Sys.int_size < 63
  then
    failwith "Ucharset: needs a 64-bit target; int is too narrow for the packed sort key"
;;

(* -- Distinguished codepoints ---------------------------------------------- *)
let max_codepoint = 0x10FFFF
let surrogate_lo = 0xD800
let surrogate_hi = 0xDFFF

let validate_codepoint cp =
  if cp < 0 || cp > max_codepoint
  then fail "codepoint out of range"
  else if cp >= surrogate_lo && cp <= surrogate_hi
  then fail "surrogate codepoint is not a scalar value"
;;

(* -- Top and bottom -------------------------------------------------------- *)

let empty : t = { ivals = [||] }
let all : t = { ivals = [| 0; surrogate_lo - 1; surrogate_hi + 1; max_codepoint |] }

(* -- Shape ----------------------------------------------------------------- *)

let is_empty t = Array.length t.ivals = 0

(* Canonical form makes this a shape test. *)
let is_all t =
  t == all
  ||
  let a = t.ivals in
  Array.length a = 4
  && a.(0) = 0
  && a.(1) = surrogate_lo - 1
  && a.(2) = surrogate_hi + 1
  && a.(3) = max_codepoint
;;

let num_intervals t = Array.length t.ivals / 2
let is_singleton t = Array.length t.ivals = 2 && t.ivals.(0) = t.ivals.(1)

(* -- Constructors ---------------------------------------------------------- *)

let singleton cp =
  validate_codepoint cp;
  { ivals = [| cp; cp |] }
;;

let singleton_char c = singleton (Char.code c)

(* A [Uchar.t] is a scalar value by construction; the [_uchar] family has
   nothing to validate. *)
let singleton_uchar u =
  let cp = Uchar.to_int u in
  { ivals = [| cp; cp |] }
;;

let range ~lo ~hi =
  validate_codepoint lo;
  validate_codepoint hi;
  if lo > hi
  then empty
  else if hi < surrogate_lo || lo > surrogate_hi
  then { ivals = [| lo; hi |] }
  else
    (* [lo] and [hi] are valid scalar values straddling the surrogate
       block, so lo < 0xD800 and hi > 0xDFFF. *)
    { ivals = [| lo; surrogate_lo - 1; surrogate_hi + 1; hi |] }
;;

let range_char ~lo ~hi = range ~lo:(Char.code lo) ~hi:(Char.code hi)
let range_uchar ~lo ~hi = range ~lo:(Uchar.to_int lo) ~hi:(Uchar.to_int hi)

(* -- Membership ------------------------------------------------------------ *)

(* Binary search for the interval that could contain [cp]. Unsafe accesses:
   [mid] lies in [lo_idx, hi_idx), within [0, num_intervals t), so [mid * 2 + 1]
   is in bounds. *)
let mem t cp =
  let a = t.ivals in
  let rec go lo_idx hi_idx =
    lo_idx < hi_idx
    &&
    let mid = (lo_idx + hi_idx) / 2 in
    if cp < Array.unsafe_get a (mid * 2)
    then go lo_idx mid
    else if cp > Array.unsafe_get a ((mid * 2) + 1)
    then go (mid + 1) hi_idx
    else true
  in
  go 0 (Array.length a / 2)
;;

let mem_char t c = mem t (Char.code c)
let mem_uchar t u = mem t (Uchar.to_int u)

(* Successor and predecessor, O(log n). [cp] need not be a member, or even a
   scalar value, so these double as "seek from here". *)
let next_elt_opt t cp =
  let a = t.ivals in
  let n = Array.length a / 2 in
  (* first interval ending strictly after [cp] *)
  let lo = ref 0
  and hi = ref n in
  while !lo < !hi do
    let mid = (!lo + !hi) / 2 in
    if Array.unsafe_get a ((mid * 2) + 1) <= cp then lo := mid + 1 else hi := mid
  done;
  if !lo >= n
  then None
  else (
    let ilo = a.(!lo * 2) in
    if ilo > cp then Some ilo else Some (cp + 1))
;;

let prev_elt_opt t cp =
  let a = t.ivals in
  let n = Array.length a / 2 in
  (* one past the last interval starting strictly before [cp] *)
  let lo = ref 0
  and hi = ref n in
  while !lo < !hi do
    let mid = (!lo + !hi) / 2 in
    if Array.unsafe_get a (mid * 2) < cp then lo := mid + 1 else hi := mid
  done;
  if !lo = 0
  then None
  else (
    let ihi = a.(((!lo - 1) * 2) + 1) in
    if ihi < cp then Some ihi else Some (cp - 1))
;;

(* -- Queries --------------------------------------------------------------- *)

let cardinal t =
  let a = t.ivals in
  let n = Array.length a / 2 in
  let total = ref 0 in
  for i = 0 to n - 1 do
    total := !total + a.((i * 2) + 1) - a.(i * 2) + 1
  done;
  !total
;;

let choose_opt t = if is_empty t then None else Some t.ivals.(0)
let min_elt_opt = choose_opt

let max_elt_opt t =
  let n = Array.length t.ivals in
  if n = 0 then None else Some t.ivals.(n - 1)
;;

(* -- Iteration ------------------------------------------------------------- *)

let iter_intervals f t =
  let a = t.ivals in
  let n = Array.length a / 2 in
  for i = 0 to n - 1 do
    f a.(i * 2) a.((i * 2) + 1)
  done
;;

let iter f t =
  iter_intervals
    (fun lo hi ->
       for cp = lo to hi do
         f cp
       done)
    t
;;

let fold f t init =
  let a = t.ivals in
  let n = Array.length a in
  let acc = ref init in
  let i = ref 0 in
  while !i < n do
    let hi = Array.unsafe_get a (!i + 1) in
    for cp = Array.unsafe_get a !i to hi do
      acc := f cp !acc
    done;
    i := !i + 2
  done;
  !acc
;;

let fold_intervals f t init =
  let a = t.ivals in
  let n = Array.length a / 2 in
  let acc = ref init in
  for i = 0 to n - 1 do
    acc := f a.(i * 2) a.((i * 2) + 1) !acc
  done;
  !acc
;;

let exists f t =
  let a = t.ivals in
  let n = Array.length a in
  let found = ref false in
  let i = ref 0 in
  while (not !found) && !i < n do
    let hi = Array.unsafe_get a (!i + 1) in
    let cp = ref (Array.unsafe_get a !i) in
    while (not !found) && !cp <= hi do
      if f !cp then found := true else incr cp
    done;
    i := !i + 2
  done;
  !found
;;

let for_all f t =
  let a = t.ivals in
  let n = Array.length a in
  let failed = ref false in
  let i = ref 0 in
  while (not !failed) && !i < n do
    let hi = Array.unsafe_get a (!i + 1) in
    let cp = ref (Array.unsafe_get a !i) in
    while (not !failed) && !cp <= hi do
      if f !cp then incr cp else failed := true
    done;
    i := !i + 2
  done;
  not !failed
;;

let to_seq_intervals t =
  let a = t.ivals in
  let n = Array.length a / 2 in
  let rec go i () =
    if i >= n then Seq.Nil else Seq.Cons ((a.(i * 2), a.((i * 2) + 1)), go (i + 1))
  in
  go 0
;;

let to_seq t =
  let a = t.ivals in
  let n = Array.length a / 2 in
  let rec from i () = if i >= n then Seq.Nil else run i a.(i * 2) ()
  and run i cp () =
    if cp > a.((i * 2) + 1) then from (i + 1) () else Seq.Cons (cp, run i (cp + 1))
  in
  from 0
;;

let to_list t =
  let a = t.ivals in
  let acc = ref [] in
  let n = Array.length a / 2 in
  for i = n - 1 downto 0 do
    acc := (a.(i * 2), a.((i * 2) + 1)) :: !acc
  done;
  !acc
;;

(* -- Canonical buffers ----------------------------------------------------- *)

(* Push an interval at offset [!len], merging with the previous one if they
   overlap or abut. Returns [true] when the push changed nothing (the interval
   was already covered), which [union] uses to spot that it is reproducing an
   input verbatim. Unsafe accesses: callers guarantee capacity. *)
let push_canonical buf len ~lo ~hi =
  if !len > 0 && Array.unsafe_get buf (!len - 1) + 1 >= lo
  then (
    let prev = Array.unsafe_get buf (!len - 1) in
    if hi <= prev
    then true
    else (
      Array.unsafe_set buf (!len - 1) hi;
      false))
  else (
    Array.unsafe_set buf !len lo;
    Array.unsafe_set buf (!len + 1) hi;
    len := !len + 2;
    false)
;;

let trim (buf : int array) len =
  if len = Array.length buf then buf else Array.sub buf 0 len
;;

(* -- Set operations -------------------------------------------------------- *)

(* Two-pointer merge over canonical inputs; [push_canonical] merges only where
   the two meet, since within each the invariants already hold. *)
let union t1 t2 =
  if is_empty t1
  then t2
  else if is_empty t2
  then t1
  else if t1 == t2
  then t1
  else (
    let a1 = t1.ivals
    and a2 = t2.ivals in
    let n1 = Array.length a1 / 2 in
    let n2 = Array.length a2 / 2 in
    let buf = Array.make ((n1 + n2) * 2) 0 in
    let len = ref 0 in
    let i1 = ref 0
    and i2 = ref 0 in
    let pure_t1 = ref true
    and pure_t2 = ref true in
    (* Unsafe accesses: [!i1 < n1] and [!i2 < n2] bound every index. *)
    while !i1 < n1 && !i2 < n2 do
      let lo1 = Array.unsafe_get a1 (!i1 * 2)
      and hi1 = Array.unsafe_get a1 ((!i1 * 2) + 1) in
      let lo2 = Array.unsafe_get a2 (!i2 * 2)
      and hi2 = Array.unsafe_get a2 ((!i2 * 2) + 1) in
      if lo1 <= lo2
      then (
        if not (push_canonical buf len ~lo:lo1 ~hi:hi1) then pure_t2 := false;
        incr i1)
      else (
        if not (push_canonical buf len ~lo:lo2 ~hi:hi2) then pure_t1 := false;
        incr i2)
    done;
    while !i1 < n1 do
      if
        not
          (push_canonical
             buf
             len
             ~lo:(Array.unsafe_get a1 (!i1 * 2))
             ~hi:(Array.unsafe_get a1 ((!i1 * 2) + 1)))
      then pure_t2 := false;
      incr i1
    done;
    while !i2 < n2 do
      if
        not
          (push_canonical
             buf
             len
             ~lo:(Array.unsafe_get a2 (!i2 * 2))
             ~hi:(Array.unsafe_get a2 ((!i2 * 2) + 1)))
      then pure_t1 := false;
      incr i2
    done;
    if !pure_t1 then t1 else if !pure_t2 then t2 else { ivals = trim buf !len })
;;

let add t cp =
  validate_codepoint cp;
  if mem t cp then t else union t { ivals = [| cp; cp |] }
;;

(* Emit the overlap of the aligned pair, then advance whichever interval ends
   first (both when they end together). Every emitted interval sits inside a
   [t1] interval, so the invariants hold without merging. *)
let inter t1 t2 =
  if is_empty t1 || is_empty t2
  then empty
  else if t1 == t2
  then t1
  else (
    let a1 = t1.ivals
    and a2 = t2.ivals in
    let n1 = Array.length a1 / 2 in
    let n2 = Array.length a2 / 2 in
    let buf = Array.make ((n1 + n2) * 2) 0 in
    let len = ref 0 in
    let i1 = ref 0
    and i2 = ref 0 in
    let pure_t1 = ref true
    and pure_t2 = ref true in
    (* Unsafe accesses: [!i1 < n1] and [!i2 < n2] bound every index;
       [buf] writes are bounded by the n1 + n2 - 1 possible overlaps. *)
    while !i1 < n1 && !i2 < n2 do
      let lo1 = Array.unsafe_get a1 (!i1 * 2)
      and hi1 = Array.unsafe_get a1 ((!i1 * 2) + 1) in
      let lo2 = Array.unsafe_get a2 (!i2 * 2)
      and hi2 = Array.unsafe_get a2 ((!i2 * 2) + 1) in
      let lo = if lo1 > lo2 then lo1 else lo2 in
      let hi = if hi1 < hi2 then hi1 else hi2 in
      if lo <= hi
      then (
        if !pure_t1 && not (lo = lo1 && hi = hi1) then pure_t1 := false;
        if !pure_t2 && not (lo = lo2 && hi = hi2) then pure_t2 := false;
        Array.unsafe_set buf !len lo;
        Array.unsafe_set buf (!len + 1) hi;
        len := !len + 2);
      if hi1 <= hi2 then incr i1;
      if hi2 <= hi1 then incr i2
    done;
    if !len = 0
    then empty
    else if !pure_t1 && !len = Array.length a1
    then t1
    else if !pure_t2 && !len = Array.length a2
    then t2
    else { ivals = trim buf !len })
;;

(* One pass, one allocation. For each [t] interval, carve out the overlapping
   [remove] intervals; a [remove] interval ending before the current one is
   consumed, one running past its end is kept, since it may clip the next.

   Emitted pieces are sub-intervals of [t]'s, in order, separated by a removed
   interval or by a gap, so the output is canonical without merging. Size is
   bounded by n + n_rem; each piece ends at a [t] hi or just before a [remove]
   lo, and each is used once. *)
let diff t ~remove =
  if is_empty t || t == remove
  then empty
  else if is_empty remove
  then t
  else (
    let a = t.ivals
    and rem = remove.ivals in
    let n = Array.length a / 2 in
    let n_rem = Array.length rem / 2 in
    let buf = Array.make ((n + n_rem) * 2) 0 in
    let len = ref 0 in
    let pure_t = ref true in
    let emit ~lo ~hi =
      if
        !pure_t
        && (!len + 2 > Array.length a
            || lo <> Array.unsafe_get a !len
            || hi <> Array.unsafe_get a (!len + 1))
      then pure_t := false;
      Array.unsafe_set buf !len lo;
      Array.unsafe_set buf (!len + 1) hi;
      len := !len + 2
    in
    let i_rem = ref 0 in
    (* Unsafe accesses: [i < n] by the for-loop bound, [!i_rem < n_rem]
       checked before every [remove] read. *)
    for i = 0 to n - 1 do
      let lo = ref (Array.unsafe_get a (i * 2)) in
      let hi = Array.unsafe_get a ((i * 2) + 1) in
      while !i_rem < n_rem && Array.unsafe_get rem ((!i_rem * 2) + 1) < !lo do
        incr i_rem
      done;
      let continue = ref true in
      while !continue && !i_rem < n_rem && Array.unsafe_get rem (!i_rem * 2) <= hi do
        let rem_lo = Array.unsafe_get rem (!i_rem * 2)
        and rem_hi = Array.unsafe_get rem ((!i_rem * 2) + 1) in
        if rem_lo > !lo then emit ~lo:!lo ~hi:(rem_lo - 1);
        if rem_hi >= hi
        then (
          lo := hi + 1;
          continue := false)
        else (
          lo := rem_hi + 1;
          incr i_rem)
      done;
      if !lo <= hi then emit ~lo:!lo ~hi
    done;
    if !len = 0
    then empty
    else if !pure_t && !len = Array.length a
    then t
    else { ivals = trim buf !len })
;;

let comp t = diff all ~remove:t

(* Composed from the two differences; three allocations, still O(n + m). *)
let xor t1 t2 =
  if t1 == t2
  then empty
  else if is_empty t1
  then t2
  else if is_empty t2
  then t1
  else union (diff t1 ~remove:t2) (diff t2 ~remove:t1)
;;

let remove t cp =
  validate_codepoint cp;
  if mem t cp then diff t ~remove:{ ivals = [| cp; cp |] } else t
;;

let add_range t ~lo ~hi = union t (range ~lo ~hi)
let remove_range t ~lo ~hi = diff t ~remove:(range ~lo ~hi)

(* -- Relations ------------------------------------------------------------- *)

(* [t] is a subset of [of_] iff every [t] interval is contained in some [of_]
   interval; since both are canonical, a single forward walk suffices. *)
let subset t ~of_ =
  t == of_
  ||
  let a = t.ivals
  and sup = of_.ivals in
  let n = Array.length a / 2
  and n_sup = Array.length sup / 2 in
  let rec loop i i_sup =
    i >= n
    || (i_sup < n_sup
        &&
        let lo = a.(i * 2)
        and hi = a.((i * 2) + 1) in
        let sup_lo = sup.(i_sup * 2)
        and sup_hi = sup.((i_sup * 2) + 1) in
        if sup_hi < lo
        then loop i (i_sup + 1)
        else sup_lo <= lo && hi <= sup_hi && loop (i + 1) i_sup)
  in
  loop 0 0
;;

let scan_before_gallop = 4

let gallop_hi (a : int array) n i x =
  if i >= n
  then n
  else if Array.unsafe_get a ((i * 2) + 1) >= x
  then i (* the single-step case, which finely interleaved runs stay in *)
  else (
    let j = ref (i + 1)
    and steps = ref 1 in
    while
      !j < n && !steps < scan_before_gallop && Array.unsafe_get a ((!j * 2) + 1) < x
    do
      incr j;
      incr steps
    done;
    if !j >= n
    then n
    else if Array.unsafe_get a ((!j * 2) + 1) >= x
    then !j
    else (
      let base = !j in
      let step = ref 1 in
      while base + !step < n && Array.unsafe_get a (((base + !step) * 2) + 1) < x do
        step := !step * 2
      done;
      let lo = ref (base + (!step / 2))
      and hi = ref (min (base + !step) (n - 1)) in
      while !lo < !hi do
        let mid = (!lo + !hi) / 2 in
        if Array.unsafe_get a ((mid * 2) + 1) >= x then hi := mid else lo := mid + 1
      done;
      if Array.unsafe_get a ((!lo * 2) + 1) >= x then !lo else n))
;;

let disjoint t1 t2 =
  if t1 == t2
  then is_empty t1
  else (
    let a1 = t1.ivals
    and a2 = t2.ivals in
    let n1 = Array.length a1 / 2
    and n2 = Array.length a2 / 2 in
    let i1 = ref 0
    and i2 = ref 0
    and meet = ref false in
    while (not !meet) && !i1 < n1 && !i2 < n2 do
      let hi1 = Array.unsafe_get a1 ((!i1 * 2) + 1)
      and lo2 = Array.unsafe_get a2 (!i2 * 2) in
      if hi1 < lo2
      then (
        (* The single-step case is taken here so that interleaved runs never
           reach the call. *)
        let j = !i1 + 1 in
        i1
        := if j < n1 && Array.unsafe_get a1 ((j * 2) + 1) >= lo2
           then j
           else gallop_hi a1 n1 j lo2)
      else (
        let hi2 = Array.unsafe_get a2 ((!i2 * 2) + 1)
        and lo1 = Array.unsafe_get a1 (!i1 * 2) in
        if hi2 < lo1
        then (
          let j = !i2 + 1 in
          i2
          := if j < n2 && Array.unsafe_get a2 ((j * 2) + 1) >= lo1
             then j
             else gallop_hi a2 n2 j lo1)
        else meet := true)
    done;
    not !meet)
;;

(* -- Sorting --------------------------------------------------------------- *)

(* Keys are non-negative ints of known width: 21 bits for a codepoint, 42 for a
   packed pair. [Array.sort] compares through a closure and heapsorts, costing
   30ns an element at a hundred and 110ns at a hundred thousand. [sort_int_keys]
   picks by input: an ascending pass, a merge sort under [radix_min], an LSD
   radix above it. *)

let is_ascending (a : int array) =
  let n = Array.length a in
  let i = ref 1 in
  while !i < n && Array.unsafe_get a (!i - 1) <= Array.unsafe_get a !i do
    incr i
  done;
  !i >= n
;;

(* Bottom-up, over a scratch buffer; the comparison inlines. *)
let merge_sort_int (a : int array) =
  let n = Array.length a in
  let buf = Array.make n 0 in
  let src = ref a
  and dst = ref buf
  and width = ref 1 in
  while !width < n do
    let s = !src
    and d = !dst in
    let i = ref 0 in
    while !i < n do
      let lo = !i in
      let mid = min n (lo + !width) in
      let hi = min n (lo + (2 * !width)) in
      let p = ref lo
      and q = ref mid
      and k = ref lo in
      while !p < mid && !q < hi do
        let x = Array.unsafe_get s !p
        and y = Array.unsafe_get s !q in
        if x <= y
        then (
          Array.unsafe_set d !k x;
          incr p)
        else (
          Array.unsafe_set d !k y;
          incr q);
        incr k
      done;
      while !p < mid do
        Array.unsafe_set d !k (Array.unsafe_get s !p);
        incr p;
        incr k
      done;
      while !q < hi do
        Array.unsafe_set d !k (Array.unsafe_get s !q);
        incr q;
        incr k
      done;
      i := hi
    done;
    let t = !src in
    src := !dst;
    dst := t;
    width := !width * 2
  done;
  if !src != a then Array.blit !src 0 a 0 n
;;

let radix_bits = 11
let radix_base = 1 lsl radix_bits

(* [bits] is the key width. 21 and 42 both give an even pass count, so the
   result lands back in [a]. *)
let radix_sort_int (a : int array) ~bits =
  let n = Array.length a in
  let passes = (bits + radix_bits - 1) / radix_bits in
  let buf = Array.make n 0 in
  let counts = Array.make radix_base 0 in
  let src = ref a
  and dst = ref buf in
  for pass = 0 to passes - 1 do
    let shift = pass * radix_bits in
    Array.fill counts 0 radix_base 0;
    let s = !src
    and d = !dst in
    for i = 0 to n - 1 do
      let digit = (Array.unsafe_get s i lsr shift) land (radix_base - 1) in
      Array.unsafe_set counts digit (Array.unsafe_get counts digit + 1)
    done;
    let acc = ref 0 in
    for digit = 0 to radix_base - 1 do
      let c = Array.unsafe_get counts digit in
      Array.unsafe_set counts digit !acc;
      acc := !acc + c
    done;
    for i = 0 to n - 1 do
      let v = Array.unsafe_get s i in
      let digit = (v lsr shift) land (radix_base - 1) in
      let at = Array.unsafe_get counts digit in
      Array.unsafe_set d at v;
      Array.unsafe_set counts digit (at + 1)
    done;
    let t = !src in
    src := !dst;
    dst := t
  done;
  if !src != a then Array.blit !src 0 a 0 n
;;

(* Measured crossover. Below it the [passes * 2048] counter slots cost more
   than the linear scan saves. *)
let radix_min = 512

let sort_int_keys (a : int array) ~bits =
  if not (is_ascending a)
  then if Array.length a < radix_min then merge_sort_int a else radix_sort_int a ~bits
;;

(* -- List and sequence constructors ---------------------------------------- *)

(* Sort in place, then canonicalize in one pass. Takes ownership of [arr];
   codepoints must already be validated. *)
let of_unsorted_array (arr : int array) =
  if Array.length arr = 0
  then empty
  else (
    sort_int_keys arr ~bits:21;
    let buf = Array.make (Array.length arr * 2) 0 in
    let len = ref 0 in
    Array.iter (fun cp -> ignore (push_canonical buf len ~lo:cp ~hi:cp : bool)) arr;
    { ivals = trim buf !len })
;;

let of_list xs =
  List.iter validate_codepoint xs;
  of_unsorted_array (Array.of_list xs)
;;

(* Chars are always valid codepoints, so validation is skipped. *)
let of_char_list xs =
  match xs with
  | [] -> empty
  | first :: _ ->
    let arr = Array.make (List.length xs) (Char.code first) in
    List.iteri (fun i c -> Array.unsafe_set arr i (Char.code c)) xs;
    of_unsorted_array arr
;;

let of_uchar_list xs =
  match xs with
  | [] -> empty
  | first :: _ ->
    let arr = Array.make (List.length xs) (Uchar.to_int first) in
    List.iteri (fun i u -> Array.unsafe_set arr i (Uchar.to_int u)) xs;
    of_unsorted_array arr
;;

let of_seq s =
  let arr = Array.of_seq s in
  Array.iter validate_codepoint arr;
  of_unsorted_array arr
;;

(* -- Bulk construction ----------------------------------------------------- *)

(* Mutable bulk construction: append raw pairs to a growable buffer in
   amortized O(1), and defer canonicalization to [build], so k intervals cost
   O(k log k) in total.

   Sorting by [lo] alone suffices; once a gap starts a new output pair every
   later input has a lower bound at least as large and cannot reach back across
   it, and [push_canonical] keeps the running max of merged upper bounds. *)
module Builder = struct
  type set = t

  type t =
    { mutable pairs : int array (* flat lo,hi pairs; first [len] cells used *)
    ; mutable len : int
    }

  let create ?(size_hint = 16) () =
    { pairs = Array.make (2 * max 1 size_hint) 0; len = 0 }
  ;;

  let ensure b extra =
    let needed = b.len + extra in
    if needed > Array.length b.pairs
    then (
      let cap = ref (max 4 (Array.length b.pairs)) in
      while !cap < needed do
        cap := !cap * 2
      done;
      let bigger = Array.make !cap 0 in
      Array.blit b.pairs 0 bigger 0 b.len;
      b.pairs <- bigger)
  ;;

  let unchecked_pair b lo hi =
    ensure b 2;
    b.pairs.(b.len) <- lo;
    b.pairs.(b.len + 1) <- hi;
    b.len <- b.len + 2
  ;;

  let add b cp =
    validate_codepoint cp;
    unchecked_pair b cp cp
  ;;

  let add_uchar b u =
    let cp = Uchar.to_int u in
    unchecked_pair b cp cp
  ;;

  let length b = b.len / 2

  (* Keeps the buffer, so a reused builder pays its growth cost once. *)
  let reset b = b.len <- 0

  (* Same validation and surrogate-straddle split as [range]. *)
  let add_interval b ~lo ~hi =
    validate_codepoint lo;
    validate_codepoint hi;
    if lo <= hi
    then
      if hi < surrogate_lo || lo > surrogate_hi
      then unchecked_pair b lo hi
      else (
        unchecked_pair b lo (surrogate_lo - 1);
        unchecked_pair b (surrogate_hi + 1) hi)
  ;;

  (* A set's pairs are already valid and canonical among themselves, so they can
     be blitted in wholesale. *)
  let add_set b (s : set) =
    let n = Array.length s.ivals in
    ensure b n;
    Array.blit s.ivals 0 b.pairs b.len n;
    b.len <- b.len + n
  ;;

  let build b =
    let n_pairs = b.len / 2 in
    if n_pairs = 0
    then empty
    else (
      (* Sort a copy, so [build] stays non-destructive. Each pair packs into
         one int (endpoints fit in 21 bits), keeping the sort on a flat int
         array; the packed order is [lo] then [hi], which is what
         [push_canonical] needs. *)
      let key = Array.make n_pairs 0 in
      for i = 0 to n_pairs - 1 do
        Array.unsafe_set
          key
          i
          ((Array.unsafe_get b.pairs (i * 2) lsl 21)
           lor Array.unsafe_get b.pairs ((i * 2) + 1))
      done;
      sort_int_keys key ~bits:42;
      let buf = Array.make b.len 0 in
      let out = ref 0 in
      Array.iter
        (fun k ->
           ignore (push_canonical buf out ~lo:(k lsr 21) ~hi:(k land 0x1FFFFF) : bool))
        key;
      { ivals = trim buf !out })
  ;;
end

(* -- n-ary operations ------------------------------------------------------ *)

(* Accumulate into one builder and canonicalize once: O(total log total), with
   a single output allocation. *)
let union_list ts =
  match ts with
  | [] -> empty
  | [ t ] -> t
  | _ ->
    let b =
      Builder.create
        ~size_hint:(List.fold_left (fun acc t -> acc + num_intervals t) 0 ts)
        ()
    in
    List.iter (Builder.add_set b) ts;
    Builder.build b
;;

(* One n-way sweep, so no intermediate set is built. A cursor per input; each
   step takes the overlap of all current intervals and advances every cursor
   that ends soonest, which guarantees progress. Any input running out ends the
   walk, since the result can only shrink. *)
let inter_list ts =
  match ts with
  | [] -> all
  | [ t ] -> t
  | [ t1; t2 ] -> inter t1 t2
  | _ ->
    let ts = Array.of_list ts in
    let k = Array.length ts in
    if Array.exists is_empty ts
    then empty
    else (
      let cap = Array.fold_left (fun acc t -> acc + Array.length t.ivals) 0 ts in
      let buf = Array.make cap 0 in
      let len = ref 0 in
      let cur = Array.make k 0 in
      let running = ref true in
      while !running do
        let live = ref true in
        for x = 0 to k - 1 do
          if cur.(x) * 2 >= Array.length ts.(x).ivals then live := false
        done;
        if not !live
        then running := false
        else (
          let lo = ref 0
          and hi = ref max_codepoint in
          for x = 0 to k - 1 do
            let a = ts.(x).ivals in
            let c = cur.(x) in
            if a.(c * 2) > !lo then lo := a.(c * 2);
            if a.((c * 2) + 1) < !hi then hi := a.((c * 2) + 1)
          done;
          if !lo <= !hi
          then (
            Array.unsafe_set buf !len !lo;
            Array.unsafe_set buf (!len + 1) !hi;
            len := !len + 2);
          let hmin = !hi in
          for x = 0 to k - 1 do
            if ts.(x).ivals.((cur.(x) * 2) + 1) = hmin then cur.(x) <- cur.(x) + 1
          done)
      done;
      if !len = 0 then empty else { ivals = trim buf !len })
;;

(* -- Transformations ------------------------------------------------------- *)

let filter f t =
  let b = Builder.create ~size_hint:(num_intervals t) () in
  iter_intervals
    (fun lo hi ->
       let run_lo = ref (-1) in
       for cp = lo to hi do
         if f cp
         then if !run_lo < 0 then run_lo := cp else ()
         else if !run_lo >= 0
         then (
           Builder.unchecked_pair b !run_lo (cp - 1);
           run_lo := -1)
       done;
       if !run_lo >= 0 then Builder.unchecked_pair b !run_lo hi)
    t;
  Builder.build b
;;

let map f t =
  let b = Builder.create ~size_hint:(num_intervals t) () in
  iter
    (fun cp ->
       let cp' = f cp in
       validate_codepoint cp';
       Builder.unchecked_pair b cp' cp')
    t;
  Builder.build b
;;

(* -- Builder-backed constructors ------------------------------------------- *)

(* Malformed bytes decode to U+FFFD, following [String.get_utf_8_uchar]. *)
let of_utf_8_string s =
  let b = Builder.create () in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    let d = String.get_utf_8_uchar s !i in
    Builder.add_uchar b (Uchar.utf_decode_uchar d);
    i := !i + Uchar.utf_decode_length d
  done;
  Builder.build b
;;

(* Pairs may be unsorted, overlapping, adjacent or reversed ([lo > hi] is
   ignored); the Builder normalizes them. The entry point for generated tables,
   such as Unicode property data emitted as literals. *)
let of_intervals pairs =
  let b = Builder.create ~size_hint:(List.length pairs) () in
  List.iter (fun (lo, hi) -> Builder.add_interval b ~lo ~hi) pairs;
  Builder.build b
;;

(* -- Partition refinement -------------------------------------------------- *)

(* Partitions and their common refinement.

   Blocks within a partition are disjoint, so every codepoint carries at most
   one block index per side and the refinement is a merge: walk both sides'
   intervals in order, attributing each overlap to the block named by the pair
   of indices it fell under. O(P + Q) in the total interval counts.

   A partition is held as its intervals tagged with an owning block index,
   sorted by lower bound and pairwise disjoint. Refinement consumes and
   produces that form, so a chain of meets never materialises an intermediate
   block, and a representative codepoint per block falls out of the sweep.
   Callers needing only representatives (a character to derive on, say) can
   skip building the blocks. *)
module Partition = struct
  type set = t

  type t =
    { lo : int array (* segment lower bounds, strictly ascending *)
    ; hi : int array (* segment upper bounds *)
    ; lab : int array (* owning block index, below [nblocks] *)
    ; rep : int array (* least element of each block *)
    ; nblocks : int
    }

  let empty = { lo = [||]; hi = [||]; lab = [||]; rep = [||]; nblocks = 0 }

  let universe =
    { lo = [| 0; surrogate_hi + 1 |]
    ; hi = [| surrogate_lo - 1; max_codepoint |]
    ; lab = [| 0; 0 |]
    ; rep = [| 0 |]
    ; nblocks = 1
    }
  ;;

  let num_blocks p = p.nblocks

  let representative p i =
    if i < 0 || i >= p.nblocks
    then fail ~fn:"Partition.representative" "index out of range";
    p.rep.(i)
  ;;

  let representatives p = Array.to_list p.rep

  (* Segments are disjoint and ascending in [lo], so the segment holding
     [cp] is one binary search; its [lab] is the block. Note that the
     blocks themselves are not intervals -- they interleave -- so this
     cannot be answered by searching [rep]. *)
  let block_of p cp =
    let lo = p.lo
    and hi = p.hi in
    let rec go a b =
      if a >= b
      then -1
      else (
        let mid = (a + b) / 2 in
        if cp < Array.unsafe_get lo mid
        then go a mid
        else if cp > Array.unsafe_get hi mid
        then go (mid + 1) b
        else Array.unsafe_get p.lab mid)
    in
    go 0 (Array.length lo)
  ;;

  (* Empty blocks are dropped, so [nblocks] counts inhabited blocks and every
     [rep] entry is real. *)
  let of_blocks (bs : set list) =
    let bs = List.filter (fun b -> Array.length b.ivals > 0) bs in
    let nseg = List.fold_left (fun acc b -> acc + (Array.length b.ivals / 2)) 0 bs in
    if nseg = 0
    then empty
    else (
      let lo = Array.make nseg 0
      and hi = Array.make nseg 0
      and lab = Array.make nseg 0 in
      let k = ref 0 in
      List.iteri
        (fun label b ->
           let a = b.ivals in
           for i = 0 to (Array.length a / 2) - 1 do
             lo.(!k) <- a.(i * 2);
             hi.(!k) <- a.((i * 2) + 1);
             lab.(!k) <- label;
             incr k
           done)
        bs;
      let order = Array.init nseg (fun i -> i) in
      Array.sort (fun i j -> Stdlib.compare (lo.(i) : int) lo.(j)) order;
      let slo = Array.make nseg 0
      and shi = Array.make nseg 0
      and slab = Array.make nseg 0 in
      Array.iteri
        (fun k' i ->
           slo.(k') <- lo.(i);
           shi.(k') <- hi.(i);
           slab.(k') <- lab.(i))
        order;
      for i = 1 to nseg - 1 do
        if slo.(i) <= shi.(i - 1)
        then fail ~fn:"Partition.of_blocks" "blocks are not disjoint"
      done;
      let nblocks = List.length bs in
      let remap = Array.make nblocks (-1) in
      let rep = Array.make nblocks 0 in
      let next = ref 0 in
      for i = 0 to nseg - 1 do
        let l = slab.(i) in
        if remap.(l) < 0
        then (
          remap.(l) <- !next;
          rep.(!next) <- slo.(i);
          incr next);
        slab.(i) <- remap.(l)
      done;
      { lo = slo; hi = shi; lab = slab; rep; nblocks })
  ;;

  let of_set (s : set) = of_blocks [ s; comp s ]

  (* Two-pointer sweep. Block indices are handed out in first-appearance
     order; overlaps are emitted in increasing order, so index order agrees
     with least-element order and [rep] is correct by construction. *)
  let meet p q =
    let np = Array.length p.lo
    and nq = Array.length q.lo in
    let cap = np + nq in
    let olo = Array.make cap 0
    and ohi = Array.make cap 0
    and olab = Array.make cap 0
    and orep = Array.make cap 0 in
    let out = ref 0
    and nb = ref 0 in
    (* Pair (block of [p], block of [q]) -> new block id. There are at
       most [cap] distinct pairs, one per emitted segment, and the key
       is already an int -- so an open-addressed table over two
       preallocated arrays does the job without the bucket array,
       boxed keys, [Some] allocation and polymorphic hash that
       [Hashtbl] costs on every [meet]. [-1] marks a free slot;
       [mask] keeps the load factor at or below 1/2. *)
    let tsize =
      let rec pow2 k = if k >= cap * 2 then k else pow2 (k * 2) in
      pow2 8
    in
    let mask = tsize - 1 in
    let tkey = Array.make tsize (-1)
    and tval = Array.make tsize 0 in
    let i = ref 0
    and j = ref 0 in
    while !i < np && !j < nq do
      let alo = p.lo.(!i)
      and ahi = p.hi.(!i) in
      let blo = q.lo.(!j)
      and bhi = q.hi.(!j) in
      let l = if alo > blo then alo else blo in
      let h = if ahi < bhi then ahi else bhi in
      if l <= h
      then (
        let key = (p.lab.(!i) * q.nblocks) + q.lab.(!j) in
        let id =
          (* Knuth multiplicative, then linear probe. The table can
             never fill: at most [cap] insertions into [2 * cap]
             slots. *)
          let slot = ref (key * 0x27d4_eb2d land max_int land mask) in
          while Array.unsafe_get tkey !slot >= 0 && Array.unsafe_get tkey !slot <> key do
            slot := (!slot + 1) land mask
          done;
          if Array.unsafe_get tkey !slot = key
          then Array.unsafe_get tval !slot
          else (
            let id = !nb in
            incr nb;
            Array.unsafe_set tkey !slot key;
            Array.unsafe_set tval !slot id;
            orep.(id) <- l;
            id)
        in
        olo.(!out) <- l;
        ohi.(!out) <- h;
        olab.(!out) <- id;
        incr out);
      if ahi <= bhi then incr i;
      if bhi <= ahi then incr j
    done;
    { lo = trim olo !out
    ; hi = trim ohi !out
    ; lab = trim olab !out
    ; rep = trim orep !nb
    ; nblocks = !nb
    }
  ;;

  let meet_all ps =
    let rec halve = function
      | [] -> universe
      | [ p ] -> p
      | ps ->
        (* Each pass reverses; [meet] is commutative up to block
           numbering, and its numbering is canonical, so this is safe. *)
        let rec pass acc = function
          | a :: b :: rest -> pass (meet a b :: acc) rest
          | [ a ] -> a :: acc
          | [] -> acc
        in
        halve (pass [] ps)
    in
    halve ps
  ;;

  (* Extracting a block is a copy; its segments arrive in order and already
     non-adjacent. Two segments of one block are always separated by a gap in
     one of the two blocks that produced them, because when the sweep closed
     the first it had reached the end of a segment on some side, and that
     side's next segment with the same label starts at least two codepoints
     later (its own set being canonical). Only a count is needed, to size each
     array exactly. *)
  let blocks p =
    if p.nblocks = 0
    then []
    else (
      let nseg = Array.length p.lo in
      let counts = Array.make p.nblocks 0 in
      for i = 0 to nseg - 1 do
        let l = p.lab.(i) in
        counts.(l) <- counts.(l) + 1
      done;
      let out = Array.map (fun c -> Array.make (c * 2) 0) counts in
      let fill = Array.make p.nblocks 0 in
      for i = 0 to nseg - 1 do
        let l = p.lab.(i) in
        let a = out.(l) in
        let k = fill.(l) in
        Array.unsafe_set a k p.lo.(i);
        Array.unsafe_set a (k + 1) p.hi.(i);
        fill.(l) <- k + 2
      done;
      Array.to_list (Array.map (fun a -> { ivals = a }) out))
  ;;

  let block p i =
    if i < 0 || i >= p.nblocks then fail ~fn:"Partition.block" "index out of range";
    let nseg = Array.length p.lo in
    let c = ref 0 in
    for k = 0 to nseg - 1 do
      if p.lab.(k) = i then incr c
    done;
    let a = Array.make (!c * 2) 0 in
    let j = ref 0 in
    for k = 0 to nseg - 1 do
      if p.lab.(k) = i
      then (
        Array.unsafe_set a !j p.lo.(k);
        Array.unsafe_set a (!j + 1) p.hi.(k);
        j := !j + 2)
    done;
    { ivals = a }
  ;;
end

let refine p q =
  Partition.blocks (Partition.meet (Partition.of_blocks p) (Partition.of_blocks q))
;;

let refine_all ps =
  Partition.blocks (Partition.meet_all (List.map Partition.of_blocks ps))
;;

(* -- Compiled lookup ------------------------------------------------------- *)

(* Compiled constant-time membership: a two-level bitmap trie.

   The codespace splits into 4352 pages of 256 codepoints, each page's
   membership a 32-byte bitmap. Real sets are clumpy, most pages being
   all-zero, all-one or repeats, so pages map through an id in [index] into a
   pool of distinct leaves. Two things keep that index proportional to the set
   rather than to the codespace: pages above the largest member are not stored,
   and the id is a single byte until the set needs more than 256 distinct
   leaves. A set confined to Latin-1 costs one page of index and two leaves.

   [mem] is two dependent loads and a mask, with no data-dependent branches. *)
module Lookup = struct
  type t =
    { index : string (* leaf id per page: one byte, or two big-endian if [wide] *)
    ; leaves : string (* 32 bytes per distinct leaf, at id * 32 *)
    ; pages : int (* pages covered; anything at or above this is absent *)
    ; wide : bool (* index entries are two bytes: over 256 distinct leaves *)
    }

  (* Unsafe accesses: [page < pages] bounds the index read, and every leaf id
     was written from an offset inside [leaves]. That test doubles as the range
     check on [cp]; [pages] never exceeds 4352, and [lsr] is logical, so a
     negative [cp] yields an enormous [page]. Surrogates hit an all-zero
     leaf. *)
  let mem lk cp =
    let page = cp lsr 8 in
    page < lk.pages
    &&
    let id =
      if lk.wide
      then
        (Char.code (String.unsafe_get lk.index (page * 2)) lsl 8)
        lor Char.code (String.unsafe_get lk.index ((page * 2) + 1))
      else Char.code (String.unsafe_get lk.index page)
    in
    let byte =
      Char.code (String.unsafe_get lk.leaves ((id * 32) + ((cp lsr 3) land 31)))
    in
    byte land (1 lsl (cp land 7)) <> 0
  ;;

  let mem_char lk c = mem lk (Char.code c)
  let memory_bytes lk = String.length lk.index + String.length lk.leaves
end

let to_lookup t =
  match max_elt_opt t with
  | None -> Lookup.{ index = ""; leaves = ""; pages = 0; wide = false }
  | Some max_elt ->
    (* Only pages up to the last member are represented; [Lookup.mem] reads
         anything above [pages] as absent. *)
    let pages = (max_elt lsr 8) + 1 in
    (* Paint the intervals into a temporary bitmap; long runs go through
       [Bytes.fill]. *)
    let bits = Bytes.make (pages * 32) '\000' in
    let set_bits byte_idx first_bit last_bit =
      let m = ref (Char.code (Bytes.get bits byte_idx)) in
      for b = first_bit to last_bit do
        m := !m lor (1 lsl b)
      done;
      Bytes.set bits byte_idx (Char.unsafe_chr !m)
    in
    iter_intervals
      (fun lo hi ->
         let first_byte = lo lsr 3
         and last_byte = hi lsr 3 in
         if first_byte = last_byte
         then set_bits first_byte (lo land 7) (hi land 7)
         else (
           set_bits first_byte (lo land 7) 7;
           if last_byte - first_byte > 1
           then Bytes.fill bits (first_byte + 1) (last_byte - first_byte - 1) '\xff';
           set_bits last_byte 0 (hi land 7)))
      t;
    (* Dedup the 32-byte pages into a leaf pool. *)
    let ids = Hashtbl.create 64 in
    let leaves = Buffer.create 1024 in
    let page_id = Array.make pages 0 in
    for page = 0 to pages - 1 do
      let leaf = Bytes.sub_string bits (page * 32) 32 in
      let id =
        match Hashtbl.find_opt ids leaf with
        | Some id -> id
        | None ->
          let id = Hashtbl.length ids in
          Hashtbl.add ids leaf id;
          Buffer.add_string leaves leaf;
          id
      in
      page_id.(page) <- id
    done;
    (* One byte per page until the set needs more than 256 distinct leaves;
         ids fit 16 bits either way, there being only 4352 pages. *)
    let wide = Hashtbl.length ids > 256 in
    let index = Bytes.create (pages * if wide then 2 else 1) in
    Array.iteri
      (fun page id ->
         if wide
         then (
           Bytes.set index (page * 2) (Char.unsafe_chr (id lsr 8));
           Bytes.set index ((page * 2) + 1) (Char.unsafe_chr (id land 0xFF)))
         else Bytes.set index page (Char.unsafe_chr id))
      page_id;
    Lookup.
      { index = Bytes.unsafe_to_string index
      ; leaves = Buffer.contents leaves
      ; pages
      ; wide
      }
;;

(* 256-entry byte table for the ASCII fast path of a UTF-8 inner loop. Bytes
   0..127 are their own codepoints; 0x80..0xFF are lead and continuation bytes,
   and map to false, so the raw input byte indexes the table with no masking.
   Query: [tbl.[Char.code byte] <> '\000']. *)
let ascii_table (s : t) =
  let tbl = Bytes.make 256 '\000' in
  let a = s.ivals in
  let n = Array.length a / 2 in
  (* Intervals are ascending, so the first one starting above ASCII ends the
     job. *)
  let i = ref 0 in
  while !i < n && Array.unsafe_get a (!i * 2) <= 0x7F do
    let lo = Array.unsafe_get a (!i * 2) in
    let hi = Array.unsafe_get a ((!i * 2) + 1) in
    let hi = if hi > 0x7F then 0x7F else hi in
    for cp = lo to hi do
      Bytes.unsafe_set tbl cp '\001'
    done;
    incr i
  done;
  Bytes.unsafe_to_string tbl
;;

(* -- Packed encoding ------------------------------------------------------- *)

(* Each endpoint of the canonical array as 3 big-endian bytes (endpoints fit
   in 21 bits), so 6 bytes per interval. The format is stable and part of the
   interface; generated blobs are committed to other repositories and must
   survive upgrades. *)
let to_packed_string t =
  let a = t.ivals in
  let n = Array.length a in
  let buf = Bytes.create (n * 3) in
  for i = 0 to n - 1 do
    let v = Array.unsafe_get a i in
    Bytes.unsafe_set buf (i * 3) (Char.unsafe_chr (v lsr 16));
    Bytes.unsafe_set buf ((i * 3) + 1) (Char.unsafe_chr ((v lsr 8) land 0xFF));
    Bytes.unsafe_set buf ((i * 3) + 2) (Char.unsafe_chr (v land 0xFF))
  done;
  Bytes.unsafe_to_string buf
;;

(* Packed data claims to be canonical already, so corruption is rejected. *)
let of_packed_string_opt s =
  let byte_len = String.length s in
  if byte_len mod 6 <> 0
  then None
  else (
    let n = byte_len / 3 in
    let a = Array.make n 0 in
    for i = 0 to n - 1 do
      a.(i)
      <- (Char.code s.[i * 3] lsl 16)
         lor (Char.code s.[(i * 3) + 1] lsl 8)
         lor Char.code s.[(i * 3) + 2]
    done;
    let ok = ref true in
    for i = 0 to (n / 2) - 1 do
      let lo = a.(i * 2)
      and hi = a.((i * 2) + 1) in
      if
        lo > hi
        || hi > max_codepoint
        || (lo <= surrogate_hi && hi >= surrogate_lo)
        || (i > 0 && a.(((i - 1) * 2) + 1) + 1 >= lo)
      then ok := false
    done;
    if !ok then Some { ivals = a } else None)
;;

let of_packed_string s =
  let byte_len = String.length s in
  if byte_len mod 6 <> 0 then fail ~fn:"of_packed_string" "length not a multiple of 6";
  let n = byte_len / 3 in
  let a = Array.make n 0 in
  for i = 0 to n - 1 do
    a.(i)
    <- (Char.code s.[i * 3] lsl 16)
       lor (Char.code s.[(i * 3) + 1] lsl 8)
       lor Char.code s.[(i * 3) + 2]
  done;
  let ok = ref true in
  for i = 0 to (n / 2) - 1 do
    let lo = a.(i * 2)
    and hi = a.((i * 2) + 1) in
    if
      lo > hi
      || hi > max_codepoint
      || (lo <= surrogate_hi && hi >= surrogate_lo)
      || (i > 0 && a.(((i - 1) * 2) + 1) + 1 >= lo)
    then ok := false
  done;
  if not !ok then fail ~fn:"of_packed_string" "malformed data";
  { ivals = a }
;;

(* -- Comparison and hashing ------------------------------------------------ *)

let equal t1 t2 =
  t1 == t2
  ||
  let a1 = t1.ivals
  and a2 = t2.ivals in
  let n = Array.length a1 in
  n = Array.length a2
  &&
  let rec loop i = i >= n || (a1.(i) = a2.(i) && loop (i + 1)) in
  loop 0
;;

(* Endpoints are bounded by [max_codepoint], so the subtraction cannot
   overflow. *)
let compare t1 t2 =
  let a1 = t1.ivals
  and a2 = t2.ivals in
  let n1 = Array.length a1
  and n2 = Array.length a2 in
  let n = if n1 < n2 then n1 else n2 in
  let rec loop i =
    if i >= n
    then n1 - n2
    else (
      let c = a1.(i) - a2.(i) in
      if c <> 0 then c else loop (i + 1))
  in
  loop 0
;;

(* A plain arithmetic mix seeded with the endpoint count so that sets differing 
   only in length — [empty] and [singleton 0], whose endpoints are all zero, do 
   not fold to the same value. *)
let hash t =
  let a = t.ivals in
  let n = Array.length a in
  let h = ref n in
  for i = 0 to n - 1 do
    h := !h * 31 lxor a.(i) land max_int
  done;
  !h
;;

(* -- Printing -------------------------------------------------------------- *)

let unwrapped pp t =
  let b = Buffer.create 64 in
  let ppf = Format.formatter_of_buffer b in
  Format.pp_set_margin ppf max_int;
  pp ppf t;
  Format.pp_print_flush ppf ();
  Buffer.contents b
;;

let pp ppf t =
  Format.fprintf ppf "@[<hov 1>[";
  let first = ref true in
  iter_intervals
    (fun lo hi ->
       if !first then first := false else Format.fprintf ppf ";@ ";
       if lo = hi then Format.fprintf ppf "%d" lo else Format.fprintf ppf "%d-%d" lo hi)
    t;
  Format.fprintf ppf "]@]"
;;

let to_string t = unwrapped pp t

(* [U+XXXX] form; four hex digits minimum, more above the BMP. *)
let pp_hex ppf t =
  Format.fprintf ppf "@[<hov 1>[";
  let first = ref true in
  iter_intervals
    (fun lo hi ->
       if !first then first := false else Format.fprintf ppf ";@ ";
       if lo = hi
       then Format.fprintf ppf "U+%04X" lo
       else Format.fprintf ppf "U+%04X-U+%04X" lo hi)
    t;
  Format.fprintf ppf "]@]"
;;

let to_hex_string t = unwrapped pp_hex t

(* A regex-style character class view: [{a-g j m-t}]. Members are written as
   themselves, UTF-8 encoded; the escapes cover the syntax ([-], space, [{],
   [}], [\]) and the C0 and C1 controls, which would otherwise be invisible.
   Format counts bytes, so multi-byte members are announced with [pp_print_as]
   at one column to keep line breaking sane. *)
let pp_class_elt ppf cp =
  match cp with
  | 0x5C -> Format.pp_print_string ppf "\\\\"
  | 0x2D -> Format.pp_print_string ppf "\\-"
  | 0x7B -> Format.pp_print_string ppf "\\{"
  | 0x7D -> Format.pp_print_string ppf "\\}"
  | 0x20 -> Format.pp_print_string ppf "\\u{20}"
  | 0x00 -> Format.pp_print_string ppf "\\0"
  | 0x09 -> Format.pp_print_string ppf "\\t"
  | 0x0A -> Format.pp_print_string ppf "\\n"
  | 0x0B -> Format.pp_print_string ppf "\\v"
  | 0x0C -> Format.pp_print_string ppf "\\f"
  | 0x0D -> Format.pp_print_string ppf "\\r"
  | cp when cp < 0x20 || cp = 0x7F || (cp >= 0x80 && cp <= 0x9F) ->
    Format.fprintf ppf "\\u{%X}" cp
  | cp when cp <= 0x7E -> Format.pp_print_char ppf (Char.unsafe_chr cp)
  | cp ->
    let b = Buffer.create 4 in
    Buffer.add_utf_8_uchar b (Uchar.of_int cp);
    Format.pp_print_as ppf 1 (Buffer.contents b)
;;

let pp_class ppf t =
  Format.fprintf ppf "@[<hov 1>{";
  let first = ref true in
  iter_intervals
    (fun lo hi ->
       if !first then first := false else Format.fprintf ppf "@ ";
       if lo = hi
       then pp_class_elt ppf lo
       else Format.fprintf ppf "%a-%a" pp_class_elt lo pp_class_elt hi)
    t;
  Format.fprintf ppf "}@]"
;;

let to_class_string t = unwrapped pp_class t
