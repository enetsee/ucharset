(** Character classes for Unicode-aware lexers and regex engines: a faster,
    smaller [Set.Make (Uchar)] *)
type t

(** Largest valid codepoint, [0x10FFFF]. *)
val max_codepoint : int

(** {1 Constructors} *)

(** The empty set. *)
val empty : t

(** The set of all Unicode scalar values: [0 .. 0xD7FF] and
    [0xE000 .. max_codepoint]. *)
val all : t

(** [singleton cp] is the set containing exactly [cp]. *)
val singleton : int -> t

(** [singleton_char c] is [singleton (Char.code c)]. *)
val singleton_char : char -> t

(** [singleton_uchar u] is [singleton (Uchar.to_int u)]. A [Uchar.t] is a scalar
    value by construction, so none of the [_uchar] functions can raise. *)
val singleton_uchar : Uchar.t -> t

(** [range ~lo ~hi] is the set of scalar values from [lo] to [hi] inclusive;
    empty if [lo > hi]. Both bounds are validated (and must not be surrogates)
    even when the result is empty. A range straddling the surrogate block is
    split around it, so [range ~lo:0xD000 ~hi:0xF000] contains
    [0xD000 .. 0xD7FF] and [0xE000 .. 0xF000]. *)
val range : lo:int -> hi:int -> t

(** [range_char ~lo ~hi] is [range ~lo:(Char.code lo) ~hi:(Char.code hi)]. *)
val range_char : lo:char -> hi:char -> t

(** [of_list cps] is the set of the given codepoints. Duplicates are allowed;
    order is irrelevant. O(n log n). *)
val of_list : int list -> t

(** [range_uchar ~lo ~hi] is [range] on the two scalar values. *)
val range_uchar : lo:Uchar.t -> hi:Uchar.t -> t

(** [of_char_list cs] is [of_list (List.map Char.code cs)]. *)
val of_char_list : char list -> t

(** [of_uchar_list us] is [of_list (List.map Uchar.to_int us)]. O(n log n). *)
val of_uchar_list : Uchar.t list -> t

(** [of_seq s] is the set of the codepoints of [s]. Validates like [of_list];
    O(n log n). *)
val of_seq : int Seq.t -> t

(** [of_utf_8_string s] is the set of scalar values occurring in [s]. Malformed
    bytes decode to [U+FFFD] following [String.get_utf_8_uchar], and so
    contribute [U+FFFD] to the result rather than raising. *)
val of_utf_8_string : string -> t

(** [of_intervals pairs] is the union of the inclusive ranges [(lo, hi)] in
    [pairs]. Pairs may be unsorted, overlapping, or adjacent; pairs with
    [lo > hi] are ignored; bounds are validated and split around the surrogate
    block like [range]. O(n log n). Intended for tables of literals such as
    generated Unicode property data. *)
val of_intervals : (int * int) list -> t

(** {1 Bulk construction}

    A [Builder.t] is a mutable accumulator that defers canonicalization:
    additions append to a growable buffer in amortized O(1) (O(interval count)
    for [add_set]), and [build] sorts and canonicalizes once, so [k] accumulated
    intervals cost O(k log k) in total. The typical use is compiling a character
    class from many fragments, where repeated [union] would cost O(size) a step.

    Builders are not thread-safe. *)
module Builder : sig
  (** The immutable sets being built: an alias for the enclosing [t], which the
      [t] below shadows. *)
  type set = t

  (** A mutable accumulator of intervals. *)
  type t

  (** [create ?size_hint ()] is an empty builder. [size_hint] is the number of
      intervals to preallocate for (default 16); the buffer grows as needed
      regardless. *)
  val create : ?size_hint:int -> unit -> t

  (** [add b cp] adds the single scalar value [cp]. Validates like [singleton].
  *)
  val add : t -> int -> unit

  (** [add_uchar b u] adds one scalar value; cannot raise. *)
  val add_uchar : t -> Uchar.t -> unit

  (** Intervals accumulated so far, before canonicalization; this counts what
      was added, not what {!build} would produce. *)
  val length : t -> int

  (** Discard everything accumulated so far. Keeps the buffer, so a reused
      builder pays its growth cost only once. *)
  val reset : t -> unit

  (** [add_interval b ~lo ~hi] adds the inclusive range; no-op if [lo > hi].
      Validates the bounds and splits a range straddling the surrogate block,
      exactly like [range]. *)
  val add_interval : t -> lo:int -> hi:int -> unit

  (** [add_set b s] adds every element of [s]. O(intervals of [s]). *)
  val add_set : t -> set -> unit

  (** Canonicalize everything added so far into a set. Does not consume or reset
      the builder: further additions and later [build]s are permitted. O(k log
      k) in accumulated intervals. *)
  val build : t -> set
end

(** {1 Compiled lookup}

    [Lookup] compiles a set once into a two-level bitmap trie whose membership
    test is two dependent loads and a mask: branch-free, and O(1) in the number
    of intervals. [mem] on the interval form is a binary search, so its cost
    grows with the set while [Lookup.mem]'s does not. The compiled form is
    derived and immutable; the interval set remains what you do algebra on.

    Against [mem] over a uniform stream of scalar values, [Lookup.mem] is
    roughly 2x faster on a set of a few intervals, ~5x at several dozen and ~7x
    at a thousand. Index and leaf pool both scale with the set rather than the
    codespace, so the footprint runs from tens of bytes for a set confined to
    Latin-1, through ~2 KB at several dozen intervals, to ~7 KB for the
    many-hundred-interval sets a Unicode property produces. When the test is
    confined to ASCII, [ascii_table] beats both. *)
module Lookup : sig
  (** A compiled constant-time membership structure, indexed by scalar value.
      Raw UTF-8 bytes are not scalar values: run those through [ascii_table]
      below, and bring the decoded scalar here. *)
  type t

  val mem : t -> int -> bool

  (** [mem_uchar lk u] is [mem lk (Uchar.to_int u)]. *)
  val mem_uchar : t -> Uchar.t -> bool

  (** Footprint of the compiled structure. *)
  val memory_bytes : t -> int
end

val to_lookup : t -> Lookup.t

(** [ascii_table s] is a 256-byte table for the ASCII fast path of a UTF-8 inner
    loop: [tbl.[b] <> '\000'] tests membership of byte [b] directly. Bytes
    [0x80..0xFF] (UTF-8 lead/continuation bytes, not characters) map to [false],
    so the raw input byte indexes the table with no masking; route multi-byte
    sequences through [Lookup.mem_uchar] on the decoded scalar instead. *)
val ascii_table : t -> string

(** {1 Packed encoding}

    A compact serialization for embedding tables in generated code: a string
    constant compiles to a single data blob, whereas a list of interval literals
    compiles to per-pair allocation code. The format is stable and part of this
    interface; each endpoint of the canonical intervals as 3 big-endian bytes, 6
    bytes per interval. *)

(** [of_packed_string s] decodes a string produced by [to_packed_string]. Raises
    [Invalid_argument] if [s] is not well-formed canonical data: wrong length,
    reversed or overlapping intervals, out-of-range or surrogate values. *)
val of_packed_string : string -> t

(** [of_packed_string] returning [None] instead of raising, for decoding data
    from an untrusted source. *)
val of_packed_string_opt : string -> t option

val to_packed_string : t -> string

(** {1 Set operations} *)

val union : t -> t -> t
val inter : t -> t -> t

(** [diff t ~remove] is the set of scalar values in [t] but not in [remove]. *)
val diff : t -> remove:t -> t

(** [comp t] is [diff all ~remove:t]. *)
val comp : t -> t

(** Symmetric difference: the values in exactly one of the two. The one
    operation here that allocates more than a single array. *)
val xor : t -> t -> t

(** [union_list ts] is the union of all of [ts], and [empty] for the empty list.
    Accumulates into one builder and canonicalizes once, O(N log N) in the total
    interval count. *)
val union_list : t list -> t

(** [inter_list ts] is the intersection of all of [ts], and [all] for the empty
    list (the identity for intersection). One k-way sweep, so no intermediate
    set is built. *)
val inter_list : t list -> t

(** [add t cp] is [t] with [cp] added. Returns [t] itself if [cp] is already a
    member; otherwise copies the interval array, so O(n). For repeated
    additions use {!Builder}, which appends in amortized O(1) and canonicalizes
    once. *)
val add : t -> int -> t

(** [remove t cp] is [t] with [cp] removed. Returns [t] itself if [cp] is not a
    member; otherwise O(n), as {!add}. *)
val remove : t -> int -> t

(** [add_range t ~lo ~hi] is [union t (range ~lo ~hi)]. *)
val add_range : t -> lo:int -> hi:int -> t

(** [remove_range t ~lo ~hi] is [diff t ~remove:(range ~lo ~hi)]. *)
val remove_range : t -> lo:int -> hi:int -> t

(** [filter f t] keeps the codepoints of [t] satisfying [f]. O(cardinal); it
    visits every codepoint, so over a million calls on [all]. *)
val filter : (int -> bool) -> t -> t

(** [map f t] is the image of [t] under [f]. O(cardinal), and every result is
    validated, so [f] returning a surrogate or an out-of-range value raises
    [Invalid_argument]. *)
val map : (int -> int) -> t -> t

(** {1 Partition refinement}

    A partition here is a collection of pairwise-disjoint non-empty blocks; it
    need not cover the codespace. The common refinement (or meet) of two
    partitions is the set of non-empty [a inter b] for [a] in one and [b] in the
    other, the coarsest partition that both are unions of.

    Blocks on each side are disjoint, so the meet is a single merge over the
    interval endpoints: O(P + Q) in the total interval counts, where computing
    it pairwise would cost [|p| * |q|] intersections to find at most [P + Q - 1]
    blocks.

    {!Partition} is that merge's working form, intervals tagged with an owning
    block index, so a chain of meets never materialises an intermediate block
    and each block's least element falls out of the sweep. Callers needing only
    one codepoint per block, such as a derivative-based DFA construction picking
    a character to derive on, can take {!Partition.representatives} and never
    build the blocks. {!refine} and {!refine_all} are the convenience forms for
    callers already holding lists of sets. *)

module Partition : sig
  (** The sets being partitioned: an alias for the enclosing [t], which the [t]
      below shadows. *)
  type set = t

  (** A partition. Blocks are numbered [0 .. num_blocks - 1] in increasing order
      of their least element. *)
  type t

  (** The partition with no blocks, covering nothing. What {!of_blocks} yields
      for an empty list, and what {!meet} yields when the two sides share no
      codepoint. *)
  val empty : t

  (** The one-block partition of the whole codespace. Identity for {!meet}. *)
  val universe : t

  (** [of_set s] is the partition [{s, comp s}], dropping either if empty; one
      block when [s] is [empty] or [all], two otherwise. *)
  val of_set : set -> t

  (** [of_blocks bs] is the partition whose blocks are the non-empty elements of
      [bs], numbered in increasing order of least element as for any partition
      rather than by position in [bs]. Raises [Invalid_argument] if two of them
      overlap. O(B log B) in the total interval count, since it has to sort. *)
  val of_blocks : set list -> t

  (** Common refinement. O(P + Q) in the total interval counts. *)
  val meet : t -> t -> t

  (** [meet_all ps] is the common refinement of all of [ps], and [universe] for
      the empty list. *)
  val meet_all : t list -> t

  val num_blocks : t -> int

  (** The blocks, in index order. This is where block sets get built, so prefer
      {!representatives} when a codepoint per block is enough. *)
  val blocks : t -> set list

  (** [block p i] builds just block [i]. Raises [Invalid_argument] if [i] is out
      of range. *)
  val block : t -> int -> set

  (** The least element of each block, in index order (hence increasing).
      O(num_blocks), and builds nothing. *)
  val representatives : t -> int list

  (** [representative p i] is the least element of block [i]. O(1). Raises
      [Invalid_argument] if [i] is out of range. *)
  val representative : t -> int -> int

  (** [block_of p cp] is the index of the block containing [cp], or [-1] if
      [cp] lies in no block of [p] (which for a partition covering the whole
      codespace cannot happen). O(log n) in the segment count.

      This is the inverse of {!representative} and the lookup a
      derivative-based construction wants once it has a partition in hand: it
      answers "which block is this character in" without building any block
      set. Searching {!representatives} does not answer it -- blocks are
      unions of intervals and interleave, so a block's least element says
      nothing about where its later intervals fall. *)
  val block_of : t -> int -> int
end

(** [refine p q] is the common refinement of two partitions given as lists of
    disjoint blocks, as
    [Partition.blocks (Partition.meet (of_blocks p) (of_blocks q))]. Blocks come
    back in increasing order of least element. Raises [Invalid_argument] if
    either list has overlapping blocks. *)
val refine : t list -> t list -> t list

(** [refine_all ps] refines every partition in [ps] together, building the
    block sets once at the end; [[all]] for the empty list. Prefer this to
    folding {!refine}, which rebuilds them at every step. *)
val refine_all : t list list -> t list

(** {1 Queries} *)

val is_empty : t -> bool

(** [is_singleton t] is [true] iff [t] contains exactly one codepoint. O(1). *)
val is_singleton : t -> bool

(** [is_all t] is [true] iff [t] is {!all}. O(1); prefer it to
    [is_empty (comp t)], which allocates a set to answer the same question. *)
val is_all : t -> bool

(** Membership test. O(log n) in the number of intervals. *)
val mem : t -> int -> bool

(** [mem_char t c] is [mem t (Char.code c)]. *)
val mem_char : t -> char -> bool

(** [mem_uchar t u] is [mem t (Uchar.to_int u)]. *)
val mem_uchar : t -> Uchar.t -> bool

(** [next_elt_opt t cp] is the smallest member of [t] strictly greater than
    [cp], if any. [cp] need not be a member, or even a scalar value, so this
    doubles as "seek to the next member beyond here". O(log n). *)
val next_elt_opt : t -> int -> int option

(** [prev_elt_opt t cp] is the largest member of [t] strictly less than [cp], if
    any. O(log n). *)
val prev_elt_opt : t -> int -> int option

(** [exists f t] is [true] iff [f] holds of some codepoint of [t]. Visits
    codepoints, so O(cardinal) in the worst case, though it stops early. *)
val exists : (int -> bool) -> t -> bool

(** [for_all f t] is [true] iff [f] holds of every codepoint of [t]. O(cardinal)
    in the worst case, stopping at the first failure. *)
val for_all : (int -> bool) -> t -> bool

(** Number of codepoints in the set. O(n) in the number of intervals. *)
val cardinal : t -> int

(** Number of maximal contiguous runs in the set. O(1). *)
val num_intervals : t -> int

(** [subset t ~of_] is [true] iff every scalar value of [t] is in [of_]. *)
val subset : t -> of_:t -> bool

(** [disjoint t1 t2] is [true] iff [t1] and [t2] share no scalar value. *)
val disjoint : t -> t -> bool

(** Smallest codepoint in the set, if any. O(1). *)
val min_elt_opt : t -> int option

(** Largest codepoint in the set, if any. O(1). *)
val max_elt_opt : t -> int option

(** An arbitrary element of the set, if any (currently the smallest). O(1). *)
val choose_opt : t -> int option

(** {1 Iteration}

    All traversal is in increasing codepoint order. Note that [iter] and [fold]
    visit every codepoint individually so on interval-dense sets such as [all]
    this is 0x110000 calls. Prefer [iter_intervals] when per-run processing
    suffices. *)

(** [iter f t] applies [f] to each codepoint of [t]. *)
val iter : (int -> unit) -> t -> unit

(** [iter_intervals f t] applies [f lo hi] to each maximal run [lo..hi] of [t].
*)
val iter_intervals : (int -> int -> unit) -> t -> unit

(** [fold f t init] folds [f] over each codepoint of [t]. *)
val fold : (int -> 'a -> 'a) -> t -> 'a -> 'a

(** [fold_intervals f t init] folds [f lo hi] over each maximal run of [t]. *)
val fold_intervals : (int -> int -> 'a -> 'a) -> t -> 'a -> 'a

(** The codepoints of [t] in increasing order. Lazy, so it can be consumed
    partially without paying for the whole set. *)
val to_seq : t -> int Seq.t

(** The maximal runs of [t] as inclusive [(lo, hi)] pairs, in increasing order.
*)
val to_seq_intervals : t -> (int * int) Seq.t

(** The maximal runs of the set as inclusive [(lo, hi)] pairs, in increasing
    order. *)
val to_list : t -> (int * int) list

(** {1 Comparison and hashing}

    Suitable for use with [Map.Make], [Set.Make] and [Hashtbl.Make], which is
    why [equal] and [compare] keep the unlabeled [t -> t -> _] signatures those
    functors require. [equal t1 t2] iff [compare t1 t2 = 0], and equal sets hash
    identically, the internal representation being canonical. *)

val equal : t -> t -> bool

(** A total order on sets. The order is representation-based (lexicographic over
    interval endpoints), rather than any set-theoretic order. *)
val compare : t -> t -> int

val hash : t -> int

(** {1 Printing} *)

(** Prints the runs of the set, e.g. [[97-122; 181; 223-246]]. *)
val pp : Format.formatter -> t -> unit

(** As {!pp}, but into a string on a single line. The printers break at the
    formatter's margin; the string forms have none, so the result never contains
    a newline, however wide the set. *)
val to_string : t -> string

(** As {!pp}, but in [U+XXXX] notation:
    [[U+0061-U+007A; U+00B5; U+00DF-U+00F6]]. *)
val pp_hex : Format.formatter -> t -> unit

(** As {!pp_hex}, on a single line. See {!to_string}. *)
val to_hex_string : t -> string

(** A regex-style character class view, reading a set as characters rather than
    as numbers: [{a-g j m-t}], [{α-ω}], [{é € 😀-😁}].

    Members are written as themselves, UTF-8 encoded. The escapes cover the
    syntax ([-], space, [{] and [}]), the backslash that introduces them, and
    the C0 and C1 controls, written [\0], [\t], [\n], [\v], [\f], [\r] or
    [\u{XX}]. Nothing else is escaped, so unassigned and private-use members
    reach the terminal as whatever it makes of them.

    A view, not regex syntax; an engine would want a single bracketed class
    with no separators, and its own escaping rules. *)
val pp_class : Format.formatter -> t -> unit

(** As {!pp_class}, on a single line. See {!to_string}. *)
val to_class_string : t -> string
