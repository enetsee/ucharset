# ucharset

[![CI](https://github.com/enetsee/ucharset/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/enetsee/ucharset/actions/workflows/ci.yml)
[![Docs](https://github.com/enetsee/ucharset/actions/workflows/docs.yml/badge.svg?branch=main)](https://github.com/enetsee/ucharset/actions/workflows/docs.yml)

Character classes for Unicode-aware lexers and regex engines: a faster,
smaller `Set.Make(Uchar)`.

Elements are scalar values in the sense of `Uchar.t`; the surrogate block is
excluded by construction, and functions taking raw codepoints reject it.

[API documentation](https://enetsee.github.io/ucharset/ucharset/Ucharset/index.html)

## Install

Not released to opam yet.

```sh
opam pin add ucharset https://github.com/enetsee/ucharset.git
```

## Example

```ocaml
let letter = Ucharset.range_char ~lo:'a' ~hi:'z'
let digit = Ucharset.range_char ~lo:'0' ~hi:'9'
let ident = Ucharset.union_list [ letter; digit; Ucharset.singleton_char '_' ]

let () = Format.printf "%a@." Ucharset.pp_class ident
(* {0-9 _ a-z} *)
```

Alongside the usual algebra (`union`, `inter`, `diff`, `comp`, `xor`, `subset`,
`disjoint`) there are four things worth knowing about.

**`Builder`** accumulates a set from many fragments, appending in amortized
O(1) and canonicalizing once, where repeated `union` costs O(size) a step.

**`Lookup`** compiles a set into a two-level bitmap trie, so membership becomes
two loads and a mask, independent of the interval count. Against `mem` it is
roughly 2x faster on a set of a few intervals and ~7x at a thousand, in
anything from tens of bytes to a few KB. `ascii_table` is faster still when the
test stays inside ASCII.

**`Partition`** computes the common refinement of two partitions as a single
merge over the interval endpoints, O(P + Q), where doing it pairwise costs
`|p| * |q|` intersections. It is written for derivative-based DFA construction,
where a regex's derivative classes are exactly such a meet;
`Partition.representatives` gives one codepoint per block without building the
blocks at all.

**Packed encoding** serialises a set to a string, six bytes per interval, for
embedding generated tables such as Unicode property data in source. The format
is stable and part of the interface.

## Development

```sh
dune build
dune runtest
dune build @doc     # _build/default/_doc/_html
```

## License

MIT.
