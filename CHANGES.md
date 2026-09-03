## v0.2.0 (unreleased)

### Breaking

- 64-bit only. `Builder.build` packs two 21-bit endpoints into one `int` while sorting, so the
  module now fails at load time on a narrower `int` rather than returning corrupted sets, and the
  package is unavailable on 32-bit architectures.
- `Lookup.mem_char` is gone. It read a byte from `0x80` up as Latin-1, where `ascii_table` reads
  the same byte as UTF-8, so the two disagreed on half the table. Use `Lookup.mem_uchar` on the
  decoded scalar, or `ascii_table` on the raw byte.
- `Partition.block_of` is now `Partition.block_of_opt`, answering `None` where it returned `-1`.
- `Partition.of_blocks` numbers blocks by least element rather than by position in the list, so
  `Partition.of_set s` leads with whichever of `s` and `comp s` holds codepoint `0`.
- `hash` mixes the endpoint count, so sets hash differently from v0.1.0. `empty` and `singleton 0`
  no longer both hash to `0`.
- `to_string`, `to_hex_string` and `to_class_string` return one line whatever the set's width. The
  `pp` family still breaks at the formatter's margin.
- `Invalid_argument` messages name `Ucharset`, not the `Charset` module that never existed.
- `to_list` is now `to_intervals`. It returns runs, not codepoints, so it never paired with
  `of_list`; `of_intervals` is its inverse.
- `pp_class` and `to_class_string` escape the non-ASCII whitespace as well (`U+00A0`, `U+1680`,
  `U+2000` to `U+200A`, `U+2028`, `U+2029`, `U+202F`, `U+205F`, `U+3000`), which used to print as
  themselves and read as the separator between members.

### Added

- `Partition.block_of_opt`: which block holds a codepoint, without building a block.
- `Lookup.mem_uchar`.

### Performance

- `meet_all` refines pairwise by halving instead of sweeping every input at once. Faster as the number of partitions grows, at 8x to 13x the allocation.
- `Partition.meet` sizes its scratch tables by block count, not segment count.
- `subset` gallops like `disjoint` rather than walking `of_` linearly.
- `mem`, `subset`, `equal`, `compare` and `Partition.block_of_opt` allocate nothing per call.
- `min` is monomorphic again in the sort and gallop paths.
- `xor` is one merge over the endpoints rather than `union (diff a b) (diff b a)`, so one array
  where there were three.
- `union_list` of exactly two sets calls `union` directly, as `inter_list` already did.
- `map` sizes its accumulator from `cardinal`, the exact number of pairs it will emit.
- `inter_list` finds the overlap and the exhausted inputs in one pass rather than two.

### Documentation

- The module preamble carries the validation contract again: functions building or updating a set from a raw `int` raise on a surrogate or an out-of-range value, queries answer for any `int`.
- `of_packed_string` documents acceptance as exactly what `to_packed_string` emits, adjacent intervals included. The encoding itself is unchanged since v0.1.0.
- The `Lookup` footprint and "branch-free" claims are corrected: only the leaf pool scales with the set, and the index scales with the largest member.
- Doc comments for the values that had none.
- `xor` no longer claims to be the only operation allocating more than one array, which was false
  for `refine`, `of_blocks`, `to_lookup` and `meet_all`.
- `meet_all` states its cost again: O(S log k) against folding `meet` at O(S k).
- `filter` documents that it cannot size its accumulator in advance, and `Partition.block` that
  building every block one at a time is what `blocks` is for.

## v0.1.0

- Initial release.
