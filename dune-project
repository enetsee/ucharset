(lang dune 3.22)

(name ucharset)

(generate_opam_files true)

(source
 (github enetsee/ucharset))

(authors "Michael Thomas")

(maintainers "Michael Thomas")

(license MIT)

(documentation https://enetsee.github.io/ucharset/)

(package
 (name ucharset)
 (synopsis "Sets of Unicode scalar values as sorted interval runs")
 (description
  "Immutable sets of Unicode scalar values, stored as sorted runs of inclusive
intervals so that size is proportional to the number of runs rather than the
number of codepoints. Surrogates are excluded by construction. Alongside the
usual set algebra there is a builder for accumulating a set from many
fragments, a compiled two-level bitmap trie for constant-time membership in a
matcher or lexer inner loop, partition refinement for computing derivative
classes during DFA construction, and a stable packed encoding for embedding
generated tables in source.")
 (depends
  (ocaml
   (>= 4.14))
  (alcotest :with-test)
  (qcheck-core :with-test)
  (qcheck-alcotest :with-test))
 (tags
  (unicode charset codepoint "interval set" regex lexer dfa)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
