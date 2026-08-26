(lang dune 3.20)

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
 (synopsis "Character classes for Unicode-aware lexers and regex engines")
 (description
  "A faster, smaller Set.Make(Uchar). Cost follows the run count, not the
cardinal: the Alphabetic property is 147,421 codepoints in 761 runs, held in
12KB against 5.6MB, and the whole codespace is 40 bytes against 42.4MB.
Alongside the usual set algebra there is a builder for accumulating a class
from many fragments, a compiled two-level bitmap trie for membership in an
inner loop, partition refinement for derivative classes during DFA
construction, and a stable packed encoding for embedding generated tables in
source. Surrogates are excluded by construction.")
 (depends
  (ocaml
   (>= 4.14))
  (alcotest :with-test)
  (qcheck-core :with-test)
  (qcheck-alcotest :with-test))
 (tags
  (unicode charset codepoint "interval set" regex lexer dfa)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
