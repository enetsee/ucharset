(* Tests for Ucharset.

   Property tests state a law and let QCheck shrink any counterexample; unit
   tests pin down the boundaries random generation rarely hits, being the
   surrogate block, U+FFFF, U+10FFFF, empty and full.

   Properties use one of two models. On sets confined to a narrow span the model
   is exact: a set is the sorted list of its codepoints, and operations are
   modelled with list operations. Over the whole codespace that is far too slow,
   so agreement is checked at every interval endpoint and one either side. That
   is sufficient, not approximate; both the result and the model are unions of
   intervals whose endpoints come from the inputs, so they are constant between
   consecutive probes. *)

(* -- Alcotest plumbing ----------------------------------------------------- *)

let cset = Alcotest.testable Ucharset.pp Ucharset.equal
let ivals = Alcotest.(list (pair int int))
let is_true name b = Alcotest.(check bool) name true b
let is_false name b = Alcotest.(check bool) name false b

(* Every [Invalid_argument] the library raises names the library, so a rename
   that misses a message is caught here and not by a user grepping their
   dependency tree for a module that does not exist. Checked on every raise
   site the suite already exercises. *)
let names_library msg =
  String.starts_with ~prefix:"Ucharset." msg
  || String.starts_with ~prefix:"Ucharset: " msg
;;

let raises_invalid name f =
  match f () with
  | _ -> Alcotest.fail (name ^ ": expected Invalid_argument")
  | exception Invalid_argument msg ->
    Alcotest.(check bool)
      (name ^ ": message names the library, got " ^ msg)
      true
      (names_library msg)
;;

let case name f = Alcotest.test_case name `Quick f

(* -- Shared helpers -------------------------------------------------------- *)

let is_scalar cp =
  cp >= 0 && cp <= Ucharset.max_codepoint && not (cp >= 0xD800 && cp <= 0xDFFF)
;;

let elems t =
  List.concat_map
    (fun (lo, hi) -> List.init (hi - lo + 1) (fun i -> lo + i))
    (Ucharset.to_list t)
;;

(* Sorted, non-empty, non-adjacent, surrogate-free: the invariant that makes
   structural [equal], [compare] and [hash] exact. *)
let is_canonical t =
  let rec go prev = function
    | [] -> true
    | (lo, hi) :: rest ->
      lo <= hi
      && is_scalar lo
      && is_scalar hi
      && (not (lo <= 0xDFFF && hi >= 0xD800))
      && (match prev with
          | None -> true
          | Some p -> lo > p + 1)
      && go (Some hi) rest
  in
  go None (Ucharset.to_list t)
;;

(* Every point at which membership can change, for either input. *)
let probes ts =
  List.sort_uniq
    Stdlib.compare
    (List.filter
       is_scalar
       (0
        :: Ucharset.max_codepoint
        :: 0xD7FF
        :: 0xE000
        :: List.concat_map
             (fun t ->
                List.concat_map
                  (fun (lo, hi) -> [ lo - 1; lo; hi; hi + 1 ])
                  (Ucharset.to_list t))
             ts))
;;

let agrees_on ts got want =
  List.for_all (fun cp -> Ucharset.mem got cp = want cp) (probes ts)
;;

(* -- Generators ------------------------------------------------------------ *)

(* Skip the surrogate block so generated codepoints are always scalar values;
   the reverse mapping keeps shrinking working. *)
let scalar_of_rank i = if i < 0xD800 then i else i + 0x800
let rank_of_scalar cp = if cp < 0xD800 then cp else cp - 0x800
let max_rank = Ucharset.max_codepoint - 0x800
let arb_scalar = QCheck.(map ~rev:rank_of_scalar scalar_of_rank (int_range 0 max_rank))
let print_set t = Format.asprintf "%a" Ucharset.pp t

let set_of_pairs ~span n_max =
  QCheck.(
    set_print
      print_set
      (map
         ~rev:Ucharset.to_list
         Ucharset.of_intervals
         (list_size (Gen.int_range 0 n_max) (pair (int_range 0 span) (int_range 0 span)))))
;;

(* Narrow enough that the exact list model is affordable. *)
let arb_small = set_of_pairs ~span:0x180 6

(* Spread over the whole codespace, so the surrogate hole is in play. *)
let arb_wide =
  QCheck.(
    set_print
      print_set
      (map
         ~rev:Ucharset.to_list
         Ucharset.of_intervals
         (list_size (Gen.int_range 0 12) (pair arb_scalar arb_scalar))))
;;

let prop ?(count = 300) name arb f = QCheck.Test.make ~count ~name arb f
let prop2 ?(count = 300) name a b f = QCheck.Test.make ~count ~name (QCheck.pair a b) f

let prop3 ?(count = 200) name a b c f =
  QCheck.Test.make ~count ~name (QCheck.triple a b c) f
;;

let qc ts = List.map QCheck_alcotest.to_alcotest ts

(* -- Constructors ---------------------------------------------------------- *)

let constructors =
  [ case "empty and all" (fun () ->
      is_true "empty" (Ucharset.is_empty Ucharset.empty);
      is_false "all" (Ucharset.is_empty Ucharset.all);
      Alcotest.(check int)
        "all cardinal"
        (0x110000 - 2048)
        (Ucharset.cardinal Ucharset.all);
      Alcotest.(check int) "all intervals" 2 (Ucharset.num_intervals Ucharset.all))
  ; case "all excludes surrogates, keeps noncharacters" (fun () ->
      is_false "D800" (Ucharset.mem Ucharset.all 0xD800);
      is_false "DFFF" (Ucharset.mem Ucharset.all 0xDFFF);
      is_true "D7FF" (Ucharset.mem Ucharset.all 0xD7FF);
      is_true "E000" (Ucharset.mem Ucharset.all 0xE000);
      is_true "FFFE" (Ucharset.mem Ucharset.all 0xFFFE);
      is_true "FDD0" (Ucharset.mem Ucharset.all 0xFDD0);
      is_true "10FFFF" (Ucharset.mem Ucharset.all Ucharset.max_codepoint))
  ; case "singleton and range" (fun () ->
      Alcotest.check
        ivals
        "singleton"
        [ 65, 65 ]
        (Ucharset.to_list (Ucharset.singleton 65));
      Alcotest.check
        cset
        "singleton_char"
        (Ucharset.singleton 65)
        (Ucharset.singleton_char 'A');
      Alcotest.check
        ivals
        "range"
        [ 10, 20 ]
        (Ucharset.to_list (Ucharset.range ~lo:10 ~hi:20));
      Alcotest.check
        ivals
        "degenerate range"
        [ 7, 7 ]
        (Ucharset.to_list (Ucharset.range ~lo:7 ~hi:7));
      is_true "reversed range is empty" (Ucharset.is_empty (Ucharset.range ~lo:20 ~hi:10));
      Alcotest.check
        cset
        "range_char"
        (Ucharset.range ~lo:97 ~hi:122)
        (Ucharset.range_char ~lo:'a' ~hi:'z');
      Alcotest.check
        cset
        "range over everything"
        Ucharset.all
        (Ucharset.range ~lo:0 ~hi:Ucharset.max_codepoint))
  ; case "range splits around the surrogate block" (fun () ->
      Alcotest.check
        ivals
        "straddling"
        [ 0xD000, 0xD7FF; 0xE000, 0xF000 ]
        (Ucharset.to_list (Ucharset.range ~lo:0xD000 ~hi:0xF000));
      Alcotest.check
        ivals
        "up to the gap"
        [ 0xD000, 0xD7FF ]
        (Ucharset.to_list (Ucharset.range ~lo:0xD000 ~hi:0xD7FF));
      Alcotest.check
        ivals
        "from the gap"
        [ 0xE000, 0xE001 ]
        (Ucharset.to_list (Ucharset.range ~lo:0xE000 ~hi:0xE001)))
  ; case "codepoints are validated" (fun () ->
      raises_invalid "surrogate lo" (fun () -> Ucharset.singleton 0xD800);
      raises_invalid "surrogate hi" (fun () -> Ucharset.singleton 0xDFFF);
      raises_invalid "negative" (fun () -> Ucharset.singleton (-1));
      raises_invalid "past the codespace" (fun () -> Ucharset.singleton 0x110000);
      raises_invalid "range surrogate" (fun () -> Ucharset.range ~lo:0xD800 ~hi:0xD801);
      (* documented: bounds are checked even when the result would be empty *)
      raises_invalid "range validates when empty" (fun () ->
        Ucharset.range ~lo:0x110000 ~hi:0);
      raises_invalid "of_list" (fun () -> Ucharset.of_list [ 1; 0xD800 ]);
      raises_invalid "add" (fun () -> Ucharset.add Ucharset.empty 0xD900);
      raises_invalid "remove" (fun () -> Ucharset.remove Ucharset.all 0xD900))
  ; case "endpoints survive the packed sort key" (fun () ->
      (* [Builder.build] packs both endpoints of a pair into one int and sorts
         on the 42-bit key, so a narrower int drops or invents codepoints. The
         module refuses to load below 63 bits; these are the three cases that
         come back wrong at 31 and 32 bits. *)
      is_true "int is wide enough for the key" (Sys.int_size >= 63);
      Alcotest.check
        ivals
        "a pair either side of the 31-bit cutoff"
        [ 0x100, 0x100; 0x300, 0x300 ]
        (Ucharset.to_list (Ucharset.of_intervals [ 0x100, 0x100; 0x300, 0x300 ]));
      Alcotest.check
        ivals
        "the widest key the builder can form"
        [ 0x10FFFF, 0x10FFFF ]
        (Ucharset.to_list (Ucharset.of_intervals [ 0x10FFFF, 0x10FFFF ]));
      Alcotest.check
        ivals
        "an astral pair sorted against ASCII"
        [ 0x61, 0x7A; 0x1F600, 0x1F601 ]
        (Ucharset.to_list (Ucharset.of_intervals [ 0x1F600, 0x1F601; 0x61, 0x7A ])))
  ; case "of_list and of_intervals normalise" (fun () ->
      is_true "of_list []" (Ucharset.is_empty (Ucharset.of_list []));
      Alcotest.check
        cset
        "duplicates"
        (Ucharset.singleton 5)
        (Ucharset.of_list [ 5; 5; 5 ]);
      Alcotest.check
        ivals
        "adjacency"
        [ 1, 3 ]
        (Ucharset.to_list (Ucharset.of_list [ 3; 1; 2 ]));
      is_true "of_intervals []" (Ucharset.is_empty (Ucharset.of_intervals []));
      is_true
        "reversed pairs dropped"
        (Ucharset.is_empty (Ucharset.of_intervals [ 10, 5 ]));
      Alcotest.check
        ivals
        "overlapping"
        [ 1, 2; 5, 15 ]
        (Ucharset.to_list (Ucharset.of_intervals [ 5, 10; 8, 15; 1, 2 ]));
      Alcotest.check
        ivals
        "abutting"
        [ 5, 12 ]
        (Ucharset.to_list (Ucharset.of_intervals [ 5, 9; 10, 12 ]));
      Alcotest.check
        ivals
        "surrogate split"
        [ 0xD700, 0xD7FF; 0xE000, 0xE100 ]
        (Ucharset.to_list (Ucharset.of_intervals [ 0xD700, 0xE100 ])))
  ; case "the uchar family cannot raise" (fun () ->
      let a = Uchar.of_int 0x61
      and z = Uchar.of_int 0x7A in
      Alcotest.check
        cset
        "singleton_uchar"
        (Ucharset.singleton 0x61)
        (Ucharset.singleton_uchar a);
      Alcotest.check
        cset
        "range_uchar"
        (Ucharset.range ~lo:0x61 ~hi:0x7A)
        (Ucharset.range_uchar ~lo:a ~hi:z);
      Alcotest.check
        cset
        "of_uchar_list"
        (Ucharset.of_list [ 0x61; 0x7A ])
        (Ucharset.of_uchar_list [ z; a ]);
      is_true "of_uchar_list []" (Ucharset.is_empty (Ucharset.of_uchar_list []));
      Alcotest.check
        cset
        "at the top of the codespace"
        (Ucharset.singleton Ucharset.max_codepoint)
        (Ucharset.singleton_uchar (Uchar.of_int Ucharset.max_codepoint)))
  ; case "of_utf_8_string" (fun () ->
      is_true "empty" (Ucharset.is_empty (Ucharset.of_utf_8_string ""));
      Alcotest.check
        cset
        "ascii"
        (Ucharset.of_list [ 97; 98; 99 ])
        (Ucharset.of_utf_8_string "abc");
      Alcotest.check
        cset
        "duplicates"
        (Ucharset.singleton 97)
        (Ucharset.of_utf_8_string "aaa");
      Alcotest.check
        cset
        "multibyte"
        (Ucharset.of_list [ 0x61; 0xE9; 0x20AC; 0x1F600 ])
        (Ucharset.of_utf_8_string "a\xC3\xA9\xE2\x82\xAC\xF0\x9F\x98\x80");
      (* documented: malformed input yields U+FFFD *)
      is_true
        "malformed gives U+FFFD"
        (Ucharset.mem (Ucharset.of_utf_8_string "a\xFFb") 0xFFFD))
  ]
  @ qc
      [ prop
          "an out-of-range codepoint raises, naming the library"
          QCheck.(int_range (-0x1000) (Ucharset.max_codepoint + 0x1000))
          (fun cp ->
             let outcome f =
               match f () with
               | _ -> None
               | exception Invalid_argument msg -> Some msg
             in
             List.for_all
               (fun f ->
                  match outcome f with
                  | None -> is_scalar cp
                  | Some msg -> (not (is_scalar cp)) && names_library msg)
               [ (fun () -> Ucharset.singleton cp)
               ; (fun () -> Ucharset.range ~lo:cp ~hi:cp)
               ; (fun () -> Ucharset.add Ucharset.empty cp)
               ; (fun () -> Ucharset.remove Ucharset.all cp)
               ; (fun () -> Ucharset.of_list [ cp ])
               ])
      ; (* [of_intervals] goes through [Builder.build], which sorts on a packed
           key; [range] and [union] do not pack anything. Two independent
           constructions of the same set, so a key that wrapped or a sort that
           mis-ordered would show up here. *)
        prop3
          "of_intervals agrees with a union of ranges"
          (QCheck.pair arb_scalar arb_scalar)
          (QCheck.pair arb_scalar arb_scalar)
          (QCheck.pair arb_scalar arb_scalar)
          (fun (a, b, c) ->
             let ps = [ a; b; c ] in
             Ucharset.equal
               (Ucharset.of_intervals ps)
               (List.fold_left
                  (fun acc (lo, hi) -> Ucharset.union acc (Ucharset.range ~lo ~hi))
                  Ucharset.empty
                  ps))
      ; prop "of_intervals is canonical" arb_wide is_canonical
      ; prop "of_list round trips through elems" arb_small (fun t ->
          Ucharset.equal (Ucharset.of_list (elems t)) t)
      ; prop "of_intervals round trips through to_list" arb_wide (fun t ->
          Ucharset.equal (Ucharset.of_intervals (Ucharset.to_list t)) t)
      ]
;;

(* -- Queries --------------------------------------------------------------- *)

(* Words allocated by [f], per call over [n] calls. Exact: these are array and
   option allocations, nothing float or GC-dependent. *)
let words_per_call n f =
  let before = Gc.allocated_bytes () in
  for i = 0 to n - 1 do
    ignore (Sys.opaque_identity (f i))
  done;
  let after = Gc.allocated_bytes () in
  (after -. before) /. float_of_int (Sys.word_size / 8 * n)
;;

let queries =
  [ (* A local [let rec] closing over the arrays allocates its closure on every
       call, which is invisible in the answers and cost [mem] six words a call
       until the search loops were written with refs. *)
    case "the search loops allocate nothing" (fun () ->
      let n = 2000 in
      let s =
        Ucharset.of_intervals
          (List.init n (fun i -> 0x10000 + (i * 3), 0x10000 + (i * 3) + 1))
      in
      let small =
        Ucharset.of_intervals
          (List.init 20 (fun i -> 0x10000 + (i * 3), 0x10000 + (i * 3) + 1))
      in
      let s' =
        Ucharset.of_intervals
          (List.init n (fun i -> 0x10000 + (i * 3), 0x10000 + (i * 3) + 1))
      in
      let p = Ucharset.Partition.of_set s in
      (* Not exactly zero: [Gc.allocated_bytes] boxes the float it returns, two
         words spread over the run. Six words a call was the defect. *)
      let free name f =
        let w = words_per_call 1000 f in
        is_true (Printf.sprintf "%s allocates %.3f words per call" name w) (w < 0.5)
      in
      free "mem" (fun i -> Ucharset.mem s (0x10000 + (i * 7)));
      free "subset" (fun _ -> Ucharset.subset small ~of_:s);
      free "disjoint" (fun _ -> Ucharset.disjoint small s);
      free "equal" (fun _ -> Ucharset.equal s s');
      free "compare" (fun _ -> Ucharset.compare s s');
      free "hash" (fun _ -> Ucharset.hash s);
      (* [block_of_opt] pays for its [Some] and nothing else. *)
      let w =
        words_per_call 1000 (fun i ->
          Ucharset.Partition.block_of_opt p (0x10000 + (i * 3)))
      in
      is_true (Printf.sprintf "block_of_opt allocates %.3f words per call" w) (w < 2.5))
  ; case "is_all" (fun () ->
      is_true "all" (Ucharset.is_all Ucharset.all);
      is_true "comp empty" (Ucharset.is_all (Ucharset.comp Ucharset.empty));
      is_false "empty" (Ucharset.is_all Ucharset.empty);
      is_false "all minus one" (Ucharset.is_all (Ucharset.remove Ucharset.all 5));
      (* one near-miss per endpoint, so dropping any of the four comparisons
           is caught *)
      is_false
        "missing the first codepoint"
        (Ucharset.is_all (Ucharset.remove Ucharset.all 0));
      is_false
        "missing the codepoint below the surrogates"
        (Ucharset.is_all (Ucharset.remove Ucharset.all 0xD7FF));
      is_false
        "missing the codepoint above the surrogates"
        (Ucharset.is_all (Ucharset.remove Ucharset.all 0xE000));
      is_false
        "missing the last codepoint"
        (Ucharset.is_all (Ucharset.remove Ucharset.all Ucharset.max_codepoint));
      is_false
        "range including surrogates is impossible"
        (Ucharset.is_all (Ucharset.range ~lo:1 ~hi:Ucharset.max_codepoint)))
  ; case "is_singleton" (fun () ->
      is_true "one" (Ucharset.is_singleton (Ucharset.singleton 5));
      is_false "two separate" (Ucharset.is_singleton (Ucharset.of_list [ 5; 9 ]));
      is_false "two adjacent" (Ucharset.is_singleton (Ucharset.range ~lo:5 ~hi:6));
      is_false "empty" (Ucharset.is_singleton Ucharset.empty))
  ; case "mem tolerates out-of-range input" (fun () ->
      is_false "negative" (Ucharset.mem Ucharset.all (-1));
      is_false "past the top" (Ucharset.mem Ucharset.all 0x110000);
      is_false "min_int" (Ucharset.mem Ucharset.all min_int);
      is_false "max_int" (Ucharset.mem Ucharset.all max_int);
      is_true "mem_char" (Ucharset.mem_char (Ucharset.range_char ~lo:'a' ~hi:'z') 'q');
      is_true
        "mem_uchar"
        (Ucharset.mem_uchar (Ucharset.range ~lo:0x61 ~hi:0x7A) (Uchar.of_int 0x61)))
  ; case "extremes of empty and all" (fun () ->
      Alcotest.(check (option int)) "min empty" None (Ucharset.min_elt_opt Ucharset.empty);
      Alcotest.(check (option int)) "max empty" None (Ucharset.max_elt_opt Ucharset.empty);
      Alcotest.(check (option int))
        "choose empty"
        None
        (Ucharset.choose_opt Ucharset.empty);
      Alcotest.(check (option int)) "min all" (Some 0) (Ucharset.min_elt_opt Ucharset.all);
      Alcotest.(check (option int))
        "max all"
        (Some Ucharset.max_codepoint)
        (Ucharset.max_elt_opt Ucharset.all))
  ; case "next and prev step over the surrogate block" (fun () ->
      Alcotest.(check (option int))
        "next"
        (Some 0xE000)
        (Ucharset.next_elt_opt Ucharset.all 0xD7FF);
      Alcotest.(check (option int))
        "prev"
        (Some 0xD7FF)
        (Ucharset.prev_elt_opt Ucharset.all 0xE000);
      Alcotest.(check (option int))
        "next at top"
        None
        (Ucharset.next_elt_opt Ucharset.all Ucharset.max_codepoint);
      Alcotest.(check (option int))
        "prev at bottom"
        None
        (Ucharset.prev_elt_opt Ucharset.all 0);
      Alcotest.(check (option int))
        "next of empty"
        None
        (Ucharset.next_elt_opt Ucharset.empty 5);
      Alcotest.(check (option int))
        "prev of empty"
        None
        (Ucharset.prev_elt_opt Ucharset.empty 5);
      let r = Ucharset.range ~lo:10 ~hi:20 in
      Alcotest.(check (option int))
        "next from below"
        (Some 10)
        (Ucharset.next_elt_opt r 0);
      Alcotest.(check (option int))
        "next from inside"
        (Some 16)
        (Ucharset.next_elt_opt r 15);
      Alcotest.(check (option int)) "next from the end" None (Ucharset.next_elt_opt r 20);
      Alcotest.(check (option int))
        "prev from above"
        (Some 20)
        (Ucharset.prev_elt_opt r 99);
      Alcotest.(check (option int))
        "prev from inside"
        (Some 14)
        (Ucharset.prev_elt_opt r 15);
      Alcotest.(check (option int))
        "prev from the start"
        None
        (Ucharset.prev_elt_opt r 10))
  ]
  @ qc
      [ prop "to_list agrees with mem" arb_small (fun t ->
          elems t = List.filter (Ucharset.mem t) (List.init 0x200 Fun.id))
      ; prop "cardinal counts elements" arb_small (fun t ->
          Ucharset.cardinal t = List.length (elems t))
      ; prop "min and max are the extremes" arb_wide (fun t ->
          match Ucharset.to_list t with
          | [] -> Ucharset.min_elt_opt t = None && Ucharset.max_elt_opt t = None
          | (lo, _) :: _ ->
            let hi = snd (List.nth (Ucharset.to_list t) (Ucharset.num_intervals t - 1)) in
            Ucharset.min_elt_opt t = Some lo && Ucharset.max_elt_opt t = Some hi)
      ; prop "choose returns a member" arb_wide (fun t ->
          match Ucharset.choose_opt t with
          | None -> Ucharset.is_empty t
          | Some c -> Ucharset.mem t c)
      ; prop "is_all agrees with comparing to all" arb_wide (fun t ->
          Ucharset.is_all t = Ucharset.equal t Ucharset.all)
      ; prop2
          "next_elt_opt is the least member above"
          arb_small
          QCheck.(int_range (-1) 0x200)
          (fun (t, cp) ->
             Ucharset.next_elt_opt t cp
             =
             match List.filter (fun x -> x > cp) (elems t) with
             | [] -> None
             | x :: _ -> Some x)
      ; prop2
          "prev_elt_opt is the greatest member below"
          arb_small
          QCheck.(int_range (-1) 0x200)
          (fun (t, cp) ->
             Ucharset.prev_elt_opt t cp
             =
             match List.rev (List.filter (fun x -> x < cp) (elems t)) with
             | [] -> None
             | x :: _ -> Some x)
      ]
;;

(* -- Set algebra ----------------------------------------------------------- *)

let algebra_props =
  let mem l x = List.mem x l in
  [ (* exact model, on small sets *)
    prop2 "union" arb_small arb_small (fun (a, b) ->
      let ea = elems a
      and eb = elems b in
      Ucharset.equal (Ucharset.union a b) (Ucharset.of_list (ea @ eb))
      && is_canonical (Ucharset.union a b))
  ; prop2 "inter" arb_small arb_small (fun (a, b) ->
      let ea = elems a
      and eb = elems b in
      Ucharset.equal (Ucharset.inter a b) (Ucharset.of_list (List.filter (mem eb) ea))
      && is_canonical (Ucharset.inter a b))
  ; prop2 "diff" arb_small arb_small (fun (a, b) ->
      let ea = elems a
      and eb = elems b in
      Ucharset.equal
        (Ucharset.diff a ~remove:b)
        (Ucharset.of_list (List.filter (fun x -> not (mem eb x)) ea)))
  ; prop2 "xor" arb_small arb_small (fun (a, b) ->
      let ea = elems a
      and eb = elems b in
      Ucharset.equal
        (Ucharset.xor a b)
        (Ucharset.of_list
           (List.filter
              (fun x -> mem ea x <> mem eb x)
              (List.sort_uniq Stdlib.compare (ea @ eb)))))
  ; prop2 "subset" arb_small arb_small (fun (a, b) ->
      Ucharset.subset a ~of_:b = List.for_all (mem (elems b)) (elems a))
  ; prop2 "disjoint" arb_small arb_small (fun (a, b) ->
      Ucharset.disjoint a b = not (List.exists (mem (elems b)) (elems a)))
    (* probe model, over the whole codespace *)
  ; prop2 "union over the codespace" arb_wide arb_wide (fun (a, b) ->
      agrees_on [ a; b ] (Ucharset.union a b) (fun cp ->
        Ucharset.mem a cp || Ucharset.mem b cp))
  ; prop2 "inter over the codespace" arb_wide arb_wide (fun (a, b) ->
      agrees_on [ a; b ] (Ucharset.inter a b) (fun cp ->
        Ucharset.mem a cp && Ucharset.mem b cp))
  ; prop2 "diff over the codespace" arb_wide arb_wide (fun (a, b) ->
      agrees_on [ a; b ] (Ucharset.diff a ~remove:b) (fun cp ->
        Ucharset.mem a cp && not (Ucharset.mem b cp)))
  ; prop "comp over the codespace" arb_wide (fun a ->
      agrees_on [ a ] (Ucharset.comp a) (fun cp -> not (Ucharset.mem a cp)))
  ; prop3 "union_list" arb_wide arb_wide arb_wide (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.union_list [ a; b; c ])
        (Ucharset.union a (Ucharset.union b c)))
  ; prop3 "inter_list" arb_wide arb_wide arb_wide (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.inter_list [ a; b; c ])
        (Ucharset.inter a (Ucharset.inter b c)))
    (* Wide sets rarely overlap, so the property above mostly exercises the
       empty case. These use dense small sets, and more than three, so the k-way
       sweep has to keep every cursor moving. *)
  ; prop3 "inter_list on overlapping sets" arb_small arb_small arb_small (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.inter_list [ a; b; c ])
        (Ucharset.inter a (Ucharset.inter b c)))
  ; QCheck.Test.make
      ~count:300
      ~name:"inter_list of many overlapping sets"
      QCheck.(list_size (Gen.int_range 3 6) arb_small)
      (fun ts ->
         Ucharset.equal
           (Ucharset.inter_list ts)
           (List.fold_left Ucharset.inter Ucharset.all ts))
  ; QCheck.Test.make
      ~count:300
      ~name:"union_list of many overlapping sets"
      QCheck.(list_size (Gen.int_range 3 6) arb_small)
      (fun ts ->
         Ucharset.equal
           (Ucharset.union_list ts)
           (List.fold_left Ucharset.union Ucharset.empty ts))
    (* canonical results are what make equal, compare and hash exact *)
  ; prop2 "results are canonical" arb_wide arb_wide (fun (a, b) ->
      List.for_all
        is_canonical
        [ Ucharset.union a b
        ; Ucharset.inter a b
        ; Ucharset.diff a ~remove:b
        ; Ucharset.comp a
        ; Ucharset.xor a b
        ])
    (* laws *)
  ; prop "comp is involutive" arb_wide (fun a ->
      Ucharset.equal (Ucharset.comp (Ucharset.comp a)) a)
  ; prop "comp never yields a surrogate" arb_wide (fun a ->
      not (Ucharset.mem (Ucharset.comp a) 0xD800))
  ; prop2 "union commutes" arb_wide arb_wide (fun (a, b) ->
      Ucharset.equal (Ucharset.union a b) (Ucharset.union b a))
  ; prop2 "inter commutes" arb_wide arb_wide (fun (a, b) ->
      Ucharset.equal (Ucharset.inter a b) (Ucharset.inter b a))
  ; prop3 "union associates" arb_wide arb_wide arb_wide (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.union a (Ucharset.union b c))
        (Ucharset.union (Ucharset.union a b) c))
  ; prop3 "inter associates" arb_wide arb_wide arb_wide (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.inter a (Ucharset.inter b c))
        (Ucharset.inter (Ucharset.inter a b) c))
  ; prop3 "inter distributes over union" arb_wide arb_wide arb_wide (fun (a, b, c) ->
      Ucharset.equal
        (Ucharset.inter a (Ucharset.union b c))
        (Ucharset.union (Ucharset.inter a b) (Ucharset.inter a c)))
  ; prop2 "de Morgan" arb_wide arb_wide (fun (a, b) ->
      Ucharset.equal
        (Ucharset.comp (Ucharset.union a b))
        (Ucharset.inter (Ucharset.comp a) (Ucharset.comp b)))
  ; prop2 "inclusion-exclusion on cardinals" arb_wide arb_wide (fun (a, b) ->
      Ucharset.cardinal (Ucharset.union a b) + Ucharset.cardinal (Ucharset.inter a b)
      = Ucharset.cardinal a + Ucharset.cardinal b)
  ; prop2 "xor is the union of the differences" arb_wide arb_wide (fun (a, b) ->
      Ucharset.equal
        (Ucharset.xor a b)
        (Ucharset.union (Ucharset.diff a ~remove:b) (Ucharset.diff b ~remove:a)))
  ; prop "xor with itself is empty" arb_wide (fun a ->
      Ucharset.is_empty (Ucharset.xor a a))
  ; prop2 "inter is a subset of both" arb_wide arb_wide (fun (a, b) ->
      Ucharset.subset (Ucharset.inter a b) ~of_:a
      && Ucharset.subset (Ucharset.inter a b) ~of_:b)
  ; prop2 "both are subsets of the union" arb_wide arb_wide (fun (a, b) ->
      Ucharset.subset a ~of_:(Ucharset.union a b)
      && Ucharset.subset b ~of_:(Ucharset.union a b))
  ; prop2 "disjoint iff the intersection is empty" arb_wide arb_wide (fun (a, b) ->
      Ucharset.disjoint a b = Ucharset.is_empty (Ucharset.inter a b))
  ; prop "subset is reflexive" arb_wide (fun a -> Ucharset.subset a ~of_:a)
  ; prop "disjoint with itself iff empty" arb_wide (fun a ->
      Ucharset.disjoint a a = Ucharset.is_empty a)
    (* single-element and range edits *)
  ; prop2 "add" arb_small arb_scalar (fun (t, cp) ->
      Ucharset.mem (Ucharset.add t cp) cp
      && Ucharset.equal (Ucharset.add t cp) (Ucharset.union t (Ucharset.singleton cp)))
  ; prop2 "remove" arb_small arb_scalar (fun (t, cp) ->
      (not (Ucharset.mem (Ucharset.remove t cp) cp))
      && Ucharset.equal
           (Ucharset.remove t cp)
           (Ucharset.diff t ~remove:(Ucharset.singleton cp)))
  ; prop2 "add then remove" arb_small arb_scalar (fun (t, cp) ->
      Ucharset.equal (Ucharset.remove (Ucharset.add t cp) cp) (Ucharset.remove t cp))
  ; prop "add_range" arb_small (fun t ->
      Ucharset.equal
        (Ucharset.add_range t ~lo:50 ~hi:80)
        (Ucharset.union t (Ucharset.range ~lo:50 ~hi:80)))
  ; prop "remove_range" arb_small (fun t ->
      Ucharset.equal
        (Ucharset.remove_range t ~lo:50 ~hi:80)
        (Ucharset.diff t ~remove:(Ucharset.range ~lo:50 ~hi:80)))
  ]
;;

let algebra_units =
  [ case "identities" (fun () ->
      List.iter
        (fun t ->
           Alcotest.check cset "union empty" t (Ucharset.union t Ucharset.empty);
           is_true "union all" (Ucharset.is_all (Ucharset.union t Ucharset.all));
           is_true "inter empty" (Ucharset.is_empty (Ucharset.inter t Ucharset.empty));
           Alcotest.check cset "inter all" t (Ucharset.inter t Ucharset.all);
           Alcotest.check cset "diff empty" t (Ucharset.diff t ~remove:Ucharset.empty);
           is_true "diff self" (Ucharset.is_empty (Ucharset.diff t ~remove:t));
           is_true "diff all" (Ucharset.is_empty (Ucharset.diff t ~remove:Ucharset.all));
           Alcotest.check cset "xor empty" t (Ucharset.xor t Ucharset.empty);
           Alcotest.check cset "xor all" (Ucharset.comp t) (Ucharset.xor t Ucharset.all);
           is_true "subset of all" (Ucharset.subset t ~of_:Ucharset.all);
           is_true "empty is a subset" (Ucharset.subset Ucharset.empty ~of_:t);
           is_true "disjoint from empty" (Ucharset.disjoint t Ucharset.empty))
        [ Ucharset.empty
        ; Ucharset.all
        ; Ucharset.singleton 0
        ; Ucharset.singleton Ucharset.max_codepoint
        ; Ucharset.range ~lo:0 ~hi:0x7F
        ])
  ; case "list folds on the empty list" (fun () ->
      is_true "union_list []" (Ucharset.is_empty (Ucharset.union_list []));
      (* the identity for intersection is the universe *)
      is_true "inter_list []" (Ucharset.is_all (Ucharset.inter_list []));
      Alcotest.check
        cset
        "union_list [x]"
        Ucharset.all
        (Ucharset.union_list [ Ucharset.all ]);
      Alcotest.check
        cset
        "inter_list [x]"
        Ucharset.all
        (Ucharset.inter_list [ Ucharset.all ]);
      is_true
        "inter_list with an empty member"
        (Ucharset.is_empty
           (Ucharset.inter_list [ Ucharset.all; Ucharset.empty; Ucharset.all ])))
  ; case "documented physical sharing" (fun () ->
      (* the interface promises these return an argument unchanged *)
      let x = Ucharset.range ~lo:65 ~hi:90 in
      is_true "union t empty" (Ucharset.union x Ucharset.empty == x);
      is_true "union empty t" (Ucharset.union Ucharset.empty x == x);
      is_true "union all" (Ucharset.union Ucharset.all x == Ucharset.all);
      is_true "inter all" (Ucharset.inter Ucharset.all x == x);
      is_true "diff empty" (Ucharset.diff x ~remove:Ucharset.empty == x);
      is_true "add of a member" (Ucharset.add x 70 == x);
      is_true "remove of a non-member" (Ucharset.remove x 5 == x))
  ]
;;

(* -- Bulk construction ----------------------------------------------------- *)

let builder =
  [ case "empty builders" (fun () ->
      is_true
        "fresh"
        (Ucharset.is_empty (Ucharset.Builder.build (Ucharset.Builder.create ())));
      is_true
        "zero hint"
        (Ucharset.is_empty
           (Ucharset.Builder.build (Ucharset.Builder.create ~size_hint:0 ()))))
  ; case "build does not consume the builder" (fun () ->
      let b = Ucharset.Builder.create ~size_hint:1 () in
      Alcotest.(check int) "length starts at zero" 0 (Ucharset.Builder.length b);
      Ucharset.Builder.add b 5;
      Ucharset.Builder.add_interval b ~lo:10 ~hi:20;
      Alcotest.(check int) "length counts additions" 2 (Ucharset.Builder.length b);
      Alcotest.check
        ivals
        "first build"
        [ 5, 5; 10, 20 ]
        (Ucharset.to_list (Ucharset.Builder.build b));
      Alcotest.check
        ivals
        "second build"
        [ 5, 5; 10, 20 ]
        (Ucharset.to_list (Ucharset.Builder.build b));
      Ucharset.Builder.add b 6;
      Alcotest.check
        ivals
        "still usable"
        [ 5, 6; 10, 20 ]
        (Ucharset.to_list (Ucharset.Builder.build b));
      Ucharset.Builder.add_set b (Ucharset.range ~lo:100 ~hi:110);
      Alcotest.check
        ivals
        "add_set"
        [ 5, 6; 10, 20; 100, 110 ]
        (Ucharset.to_list (Ucharset.Builder.build b));
      Ucharset.Builder.add_uchar b (Uchar.of_int 0x1F600);
      is_true "add_uchar" (Ucharset.mem (Ucharset.Builder.build b) 0x1F600);
      Ucharset.Builder.reset b;
      Alcotest.(check int) "reset clears length" 0 (Ucharset.Builder.length b);
      is_true "reset clears content" (Ucharset.is_empty (Ucharset.Builder.build b));
      Ucharset.Builder.add b 42;
      Alcotest.check
        cset
        "usable after reset"
        (Ucharset.singleton 42)
        (Ucharset.Builder.build b))
  ; case "builder validation and splitting" (fun () ->
      raises_invalid "add" (fun () ->
        Ucharset.Builder.add (Ucharset.Builder.create ()) 0xD800);
      raises_invalid "add_interval" (fun () ->
        Ucharset.Builder.add_interval (Ucharset.Builder.create ()) ~lo:0 ~hi:0x110000);
      let b = Ucharset.Builder.create () in
      Ucharset.Builder.add_interval b ~lo:20 ~hi:10;
      is_true
        "reversed interval is a no-op"
        (Ucharset.is_empty (Ucharset.Builder.build b));
      let b = Ucharset.Builder.create () in
      Ucharset.Builder.add_interval b ~lo:0xD000 ~hi:0xF000;
      Alcotest.check
        ivals
        "surrogate split"
        [ 0xD000, 0xD7FF; 0xE000, 0xF000 ]
        (Ucharset.to_list (Ucharset.Builder.build b)))
  ]
  @ qc
      [ QCheck.Test.make
          ~count:300
          ~name:"builder matches of_intervals, growing past the hint"
          QCheck.(
            list_size (Gen.int_range 0 60) (pair (int_range 0 0x400) (int_range 0 0x400)))
          (fun ivs ->
             let b = Ucharset.Builder.create ~size_hint:1 () in
             List.iter (fun (lo, hi) -> Ucharset.Builder.add_interval b ~lo ~hi) ivs;
             let built = Ucharset.Builder.build b in
             Ucharset.equal built (Ucharset.of_intervals ivs) && is_canonical built)
      ; QCheck.Test.make
          ~count:200
          ~name:"builder matches repeated add_range"
          QCheck.(
            list_size (Gen.int_range 0 30) (pair (int_range 0 0x400) (int_range 0 0x400)))
          (fun ivs ->
             let b = Ucharset.Builder.create () in
             List.iter (fun (lo, hi) -> Ucharset.Builder.add_interval b ~lo ~hi) ivs;
             Ucharset.equal
               (Ucharset.Builder.build b)
               (List.fold_left
                  (fun acc (lo, hi) ->
                     if lo > hi then acc else Ucharset.add_range acc ~lo ~hi)
                  Ucharset.empty
                  ivs))
      ; prop "add_set round trips" arb_wide (fun t ->
          let b = Ucharset.Builder.create () in
          Ucharset.Builder.add_set b t;
          Ucharset.equal (Ucharset.Builder.build b) t)
      ]
;;

(* -- Iteration ------------------------------------------------------------- *)

let iteration =
  [ case "to_seq is lazy" (fun () ->
      (* forcing three elements of [all] must not walk a million codepoints *)
      Alcotest.(check (list int))
        "prefix"
        [ 0; 1; 2 ]
        (List.of_seq (Seq.take 3 (Ucharset.to_seq Ucharset.all))))
  ; case "iteration over the corners" (fun () ->
      Alcotest.(check int)
        "fold over empty"
        0
        (Ucharset.fold (fun _ a -> a + 1) Ucharset.empty 0);
      Alcotest.check
        ivals
        "intervals of all"
        [ 0, 0xD7FF; 0xE000, Ucharset.max_codepoint ]
        (List.of_seq (Ucharset.to_seq_intervals Ucharset.all));
      raises_invalid "map validates its results" (fun () ->
        Ucharset.map (fun _ -> 0xD800) (Ucharset.singleton 5)))
  ]
  @ qc
      [ prop "iter visits exactly the elements" arb_small (fun t ->
          let acc = ref [] in
          Ucharset.iter (fun cp -> acc := cp :: !acc) t;
          List.rev !acc = elems t)
      ; prop "iter_intervals visits exactly to_list" arb_wide (fun t ->
          let acc = ref [] in
          Ucharset.iter_intervals (fun lo hi -> acc := (lo, hi) :: !acc) t;
          List.rev !acc = Ucharset.to_list t)
      ; prop "fold matches iter" arb_small (fun t ->
          List.rev (Ucharset.fold (fun cp a -> cp :: a) t []) = elems t)
      ; prop "fold_intervals sums to cardinal" arb_wide (fun t ->
          Ucharset.fold_intervals (fun lo hi a -> a + hi - lo + 1) t 0
          = Ucharset.cardinal t)
      ; prop "to_seq matches elems" arb_small (fun t ->
          List.of_seq (Ucharset.to_seq t) = elems t)
      ; prop "to_seq_intervals matches to_list" arb_wide (fun t ->
          List.of_seq (Ucharset.to_seq_intervals t) = Ucharset.to_list t)
        (* [arb_small] only; [to_seq] enumerates codepoints, and a wide set can
           hold most of the codespace *)
      ; prop "of_seq inverts to_seq" arb_small (fun t ->
          Ucharset.equal (Ucharset.of_seq (Ucharset.to_seq t)) t)
      ; prop "to_seq_intervals inverts of_intervals" arb_wide (fun t ->
          Ucharset.equal
            (Ucharset.of_intervals (List.of_seq (Ucharset.to_seq_intervals t)))
            t)
      ; prop "exists finds a member" arb_small (fun t ->
          match elems t with
          | [] -> not (Ucharset.exists (fun _ -> true) t)
          | x :: _ -> Ucharset.exists (fun y -> y = x) t)
      ; prop "exists is false for a false predicate" arb_small (fun t ->
          not (Ucharset.exists (fun _ -> false) t))
      ; prop "for_all holds for membership" arb_small (fun t ->
          Ucharset.for_all (Ucharset.mem t) t)
      ; prop "for_all of false iff empty" arb_small (fun t ->
          Ucharset.for_all (fun _ -> false) t = Ucharset.is_empty t)
      ; prop "filter matches the list model" arb_small (fun t ->
          let even x = x land 1 = 0 in
          Ucharset.equal
            (Ucharset.filter even t)
            (Ucharset.of_list (List.filter even (elems t))))
      ; prop "map matches the list model" arb_small (fun t ->
          Ucharset.equal
            (Ucharset.map (fun x -> x * 3) t)
            (Ucharset.of_list (List.map (fun x -> x * 3) (elems t))))
      ; prop "filter with a true predicate is the identity" arb_small (fun t ->
          Ucharset.equal (Ucharset.filter (fun _ -> true) t) t)
      ]
;;

(* -- Compiled lookup ------------------------------------------------------- *)

let lookup_agrees t =
  let lk = Ucharset.to_lookup t in
  let ok = ref true in
  for cp = 0 to Ucharset.max_codepoint do
    if Ucharset.Lookup.mem lk cp <> Ucharset.mem t cp then ok := false
  done;
  !ok
;;

let lookup =
  [ case "agrees with mem over the whole codespace" (fun () ->
      List.iteri
        (fun i t -> is_true (Printf.sprintf "set %d" i) (lookup_agrees t))
        [ Ucharset.empty
        ; Ucharset.all
        ; Ucharset.singleton 0
        ; Ucharset.singleton Ucharset.max_codepoint
        ; Ucharset.singleton 0xD7FF
        ; Ucharset.singleton 0xE000
        ; Ucharset.range ~lo:0 ~hi:0x7F
        ; Ucharset.range ~lo:0xD000 ~hi:0xF000
        ; Ucharset.of_intervals [ 0x30, 0x39; 0x41, 0x5A; 0x61, 0x7A ]
          (* fragmented enough to push the index past 256 distinct leaves *)
        ; Ucharset.of_intervals (List.init 3000 (fun i -> i * 17, (i * 17) + 1))
        ])
  ; case "out-of-range input answers false" (fun () ->
      let lk = Ucharset.to_lookup Ucharset.all in
      List.iter
        (fun cp -> is_false (string_of_int cp) (Ucharset.Lookup.mem lk cp))
        [ -1; -1000; min_int; 0x110000; 0x200000; max_int ])
  ; case "footprint scales with the set, not the codespace" (fun () ->
      Alcotest.(check int)
        "empty"
        0
        (Ucharset.Lookup.memory_bytes (Ucharset.to_lookup Ucharset.empty));
      is_true
        "a Latin-1 set stays tiny"
        (Ucharset.Lookup.memory_bytes
           (Ucharset.to_lookup (Ucharset.range ~lo:0x41 ~hi:0x5A))
         < 256))
  ; (* The index stores one byte per page up to 256 distinct leaves and two
       bytes beyond, so 257 is the exact value at which the switch has to
       happen; at 256 the largest id is 255 and still fits in a byte, at 257 it
       is 256 and does not.

       Building exactly 257: take 256 consecutive pages starting just above the
       surrogate block, each holding one member at a different offset, so each
       has a distinct leaf. Every page below is empty and shares the all-zero
       leaf, the 257th. Starting above the surrogates matters twice over, since
       those pages cannot hold members and keeping the populated run contiguous
       is what stops a further leaf appearing. *)
    case "the index widens at exactly 257 distinct leaves" (fun () ->
      let base = 0xE000 lsr 8 in
      let cps = List.init 256 (fun k -> ((base + k) * 256) + k) in
      let s = Ucharset.of_list cps in
      Alcotest.(check int) "populated pages" 256 (Ucharset.num_intervals s);
      let lk = Ucharset.to_lookup s in
      (* (base + 256) pages of two-byte index, plus 257 leaves of 32 bytes *)
      Alcotest.(check int)
        "footprint implies a two-byte index"
        (((base + 256) * 2) + (257 * 32))
        (Ucharset.Lookup.memory_bytes lk);
      let bad = ref 0 in
      for cp = 0 to Ucharset.max_codepoint do
        if Ucharset.Lookup.mem lk cp <> Ucharset.mem s cp then incr bad
      done;
      Alcotest.(check int) "disagreements with mem" 0 !bad)
  ]
  @ qc
      [ QCheck.Test.make
          ~count:40
          ~name:"Lookup.mem agrees with mem everywhere"
          arb_wide
          lookup_agrees
        (* [Lookup] takes scalar values, not bytes: the byte entry point was
           removed because [ascii_table]'s reading of a high byte is the
           opposite one, and the two sat side by side. *)
      ; prop2 "mem_uchar agrees with mem" arb_wide arb_scalar (fun (t, cp) ->
          let lk = Ucharset.to_lookup t in
          Ucharset.Lookup.mem_uchar lk (Uchar.of_int cp) = Ucharset.mem t cp)
      ; prop "mem_uchar agrees with mem at the boundaries" arb_wide (fun t ->
          let lk = Ucharset.to_lookup t in
          List.for_all
            (fun cp -> Ucharset.Lookup.mem_uchar lk (Uchar.of_int cp) = Ucharset.mem t cp)
            [ 0; 0x41; 0x7F; 0x80; 0xFF; 0xD7FF; 0xE000; 0xFFFF; Ucharset.max_codepoint ])
      ]
;;

(* -- ASCII table ----------------------------------------------------------- *)

let ascii_ok t =
  let tbl = Ucharset.ascii_table t in
  String.length tbl = 256
  &&
  let ok = ref true in
  for b = 0 to 255 do
    if tbl.[b] <> '\000' <> (b <= 0x7F && Ucharset.mem t b) then ok := false
  done;
  !ok
;;

let ascii_table =
  [ case "boundary cases" (fun () ->
      List.iteri
        (fun i t -> is_true (Printf.sprintf "set %d" i) (ascii_ok t))
        [ Ucharset.empty
        ; Ucharset.all
        ; Ucharset.range ~lo:0 ~hi:0x7F
        ; Ucharset.singleton 0
        ; Ucharset.singleton 0x7F
        ; Ucharset.singleton 0x80
        ; Ucharset.range ~lo:0x70 ~hi:0x90
        ; Ucharset.range ~lo:0x80 ~hi:0x100
        ])
  ]
  @ qc
      [ prop "matches mem on the low 128, false above" arb_small ascii_ok
      ; prop "matches mem on the low 128, false above (wide)" arb_wide ascii_ok
      ]
;;

(* -- Packed encoding ------------------------------------------------------- *)

let packed =
  let be3 v =
    Printf.sprintf
      "%c%c%c"
      (Char.chr (v lsr 16))
      (Char.chr ((v lsr 8) land 0xFF))
      (Char.chr (v land 0xFF))
  in
  let pack ivs = String.concat "" (List.map (fun (a, b) -> be3 a ^ be3 b) ivs) in
  let rejected name s =
    is_true (name ^ " (opt)") (Ucharset.of_packed_string_opt s = None);
    raises_invalid (name ^ " (exn)") (fun () -> Ucharset.of_packed_string s)
  in
  [ case "empty" (fun () ->
      Alcotest.(check string) "encode" "" (Ucharset.to_packed_string Ucharset.empty);
      is_true "decode" (Ucharset.is_empty (Ucharset.of_packed_string "")))
  ; case "malformed data is rejected, not repaired" (fun () ->
      rejected "short" "abc";
      rejected "length not a multiple of six" (String.make 7 '\000');
      rejected "reversed interval" (pack [ 20, 10 ]);
      rejected "out of range" (pack [ 0, 0x110000 ]);
      rejected "surrogate" (pack [ 0xD800, 0xD800 ]);
      rejected "spanning the surrogate block" (pack [ 0, Ucharset.max_codepoint ]);
      rejected "unsorted" (pack [ 100, 200; 1, 2 ]);
      rejected "overlapping" (pack [ 1, 100; 50, 200 ]);
      (* canonical form requires a gap, so abutting intervals are malformed *)
      rejected "abutting" (pack [ 1, 10; 11, 20 ]);
      is_true
        "canonical data is accepted"
        (Ucharset.of_packed_string_opt (pack [ 1, 10; 12, 20 ]) <> None))
  ]
  @ qc
      [ prop "round trips" arb_wide (fun t ->
          Ucharset.equal (Ucharset.of_packed_string (Ucharset.to_packed_string t)) t)
      ; prop "round trips through the option form" arb_wide (fun t ->
          Ucharset.of_packed_string_opt (Ucharset.to_packed_string t) = Some t)
      ; prop "six bytes per interval" arb_wide (fun t ->
          String.length (Ucharset.to_packed_string t) = Ucharset.num_intervals t * 6)
      ]
;;

(* -- Comparison and hashing ------------------------------------------------ *)

module M = Map.Make (Ucharset)

let compare_hash =
  [ case "usable as a map key" (fun () ->
      let sets =
        [ Ucharset.empty; Ucharset.all; Ucharset.singleton 5; Ucharset.range ~lo:1 ~hi:9 ]
      in
      let m = List.fold_left (fun m s -> M.add s (Ucharset.cardinal s) m) M.empty sets in
      is_true
        "every key is found"
        (List.for_all (fun s -> M.find_opt s m = Some (Ucharset.cardinal s)) sets))
  ; case "hash separates sets the endpoints alone do not" (fun () ->
      (* [empty] and [singleton 0] have the same endpoint fold, every endpoint
         being zero, so only the interval count tells them apart. *)
      let sets =
        [ Ucharset.empty
        ; Ucharset.singleton 0
        ; Ucharset.range ~lo:0 ~hi:1
        ; Ucharset.of_list [ 0; 2 ]
        ; Ucharset.all
        ]
      in
      Alcotest.(check int)
        "distinct sets, distinct hashes"
        (List.length sets)
        (List.length (List.sort_uniq Stdlib.compare (List.map Ucharset.hash sets))))
  ]
  @ qc
      [ prop "hash is non-negative" arb_wide (fun t -> Ucharset.hash t >= 0)
      ; prop "equal is reflexive" arb_wide (fun a ->
          Ucharset.equal a a && Ucharset.compare a a = 0)
      ; prop "a structural copy compares equal" arb_wide (fun a ->
          (* a copy is not physically equal, so this takes the slow path *)
          let a' = Ucharset.of_packed_string (Ucharset.to_packed_string a) in
          Ucharset.equal a a'
          && Ucharset.compare a a' = 0
          && Ucharset.hash a = Ucharset.hash a')
      ; prop2 "equal iff compare is zero" arb_wide arb_wide (fun (a, b) ->
          Ucharset.equal a b = (Ucharset.compare a b = 0))
      ; prop2 "compare is antisymmetric" arb_wide arb_wide (fun (a, b) ->
          Ucharset.compare a b = 0 || Ucharset.compare a b = -Ucharset.compare b a)
      ; prop2 "equal sets hash alike" arb_wide arb_wide (fun (a, b) ->
          (not (Ucharset.equal a b)) || Ucharset.hash a = Ucharset.hash b)
      ; prop3 "compare is transitive" arb_small arb_small arb_small (fun (a, b, c) ->
          let ( <= ) x y = Ucharset.compare x y <= 0 in
          (not (a <= b && b <= c)) || a <= c)
      ]
;;

(* -- Partition refinement -------------------------------------------------- *)

(* The reference the sweep has to match: every pairwise intersection, empties
   discarded. Uses only [inter] and [is_empty], both tested above. *)
let ref_prod_inter p q =
  List.concat_map
    (fun a ->
       List.filter_map
         (fun b ->
            let i = Ucharset.inter a b in
            if Ucharset.is_empty i then None else Some i)
         q)
    p
;;

let norm l = List.sort Ucharset.compare l

let is_partition_of_all l =
  Ucharset.is_all (Ucharset.union_list l)
  && List.for_all (fun a -> not (Ucharset.is_empty a)) l
  &&
  let rec pairwise = function
    | [] -> true
    | x :: r -> List.for_all (Ucharset.disjoint x) r && pairwise r
  in
  pairwise l
;;

(* Partitions built the way a derivative-based construction builds them. *)
let partition_of_sets cs =
  List.fold_left
    (fun acc c ->
       if Ucharset.is_empty c || Ucharset.is_all c
       then acc
       else ref_prod_inter acc [ c; Ucharset.comp c ])
    [ Ucharset.all ]
    cs
;;

let arb_partition =
  QCheck.(
    set_print
      (fun p -> String.concat " | " (List.map print_set p))
      (map partition_of_sets (list_size (Gen.int_range 0 3) arb_small)))
;;

let partition =
  [ case "empty" (fun () ->
      Alcotest.(check int)
        "no blocks"
        0
        (Ucharset.Partition.num_blocks Ucharset.Partition.empty);
      Alcotest.(check (list (of_pp Ucharset.pp)))
        "no blocks to list"
        []
        (Ucharset.Partition.blocks Ucharset.Partition.empty);
      Alcotest.(check (list int))
        "no representatives"
        []
        (Ucharset.Partition.representatives Ucharset.Partition.empty);
      Alcotest.(check int)
        "of_blocks []"
        0
        (Ucharset.Partition.num_blocks (Ucharset.Partition.of_blocks []));
      (* meeting partitions whose supports are disjoint *)
      Alcotest.(check int)
        "meet of disjoint supports"
        0
        (Ucharset.Partition.num_blocks
           (Ucharset.Partition.meet
              (Ucharset.Partition.of_blocks [ Ucharset.range ~lo:0 ~hi:10 ])
              (Ucharset.Partition.of_blocks [ Ucharset.range ~lo:20 ~hi:30 ])));
      Alcotest.(check int)
        "meet with empty"
        0
        (Ucharset.Partition.num_blocks
           (Ucharset.Partition.meet Ucharset.Partition.empty Ucharset.Partition.universe));
      raises_invalid "no block to index" (fun () ->
        Ucharset.Partition.block Ucharset.Partition.empty 0))
  ; case "block_of_opt degenerate partitions" (fun () ->
      let blk = Alcotest.(option int) in
      Alcotest.check
        blk
        "empty partition contains nothing"
        None
        (Ucharset.Partition.block_of_opt Ucharset.Partition.empty 65);
      Alcotest.check
        blk
        "universe puts everything in block 0"
        (Some 0)
        (Ucharset.Partition.block_of_opt Ucharset.Partition.universe 65);
      Alcotest.check
        blk
        "universe, at the top of the codespace"
        (Some 0)
        (Ucharset.Partition.block_of_opt Ucharset.Partition.universe 0x10FFFF);
      (* Any int is a question, as with [mem]: no block holds a surrogate or a
         value off the end of the codespace. *)
      List.iter
        (fun cp ->
           Alcotest.check
             blk
             (Printf.sprintf "not a scalar value: %d" cp)
             None
             (Ucharset.Partition.block_of_opt Ucharset.Partition.universe cp))
        [ -1; min_int; 0xD800; 0xDFFF; Ucharset.max_codepoint + 1; max_int ])
  ; case "universe" (fun () ->
      Alcotest.(check int)
        "one block"
        1
        (Ucharset.Partition.num_blocks Ucharset.Partition.universe);
      Alcotest.(check (list (of_pp Ucharset.pp)))
        "the block is all"
        [ Ucharset.all ]
        (Ucharset.Partition.blocks Ucharset.Partition.universe);
      Alcotest.(check (list (of_pp Ucharset.pp)))
        "meet_all []"
        [ Ucharset.all ]
        (Ucharset.Partition.blocks (Ucharset.Partition.meet_all []));
      Alcotest.(check (list (of_pp Ucharset.pp)))
        "refine_all []"
        [ Ucharset.all ]
        (Ucharset.refine_all []);
      Alcotest.(check (list (of_pp Ucharset.pp)))
        "refine [] q"
        []
        (Ucharset.refine [] [ Ucharset.all ]))
  ; case "of_set" (fun () ->
      (* empty and full give a single block, the two-block form collapsing
           when one side would be empty *)
      Alcotest.(check int)
        "of empty"
        1
        (Ucharset.Partition.num_blocks (Ucharset.Partition.of_set Ucharset.empty));
      Alcotest.(check int)
        "of all"
        1
        (Ucharset.Partition.num_blocks (Ucharset.Partition.of_set Ucharset.all));
      let c = Ucharset.range ~lo:97 ~hi:122 in
      Alcotest.(check int)
        "of a proper subset"
        2
        (Ucharset.Partition.num_blocks (Ucharset.Partition.of_set c));
      is_true
        "the two blocks are c and its complement"
        (norm (Ucharset.Partition.blocks (Ucharset.Partition.of_set c))
         = norm [ c; Ucharset.comp c ]);
      Alcotest.(check (list int))
        "blocks are numbered by least element, not by position"
        [ 0; 97 ]
        (Ucharset.Partition.representatives (Ucharset.Partition.of_set c)))
  ; case "misuse is rejected" (fun () ->
      Alcotest.(check int)
        "empty blocks are dropped"
        0
        (Ucharset.Partition.num_blocks (Ucharset.Partition.of_blocks [ Ucharset.empty ]));
      raises_invalid "overlapping blocks" (fun () ->
        Ucharset.Partition.of_blocks
          [ Ucharset.range ~lo:0 ~hi:10; Ucharset.range ~lo:5 ~hi:20 ]);
      raises_invalid "refine with overlapping blocks" (fun () ->
        Ucharset.refine
          [ Ucharset.range ~lo:0 ~hi:10; Ucharset.range ~lo:5 ~hi:20 ]
          [ Ucharset.all ]);
      raises_invalid "block index" (fun () ->
        Ucharset.Partition.block Ucharset.Partition.universe 5);
      raises_invalid "representative index" (fun () ->
        Ucharset.Partition.representative Ucharset.Partition.universe 1))
  ; case "a partition need not cover the codespace" (fun () ->
      let sub =
        Ucharset.Partition.of_blocks
          [ Ucharset.range ~lo:0 ~hi:10; Ucharset.range ~lo:20 ~hi:30 ]
      in
      is_true
        "meet with the universe is the identity"
        (norm
           (Ucharset.Partition.blocks
              (Ucharset.Partition.meet sub Ucharset.Partition.universe))
         = norm [ Ucharset.range ~lo:0 ~hi:10; Ucharset.range ~lo:20 ~hi:30 ]))
  ; case "meet sizes its scratch space by blocks, not segments" (fun () ->
      (* [meet]'s probe table and [rep] buffer are indexed by block, so cost
         must not follow the segment count. 10.5 words per segment is the
         output; sizing either buffer from segments measured 12.5 and 26.5.
         The count puts [2 * (np + nq)] just past 2^17, the worst case. *)
      let spread ~off =
        Ucharset.of_intervals (List.init 16385 (fun i -> off + (i * 3), off + (i * 3)))
      in
      let p = Ucharset.Partition.of_set (spread ~off:0)
      and q = Ucharset.Partition.of_set (spread ~off:1) in
      let segments =
        List.fold_left
          (fun acc b -> acc + List.length (Ucharset.to_list b))
          0
          (Ucharset.Partition.blocks p)
      in
      let before = Gc.allocated_bytes () in
      let m = Ucharset.Partition.meet p q in
      let after = Gc.allocated_bytes () in
      let per_segment =
        (after -. before) /. float_of_int (Sys.word_size / 8 * segments)
      in
      Alcotest.(check int) "two blocks a side" 2 (Ucharset.Partition.num_blocks p);
      is_true
        "the meet stays small"
        (Ucharset.Partition.num_blocks m
         <= Ucharset.Partition.num_blocks p * Ucharset.Partition.num_blocks q);
      is_true
        (Printf.sprintf
           "meeting %d segments allocated %.1f words per segment, over the 12 \
            block-indexed scratch space allows"
           segments
           per_segment)
        (per_segment <= 12.))
  ]
  @ qc
      [ prop
          "generated partitions really are partitions"
          arb_partition
          is_partition_of_all
      ; prop2
          "refine matches pairwise intersection"
          arb_partition
          arb_partition
          (fun (p, q) -> norm (Ucharset.refine p q) = norm (ref_prod_inter p q))
      ; prop2 "refine yields a partition" arb_partition arb_partition (fun (p, q) ->
          is_partition_of_all (Ucharset.refine p q))
      ; prop2 "refine blocks are canonical" arb_partition arb_partition (fun (p, q) ->
          List.for_all is_canonical (Ucharset.refine p q))
      ; prop2
          "refine blocks come out in increasing order"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let mins =
               List.map
                 (fun b -> Option.get (Ucharset.min_elt_opt b))
                 (Ucharset.refine p q)
             in
             mins = List.sort Stdlib.compare mins)
      ; prop2
          "the refinement refines both inputs"
          arb_partition
          arb_partition
          (fun (p, q) ->
             List.for_all
               (fun b ->
                  List.exists (fun a -> Ucharset.subset b ~of_:a) p
                  && List.exists (fun a -> Ucharset.subset b ~of_:a) q)
               (Ucharset.refine p q))
      ; prop2
          "Partition.blocks agrees with refine"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let m =
               Ucharset.Partition.meet
                 (Ucharset.Partition.of_blocks p)
                 (Ucharset.Partition.of_blocks q)
             in
             Ucharset.Partition.blocks m = Ucharset.refine p q
             && Ucharset.Partition.num_blocks m = List.length (Ucharset.refine p q))
      ; prop2
          (* The bound [meet] sizes its probe table by. Exceed it and the
             table fills, leaving the probe loop spinning. Tight on
             generated input, so not vacuous. *)
          "meet invents no more blocks than its inputs have pairs"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let p = Ucharset.Partition.of_blocks p
             and q = Ucharset.Partition.of_blocks q in
             Ucharset.Partition.num_blocks (Ucharset.Partition.meet p q)
             <= Ucharset.Partition.num_blocks p * Ucharset.Partition.num_blocks q)
      ; prop "of_blocks numbers its own blocks by least element" arb_partition (fun p ->
          let m = Ucharset.Partition.of_blocks p in
          let reps = Ucharset.Partition.representatives m in
          reps = List.sort Stdlib.compare reps
          && reps
             = List.map
                 (fun b -> Option.get (Ucharset.min_elt_opt b))
                 (Ucharset.Partition.blocks m))
      ; prop2
          "representatives are the least elements"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let m =
               Ucharset.Partition.meet
                 (Ucharset.Partition.of_blocks p)
                 (Ucharset.Partition.of_blocks q)
             in
             Ucharset.Partition.representatives m
             = List.map
                 (fun b -> Option.get (Ucharset.min_elt_opt b))
                 (Ucharset.Partition.blocks m))
      ; prop2
          "each representative lies in its block"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let m =
               Ucharset.Partition.meet
                 (Ucharset.Partition.of_blocks p)
                 (Ucharset.Partition.of_blocks q)
             in
             List.for_all
               (fun i ->
                  Ucharset.mem
                    (Ucharset.Partition.block m i)
                    (Ucharset.Partition.representative m i))
               (List.init (Ucharset.Partition.num_blocks m) Fun.id))
      ; prop2
          "block i matches the i-th of blocks"
          arb_partition
          arb_partition
          (fun (p, q) ->
             let m =
               Ucharset.Partition.meet
                 (Ucharset.Partition.of_blocks p)
                 (Ucharset.Partition.of_blocks q)
             in
             let bs = Ucharset.Partition.blocks m in
             List.for_all
               (fun i -> Ucharset.equal (Ucharset.Partition.block m i) (List.nth bs i))
               (List.init (Ucharset.Partition.num_blocks m) Fun.id))
      ; QCheck.Test.make
          ~count:200
          ~name:"refine_all matches folding refine"
          QCheck.(list_size (Gen.int_range 0 5) arb_partition)
          (fun ps ->
             norm (Ucharset.refine_all ps)
             = norm (List.fold_left Ucharset.refine [ Ucharset.all ] ps))
      ; QCheck.Test.make
          ~count:200
          ~name:"meet_all matches folding meet"
          QCheck.(list_size (Gen.int_range 0 5) arb_partition)
          (fun ps ->
             let pps = List.map Ucharset.Partition.of_blocks ps in
             norm (Ucharset.Partition.blocks (Ucharset.Partition.meet_all pps))
             = norm
                 (Ucharset.Partition.blocks
                    (List.fold_left
                       Ucharset.Partition.meet
                       Ucharset.Partition.universe
                       pps)))
      ; prop "meet with the universe is the identity" arb_partition (fun p ->
          norm (Ucharset.refine p [ Ucharset.all ]) = norm p)
      ; prop "refine is idempotent" arb_partition (fun p ->
          norm (Ucharset.refine p p) = norm p)
      ; prop2 "refine commutes" arb_partition arb_partition (fun (p, q) ->
          norm (Ucharset.refine p q) = norm (Ucharset.refine q p))
      ; prop
          "block_of_opt agrees with membership in that block"
          (QCheck.pair arb_partition arb_scalar)
          (fun (p, cp) ->
             let p = Ucharset.Partition.of_blocks p in
             match Ucharset.Partition.block_of_opt p cp with
             | None ->
               (* Not in any block: no block may contain it. *)
               List.for_all
                 (fun b -> not (Ucharset.mem b cp))
                 (Ucharset.Partition.blocks p)
             | Some i -> Ucharset.mem (Ucharset.Partition.block p i) cp)
      ; prop "block_of_opt inverts representative" arb_partition (fun p ->
          let p = Ucharset.Partition.of_blocks p in
          let n = Ucharset.Partition.num_blocks p in
          let rec go i =
            i >= n
            || (Ucharset.Partition.block_of_opt p (Ucharset.Partition.representative p i)
                = Some i
                && go (i + 1))
          in
          go 0)
      ]
;;

(* -- Printing -------------------------------------------------------------- *)

(* Random ranges over the codespace merge into a handful of runs, so a set whose
   printed forms overflow the default 78-column margin has to be built from
   spread singletons: 40 members already need 79 columns in the tightest of the
   three forms. *)
let arb_spread =
  QCheck.(
    set_print
      print_set
      (map ~rev:elems Ucharset.of_list (list_size (Gen.int_range 40 60) arb_scalar)))
;;

let printing =
  [ case "pp" (fun () ->
      let s = Ucharset.of_intervals [ 97, 122; 181, 181; 223, 246 ] in
      Alcotest.(check string)
        "decimal"
        "[97-122; 181; 223-246]"
        (Format.asprintf "%a" Ucharset.pp s);
      Alcotest.(check string)
        "hex"
        "[U+0061-U+007A; U+00B5; U+00DF-U+00F6]"
        (Format.asprintf "%a" Ucharset.pp_hex s);
      Alcotest.(check string)
        "empty"
        "[]"
        (Format.asprintf "%a" Ucharset.pp Ucharset.empty);
      Alcotest.(check string)
        "empty hex"
        "[]"
        (Format.asprintf "%a" Ucharset.pp_hex Ucharset.empty);
      Alcotest.(check string)
        "all"
        "[0-55295; 57344-1114111]"
        (Format.asprintf "%a" Ucharset.pp Ucharset.all);
      Alcotest.(check string)
        "above the BMP"
        "[U+1F600]"
        (Format.asprintf "%a" Ucharset.pp_hex (Ucharset.singleton 0x1F600)))
  ; case "the string forms agree with the printers" (fun () ->
      let s = Ucharset.of_intervals [ 97, 103; 106, 106; 109, 116 ] in
      Alcotest.(check string) "to_string" "[97-103; 106; 109-116]" (Ucharset.to_string s);
      Alcotest.(check string)
        "to_hex_string"
        "[U+0061-U+0067; U+006A; U+006D-U+0074]"
        (Ucharset.to_hex_string s);
      Alcotest.(check string) "to_class_string" "{a-g j m-t}" (Ucharset.to_class_string s))
  ; case "pp_class" (fun () ->
      let cls t = Format.asprintf "%a" Ucharset.pp_class t in
      Alcotest.(check string) "empty" "{}" (cls Ucharset.empty);
      Alcotest.(check string)
        "a range"
        "{a-z}"
        (cls (Ucharset.range_char ~lo:'a' ~hi:'z'));
      Alcotest.(check string)
        "several runs"
        "{0-9 A-Z _ a-z}"
        (cls (Ucharset.of_intervals [ 0x30, 0x39; 0x41, 0x5A; 0x5F, 0x5F; 0x61, 0x7A ]));
      (* the separators and the escape itself, as members *)
      Alcotest.(check string)
        "escaped metacharacters"
        "{\\u{20} \\- \\\\ \\{ \\}}"
        (cls (Ucharset.of_list [ 0x20; 0x2D; 0x5C; 0x7B; 0x7D ]));
      Alcotest.(check string)
        "named control escapes"
        "{\\0 \\t-\\r}"
        (cls (Ucharset.of_list [ 0x00; 0x09; 0x0A; 0x0B; 0x0C; 0x0D ]));
      Alcotest.(check string) "first printable" "{!}" (cls (Ucharset.singleton 0x21));
      Alcotest.(check string) "last printable" "{~}" (cls (Ucharset.singleton 0x7E));
      Alcotest.(check string) "DEL" "{\\u{7F}}" (cls (Ucharset.singleton 0x7F));
      Alcotest.(check string)
        "C1 controls"
        "{\\u{80}-\\u{84}}"
        (cls (Ucharset.range ~lo:0x80 ~hi:0x84));
      (* members are written as themselves, UTF-8 encoded *)
      Alcotest.(check string)
        "latin-1, currency, astral"
        "{é € 😀-😁}"
        (cls (Ucharset.of_intervals [ 0xE9, 0xE9; 0x20AC, 0x20AC; 0x1F600, 0x1F601 ]));
      Alcotest.(check string) "greek" "{α-ω}" (cls (Ucharset.range ~lo:0x3B1 ~hi:0x3C9));
      (* U+D7FF, U+E000 and U+10FFFF as their UTF-8 bytes; the last two are
           unrenderable, so a literal would be unreadable here *)
      Alcotest.(check string)
        "all"
        "{\\0-\xed\x9f\xbf \xee\x80\x80-\xf4\x8f\xbf\xbf}"
        (cls Ucharset.all))
  ; case "the string forms do not wrap" (fun () ->
      (* twelve singletons print to 106 columns, so the default 78-column
         margin used to fold this onto two lines *)
      let wide = Ucharset.of_list (List.init 12 (fun i -> 1 + (4 * i))) in
      let expected =
        "[U+0001; U+0005; U+0009; U+000D; U+0011; U+0015; U+0019; U+001D; U+0021; "
        ^ "U+0025; U+0029; U+002D]"
      in
      Alcotest.(check string) "to_hex_string" expected (Ucharset.to_hex_string wide);
      (* the printers keep their break hints; only the string forms are unbounded *)
      is_true
        "pp_hex still wraps at the formatter margin"
        (String.contains (Format.asprintf "%a" Ucharset.pp_hex wide) '\n'))
  ; case "printing leaves the shared formatter alone" (fun () ->
      Format.fprintf Format.str_formatter "SENTINEL";
      ignore (Format.asprintf "%a" Ucharset.pp Ucharset.all);
      ignore (Format.asprintf "%a" Ucharset.pp_hex Ucharset.all);
      ignore (Format.asprintf "%a" Ucharset.pp_class Ucharset.all);
      Alcotest.(check string) "untouched" "SENTINEL" (Format.flush_str_formatter ()))
  ]
  @ qc
      [ (* members render as themselves, so the output is UTF-8; it must never
           carry a control character through to the terminal, the newline
           included, the string forms being unwrapped *)
        prop "pp_class emits valid UTF-8 free of controls" arb_wide (fun t ->
          let s = Ucharset.to_class_string t in
          let n = String.length s in
          let rec go i =
            i >= n
            ||
            let d = String.get_utf_8_uchar s i in
            Uchar.utf_decode_is_valid d
            &&
            let u = Uchar.to_int (Uchar.utf_decode_uchar d) in
            u >= 0x20
            && u <> 0x7F
            && (not (u >= 0x80 && u <= 0x9F))
            && go (i + Uchar.utf_decode_length d)
          in
          go 0)
      ; prop "pp_class is brace-delimited" arb_wide (fun t ->
          let s = Ucharset.to_class_string t in
          String.length s >= 2 && s.[0] = '{' && s.[String.length s - 1] = '}')
      ; prop "the string forms never wrap" arb_spread (fun t ->
          (* the first conjunct is the generator doing its job: unless the
             printer itself wraps, the law below is vacuous *)
          String.contains (Format.asprintf "%a" Ucharset.pp t) '\n'
          && List.for_all
               (fun s -> not (String.contains s '\n'))
               [ Ucharset.to_string t
               ; Ucharset.to_hex_string t
               ; Ucharset.to_class_string t
               ])
      ; prop "the string forms match their printers, unwrapped" arb_spread (fun t ->
          (* every break in these [hov 1] boxes is a newline plus one space of
             indent, standing in for the space the hint would have printed, so
             dropping the newlines recovers the unwrapped text *)
          let joined s = String.concat "" (String.split_on_char '\n' s) in
          Ucharset.to_string t = joined (Format.asprintf "%a" Ucharset.pp t)
          && Ucharset.to_hex_string t = joined (Format.asprintf "%a" Ucharset.pp_hex t)
          && Ucharset.to_class_string t
             = joined (Format.asprintf "%a" Ucharset.pp_class t))
      ]
;;

(* -- Bulk construction at scale ---------------------------------------------

   [Builder.build] and [of_list] pick one of three sorts by input: an ascending
   pass, a merge sort below an internal size threshold, a radix sort at or
   above it. The generators above make at most a dozen intervals, so these
   check all three at sizes straddling the threshold, against a bitmap oracle.

   The span stays below the surrogate block, so every generated codepoint is a
   scalar value. *)

let bulk =
  let span = 0xD000 in
  (* Canonical runs of a codepoint list, computed by marking a bitmap. *)
  let oracle cps =
    let seen = Bytes.make span '\000' in
    List.iter
      (fun (lo, hi) ->
         for cp = lo to hi do
           Bytes.set seen cp '\001'
         done)
      cps;
    let out = ref []
    and i = ref 0 in
    while !i < span do
      if Bytes.get seen !i = '\001'
      then (
        let lo = !i in
        while !i < span && Bytes.get seen !i = '\001' do
          incr i
        done;
        out := (lo, !i - 1) :: !out)
      else incr i
    done;
    List.rev !out
  in
  let check_at n ~width =
    let st = Random.State.make [| n; width |] in
    let pairs =
      List.init n (fun _ ->
        let lo = Random.State.int st (span - width - 1) in
        lo, lo + Random.State.int st width)
    in
    let expected = oracle pairs in
    let ascending = List.sort compare pairs in
    let label suffix = Printf.sprintf "n=%d width=%d %s" n width suffix in
    (* of_intervals, shuffled and ascending: same answer either way. *)
    Alcotest.(check ivals)
      (label "of_intervals shuffled")
      expected
      (Ucharset.to_list (Ucharset.of_intervals pairs));
    Alcotest.(check ivals)
      (label "of_intervals ascending")
      expected
      (Ucharset.to_list (Ucharset.of_intervals ascending));
    (* Builder, the same two orders. *)
    let via_builder ps =
      let b = Ucharset.Builder.create () in
      List.iter (fun (lo, hi) -> Ucharset.Builder.add_interval b ~lo ~hi) ps;
      Ucharset.to_list (Ucharset.Builder.build b)
    in
    Alcotest.(check ivals) (label "Builder shuffled") expected (via_builder pairs);
    Alcotest.(check ivals) (label "Builder ascending") expected (via_builder ascending);
    (* of_list takes the single-codepoint sort, a different key width. *)
    let singles = List.map fst pairs in
    Alcotest.(check ivals)
      (label "of_list")
      (oracle (List.map (fun c -> c, c) singles))
      (Ucharset.to_list (Ucharset.of_list singles))
  in
  [ (* Width 1 keeps every interval a singleton, so runs = cardinal; wider
       intervals overlap and exercise canonicalization too. *)
    case "below the threshold" (fun () ->
      check_at 100 ~width:1;
      check_at 100 ~width:40)
  ; case "either side of the threshold" (fun () ->
      check_at 511 ~width:1;
      check_at 512 ~width:1;
      check_at 513 ~width:1;
      check_at 512 ~width:40)
  ; case "well past the threshold" (fun () ->
      check_at 5000 ~width:1;
      check_at 5000 ~width:60;
      check_at 20000 ~width:3)
  ; (* The radix sort keys on both endpoints; intervals sharing a lower bound
       must still come out ordered. *)
    case "shared lower bounds" (fun () ->
      let pairs = List.init 2000 (fun i -> 100, 100 + (i mod 500)) in
      Alcotest.(check ivals)
        "duplicated lo"
        (oracle pairs)
        (Ucharset.to_list (Ucharset.of_intervals pairs)))
  ; case "already ascending and dense" (fun () ->
      let pairs = List.init 4000 (fun i -> i * 3, (i * 3) + 1) in
      Alcotest.(check ivals)
        "ascending"
        (oracle pairs)
        (Ucharset.to_list (Ucharset.of_intervals pairs)))
  ]
;;

(* -- Element-wise traversal --------------------------------------------------

   [filter] emits one interval per surviving run, so every boundary matters: a
   run starting where an input interval starts, one ending where it ends, a
   codepoint dropped from the middle, everything dropped, nothing dropped.
   [fold], [exists] and [for_all] share that traversal and are checked here
   against the same model. *)

let traversal =
  let of_elems cps = Ucharset.of_list cps in
  let elems t = List.of_seq (Ucharset.to_seq t) in
  let check_traversal name t f =
    let expected = of_elems (List.filter f (elems t)) in
    Alcotest.(check cset) (name ^ ": filter") expected (Ucharset.filter f t);
    (* Same traversal. *)
    Alcotest.(check int)
      (name ^ ": fold")
      (List.fold_left (fun n cp -> n lxor cp) 0 (elems t))
      (Ucharset.fold (fun cp n -> n lxor cp) t 0);
    Alcotest.(check bool)
      (name ^ ": exists")
      (List.exists f (elems t))
      (Ucharset.exists f t);
    Alcotest.(check bool)
      (name ^ ": for_all")
      (List.for_all f (elems t))
      (Ucharset.for_all f t)
  in
  let shapes =
    [ "empty", Ucharset.empty
    ; "singleton", Ucharset.singleton 5
    ; "one run", Ucharset.range ~lo:10 ~hi:20
    ; "at zero", Ucharset.range ~lo:0 ~hi:7
    ; ( "at the top"
      , Ucharset.range ~lo:(Ucharset.max_codepoint - 7) ~hi:Ucharset.max_codepoint )
    ; "across the surrogates", Ucharset.range ~lo:0xD7FD ~hi:0xE002
    ; "many runs", Ucharset.of_intervals [ 1, 3; 7, 7; 11, 20; 40, 41 ]
    ; "comb", Ucharset.of_list (List.init 50 (fun i -> i * 2))
    ]
  in
  let preds =
    [ ("always", fun _ -> true)
    ; ("never", fun _ -> false)
    ; ("even", fun cp -> cp land 1 = 0)
    ; ("upper half", fun cp -> cp >= 15)
    ; ("lower half", fun cp -> cp <= 15)
    ; ("not the ends", fun cp -> cp <> 10 && cp <> 20)
    ; ("one hole", fun cp -> cp <> 15)
    ; ("every third", fun cp -> cp mod 3 <> 0)
    ]
  in
  List.map
    (fun (sname, t) ->
       case sname (fun () ->
         List.iter (fun (pname, f) -> check_traversal (sname ^ "/" ^ pname) t f) preds))
    shapes
;;

(* -- Galloping ---------------------------------------------------------------

   [disjoint] skips ahead by doubling and bisecting when one set's runs sit
   below the other's. The property tests above use sets of a few intervals,
   where the skip is never long enough to leave the first step. These use runs
   that sit far apart, so the gallop overshoots and has to bisect back. *)

let galloping =
  let runs ~from ~count = List.init count (fun i -> from + (i * 4), from + (i * 4) + 1) in
  (* [subset] gallops through [of_] the way [disjoint] gallops through both
     sides, so it is held to the same shapes. Its model: [t] is a subset of
     [of_] iff removing [of_] leaves nothing. *)
  let check_pair name a b want =
    Alcotest.(check bool) (name ^ " a b") want (Ucharset.disjoint a b);
    Alcotest.(check bool) (name ^ " b a") want (Ucharset.disjoint b a);
    (* The model: disjoint iff the intersection is empty. *)
    Alcotest.(check bool)
      (name ^ " vs inter")
      (Ucharset.is_empty (Ucharset.inter a b))
      (Ucharset.disjoint a b);
    Alcotest.(check bool)
      (name ^ " subset a b")
      (Ucharset.is_empty (Ucharset.diff a ~remove:b))
      (Ucharset.subset a ~of_:b);
    Alcotest.(check bool)
      (name ^ " subset b a")
      (Ucharset.is_empty (Ucharset.diff b ~remove:a))
      (Ucharset.subset b ~of_:a)
  in
  [ case "far apart, disjoint" (fun () ->
      List.iter
        (fun n ->
           let a = Ucharset.of_intervals (runs ~from:0 ~count:n) in
           let b = Ucharset.of_intervals (runs ~from:(4 * n) ~count:n) in
           check_pair (Printf.sprintf "n=%d" n) a b true)
        [ 1; 2; 3; 8; 37; 100; 1000; 5000 ])
  ; case "far apart, meeting at the end" (fun () ->
      List.iter
        (fun n ->
           let a = Ucharset.of_intervals (runs ~from:0 ~count:n) in
           (* [b] starts past [a] but reaches back to share [a]'s last run. *)
           let b =
             Ucharset.union
               (Ucharset.of_intervals (runs ~from:(4 * n) ~count:n))
               (Ucharset.singleton (4 * (n - 1)))
           in
           check_pair (Printf.sprintf "n=%d" n) a b false)
        [ 1; 2; 3; 8; 37; 100; 1000; 5000 ])
  ; (* The gallop looks for the first run ending at or after the other set's
       start. A run ending exactly there overlaps by one codepoint, and is the
       boundary the search is easiest to get wrong at. *)
    case "touching by one codepoint after a long skip" (fun () ->
      List.iter
        (fun n ->
           let a = Ucharset.of_intervals (runs ~from:0 ~count:n) in
           let last_hi = (4 * (n - 1)) + 1 in
           check_pair
             (Printf.sprintf "a ends on b's start, n=%d" n)
             a
             (Ucharset.range ~lo:last_hi ~hi:(last_hi + 100))
             false;
           check_pair
             (Printf.sprintf "b ends on a's start, n=%d" n)
             (Ucharset.of_intervals (runs ~from:100_000 ~count:n))
             (Ucharset.range ~lo:0 ~hi:100_000)
             false;
           (* A singleton meeting a run in the middle of [a], where the search
             has candidates on both sides and cannot be rescued by clamping at
             the end of the array. *)
           if n >= 8
           then (
             let mid = n / 2 in
             check_pair
               (Printf.sprintf "singleton on a middle run's end, n=%d" n)
               a
               (Ucharset.singleton ((4 * mid) + 1))
               false;
             check_pair
               (Printf.sprintf "singleton on a middle run's start, n=%d" n)
               a
               (Ucharset.singleton (4 * mid))
               false;
             check_pair
               (Printf.sprintf "singleton in a middle gap, n=%d" n)
               a
               (Ucharset.singleton ((4 * mid) + 2))
               true);
           (* One past it is a miss, and must stay one. *)
           check_pair
             (Printf.sprintf "a stops just short, n=%d" n)
             a
             (Ucharset.range ~lo:(last_hi + 1) ~hi:(last_hi + 100))
             true)
        [ 1; 2; 3; 8; 37; 100; 1000; 5000 ])
  ; case "one long run against many" (fun () ->
      let many = Ucharset.of_intervals (runs ~from:0 ~count:2000) in
      check_pair "above" many (Ucharset.range ~lo:100_000 ~hi:200_000) true;
      check_pair "overlapping" many (Ucharset.range ~lo:0 ~hi:200_000) false;
      check_pair "in a gap" many (Ucharset.singleton 2) true;
      check_pair "on a run" many (Ucharset.singleton 4) false)
  ; case "offset prefixes of a many-run set" (fun () ->
      (* Two prefixes of the same table starting at different intervals, which
         is the shape that made the linear scan visible. *)
      (* Stays below the surrogate block, and the stride keeps the runs
         apart. *)
      let ivs =
        Array.init 800 (fun i ->
          let lo = (i * 60) + (i mod 7) in
          lo, lo + (i mod 13))
      in
      let take from count =
        Ucharset.of_intervals
          (List.init count (fun i -> ivs.((from + i) mod Array.length ivs)))
      in
      List.iter
        (fun count ->
           let a = take 0 count
           and b = take 37 count in
           check_pair
             (Printf.sprintf "count=%d" count)
             a
             b
             (Ucharset.is_empty (Ucharset.inter a b)))
        [ 1; 5; 20; 37; 38; 100; 400 ])
  ; case "subset skips ahead within of_" (fun () ->
      (* Containment is where [subset] skips: every run of [t] lies in [of_],
         far from the one before. The shapes above are mostly disjoint, so
         they leave it after a run or two. *)
      List.iter
        (fun n ->
           let of_ = Ucharset.of_intervals (runs ~from:0 ~count:n) in
           let last = 4 * (n - 1) in
           let every k =
             Ucharset.of_intervals
               (List.filteri (fun i _ -> i mod k = 0) (runs ~from:0 ~count:n))
           in
           is_true "the last run alone" (Ucharset.subset (Ucharset.singleton last) ~of_);
           (* Every other run is the tight case: the run sought is the one
              after the run the single step rejects, so a skip of two lands
              past it. *)
           is_true "every other run" (Ucharset.subset (every 2) ~of_);
           is_true "every third run" (Ucharset.subset (every 3) ~of_);
           is_true "every hundredth run" (Ucharset.subset (every 100) ~of_);
           (* A fresh copy, so this walks rather than taking [t == of_]. *)
           is_true
             "an equal set"
             (Ucharset.subset (Ucharset.of_intervals (runs ~from:0 ~count:n)) ~of_);
           is_false
             "a gap between two far runs"
             (Ucharset.subset (Ucharset.singleton (last - 2)) ~of_);
           is_false
             "one run past the end"
             (Ucharset.subset (Ucharset.singleton (last + 4)) ~of_))
        [ 100; 1000; 5000 ])
  ]
;;

let () =
  Alcotest.run
    "ucharset"
    [ "constructors", constructors
    ; "queries", queries
    ; "algebra", qc algebra_props @ algebra_units
    ; "builder", builder
    ; "bulk construction", bulk
    ; "iteration", iteration
    ; "traversal", traversal
    ; "galloping", galloping
    ; "lookup", lookup
    ; "ascii_table", ascii_table
    ; "packed", packed
    ; "compare and hash", compare_hash
    ; "partition", partition
    ; "printing", printing
    ]
;;
