From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require ByteCompare ByteCompareSpec.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From Peregrine Require Import Unicode.
From Peregrine Require Import UnicodeXID.
From Peregrine Require Import Utils.
From Peregrine Require PAst.
From Peregrine Require Config.

From Stdlib Require Import Strings.Byte.

Import MonadNotation.
Local Open Scope bs_scope.



Definition eqb_byte (a b : byte) : bool :=
  ByteCompare.eqb a b.
Arguments eqb_byte : simpl never.

(* Note: the most significant bit is on the right. *)
Definition byte_compare (a b : byte) : comparison :=
  ByteCompare.compare a b.

Definition leb_byte (a b : byte) : bool :=
  match byte_compare a b with
  | Gt => false
  | _ => true
  end.


Definition is_digit (c : byte) : bool :=
  (leb_byte "0" c) && (leb_byte c "9").

Definition is_upper (c : byte) : bool :=
  (leb_byte "A" c) && (leb_byte c "Z").

Definition is_lower (c : byte) : bool :=
  (leb_byte "a" c) && (leb_byte c "z").

Definition is_letter (c : byte) : bool :=
  is_upper c ||
  is_lower c.

Definition is_alphanum (c : byte) : bool :=
  is_upper c ||
  is_lower c ||
  is_digit c.

Definition is_ocaml_start (c : byte) : bool :=
  is_letter c ||
  (eqb_byte "_" c).

Definition is_ocaml_continue (c : byte) : bool :=
  is_alphanum c ||
  (eqb_byte "_" c) ||
  (eqb_byte "'" c).

Local Notation "x :: y" := (String.String x y) : bs_scope.
Local Notation "x ^ y" := (String.append x y) : bs_scope.

Definition to_hexstring (x : byte) : string :=
  match x with
  | x00 => "00"
  | x01 => "01"
  | x02 => "02"
  | x03 => "03"
  | x04 => "04"
  | x05 => "05"
  | x06 => "06"
  | x07 => "07"
  | x08 => "08"
  | x09 => "09"
  | x0a => "0a"
  | x0b => "0b"
  | x0c => "0c"
  | x0d => "0d"
  | x0e => "0e"
  | x0f => "0f"
  | x10 => "10"
  | x11 => "11"
  | x12 => "12"
  | x13 => "13"
  | x14 => "14"
  | x15 => "15"
  | x16 => "16"
  | x17 => "17"
  | x18 => "18"
  | x19 => "19"
  | x1a => "1a"
  | x1b => "1b"
  | x1c => "1c"
  | x1d => "1d"
  | x1e => "1e"
  | x1f => "1f"
  | x20 => "20"
  | x21 => "21"
  | x22 => "22"
  | x23 => "23"
  | x24 => "24"
  | x25 => "25"
  | x26 => "26"
  | x27 => "27"
  | x28 => "28"
  | x29 => "29"
  | x2a => "2a"
  | x2b => "2b"
  | x2c => "2c"
  | x2d => "2d"
  | x2e => "2e"
  | x2f => "2f"
  | x30 => "30"
  | x31 => "31"
  | x32 => "32"
  | x33 => "33"
  | x34 => "34"
  | x35 => "35"
  | x36 => "36"
  | x37 => "37"
  | x38 => "38"
  | x39 => "39"
  | x3a => "3a"
  | x3b => "3b"
  | x3c => "3c"
  | x3d => "3d"
  | x3e => "3e"
  | x3f => "3f"
  | x40 => "40"
  | x41 => "41"
  | x42 => "42"
  | x43 => "43"
  | x44 => "44"
  | x45 => "45"
  | x46 => "46"
  | x47 => "47"
  | x48 => "48"
  | x49 => "49"
  | x4a => "4a"
  | x4b => "4b"
  | x4c => "4c"
  | x4d => "4d"
  | x4e => "4e"
  | x4f => "4f"
  | x50 => "50"
  | x51 => "51"
  | x52 => "52"
  | x53 => "53"
  | x54 => "54"
  | x55 => "55"
  | x56 => "56"
  | x57 => "57"
  | x58 => "58"
  | x59 => "59"
  | x5a => "5a"
  | x5b => "5b"
  | x5c => "5c"
  | x5d => "5d"
  | x5e => "5e"
  | x5f => "5f"
  | x60 => "60"
  | x61 => "61"
  | x62 => "62"
  | x63 => "63"
  | x64 => "64"
  | x65 => "65"
  | x66 => "66"
  | x67 => "67"
  | x68 => "68"
  | x69 => "69"
  | x6a => "6a"
  | x6b => "6b"
  | x6c => "6c"
  | x6d => "6d"
  | x6e => "6e"
  | x6f => "6f"
  | x70 => "70"
  | x71 => "71"
  | x72 => "72"
  | x73 => "73"
  | x74 => "74"
  | x75 => "75"
  | x76 => "76"
  | x77 => "77"
  | x78 => "78"
  | x79 => "79"
  | x7a => "7a"
  | x7b => "7b"
  | x7c => "7c"
  | x7d => "7d"
  | x7e => "7e"
  | x7f => "7f"
  | x80 => "80"
  | x81 => "81"
  | x82 => "82"
  | x83 => "83"
  | x84 => "84"
  | x85 => "85"
  | x86 => "86"
  | x87 => "87"
  | x88 => "88"
  | x89 => "89"
  | x8a => "8a"
  | x8b => "8b"
  | x8c => "8c"
  | x8d => "8d"
  | x8e => "8e"
  | x8f => "8f"
  | x90 => "90"
  | x91 => "91"
  | x92 => "92"
  | x93 => "93"
  | x94 => "94"
  | x95 => "95"
  | x96 => "96"
  | x97 => "97"
  | x98 => "98"
  | x99 => "99"
  | x9a => "9a"
  | x9b => "9b"
  | x9c => "9c"
  | x9d => "9d"
  | x9e => "9e"
  | x9f => "9f"
  | xa0 => "a0"
  | xa1 => "a1"
  | xa2 => "a2"
  | xa3 => "a3"
  | xa4 => "a4"
  | xa5 => "a5"
  | xa6 => "a6"
  | xa7 => "a7"
  | xa8 => "a8"
  | xa9 => "a9"
  | xaa => "aa"
  | xab => "ab"
  | xac => "ac"
  | xad => "ad"
  | xae => "ae"
  | xaf => "af"
  | xb0 => "b0"
  | xb1 => "b1"
  | xb2 => "b2"
  | xb3 => "b3"
  | xb4 => "b4"
  | xb5 => "b5"
  | xb6 => "b6"
  | xb7 => "b7"
  | xb8 => "b8"
  | xb9 => "b9"
  | xba => "ba"
  | xbb => "bb"
  | xbc => "bc"
  | xbd => "bd"
  | xbe => "be"
  | xbf => "bf"
  | xc0 => "c0"
  | xc1 => "c1"
  | xc2 => "c2"
  | xc3 => "c3"
  | xc4 => "c4"
  | xc5 => "c5"
  | xc6 => "c6"
  | xc7 => "c7"
  | xc8 => "c8"
  | xc9 => "c9"
  | xca => "ca"
  | xcb => "cb"
  | xcc => "cc"
  | xcd => "cd"
  | xce => "ce"
  | xcf => "cf"
  | xd0 => "d0"
  | xd1 => "d1"
  | xd2 => "d2"
  | xd3 => "d3"
  | xd4 => "d4"
  | xd5 => "d5"
  | xd6 => "d6"
  | xd7 => "d7"
  | xd8 => "d8"
  | xd9 => "d9"
  | xda => "da"
  | xdb => "db"
  | xdc => "dc"
  | xdd => "dd"
  | xde => "de"
  | xdf => "df"
  | xe0 => "e0"
  | xe1 => "e1"
  | xe2 => "e2"
  | xe3 => "e3"
  | xe4 => "e4"
  | xe5 => "e5"
  | xe6 => "e6"
  | xe7 => "e7"
  | xe8 => "e8"
  | xe9 => "e9"
  | xea => "ea"
  | xeb => "eb"
  | xec => "ec"
  | xed => "ed"
  | xee => "ee"
  | xef => "ef"
  | xf0 => "f0"
  | xf1 => "f1"
  | xf2 => "f2"
  | xf3 => "f3"
  | xf4 => "f4"
  | xf5 => "f5"
  | xf6 => "f6"
  | xf7 => "f7"
  | xf8 => "f8"
  | xf9 => "f9"
  | xfa => "fa"
  | xfb => "fb"
  | xfc => "fc"
  | xfd => "fd"
  | xfe => "fe"
  | xff => "ff"
  end.

Definition hex_to_hexstring (x : hex_digit) : byte :=
  match x with
  | D0 => "0"
  | D1 => "1"
  | D2 => "2"
  | D3 => "3"
  | D4 => "4"
  | D5 => "5"
  | D6 => "6"
  | D7 => "7"
  | D8 => "8"
  | D9 => "9"
  | Da => "a"
  | Db => "b"
  | Dc => "c"
  | Dd => "d"
  | De => "e"
  | Df => "f"
  end.

Coercion hex_to_hexstring : hex_digit >-> byte.

Definition escape_ascii_char (c : byte) : string :=
  "_UU" ^ to_hexstring c.

Definition escape_unicode_chars (fs : byte -> bool) (fc : byte -> bool)
                                (s : utf8_string) : string :=
  let fix aux f s {struct s} : string :=
    match s with
    | EmptyString => String.EmptyString
    | String x xs =>
      match x with
      | ascii b =>
        match (eqb_byte "_" b), xs with
        | true, String (ascii "U") (String (ascii "U") xs) =>
          (* String already contains "_UU" we replace it with "_UUU" *)
          let res := (aux fc xs) in
          ("_" :: "U" :: "U" :: "U" :: res)
        | _, _ =>
          let res := (aux fc xs) in
          (* Escape b if b isn't valid *)
          if (f b) then b :: res else
          escape_ascii_char b ^ res
        end
      | codepoint u v w x y z =>
        let res := (aux fc xs) in
        "_" :: "U" :: "U" :: u :: v :: w :: x :: y :: z :: res
      end
    end
  in aux fs s.


Definition ocaml_sanitizer (s : utf8_string) : string :=
  (* Unicode not allowed in OCaml identifiers so we escape all unicode chars *)
  escape_unicode_chars is_ocaml_start is_ocaml_continue s.

Definition cakeml_sanitizer (s : utf8_string) : string := ocaml_sanitizer s.
Definition elm_sanitizer (s : utf8_string) : string := ocaml_sanitizer s.
Definition c_sanitizer (s : utf8_string) : string := ocaml_sanitizer s.
Definition wasm_sanitizer (s : utf8_string) : string := ocaml_sanitizer s.
(* Lean 4 identifiers admit a richer character set than OCaml's, but
   the printer mangles all extracted names into ASCII-safe form already
   (constructor names get a trailing [_], etc.).  Reusing the OCaml
   sanitizer is conservatively correct. *)
Definition lean_sanitizer (s : utf8_string) : string := ocaml_sanitizer s.


Definition rust_delim : utf8_codepoint :=
  (* Ֆ U+0556 *)
  codepoint D0 D0 D0 D5 D5 D6.

Definition is_rust_keyword (s : utf8_string) : bool :=
  match s with
  | ("a" :: "s" :: EmptyString)%utf8_scope => true
  | ("b" :: "r" :: "e" :: "a" :: "k" :: EmptyString)%utf8_scope => true
  | ("c" :: "o" :: "n" :: "s" :: "t" :: EmptyString)%utf8_scope => true
  | ("c" :: "o" :: "n" :: "t" :: "i" :: "n" :: "u" :: "e" :: EmptyString)%utf8_scope => true
  | ("e" :: "l" :: "s" :: "e" :: EmptyString)%utf8_scope => true
  | ("e" :: "n" :: "u" :: "m" :: EmptyString)%utf8_scope => true
  | ("e" :: "x" :: "t" :: "e" :: "r" :: "n" :: EmptyString)%utf8_scope => true
  | ("f" :: "a" :: "l" :: "s" :: "e" :: EmptyString)%utf8_scope => true
  | ("f" :: "n" :: EmptyString)%utf8_scope => true
  | ("f" :: "o" :: "r" :: EmptyString)%utf8_scope => true
  | ("i" :: "f" :: EmptyString)%utf8_scope => true
  | ("i" :: "m" :: "p" :: "l" :: EmptyString)%utf8_scope => true
  | ("i" :: "n" :: EmptyString)%utf8_scope => true
  | ("l" :: "e" :: "t" :: EmptyString)%utf8_scope => true
  | ("l" :: "o" :: "o" :: "p" :: EmptyString)%utf8_scope => true
  | ("m" :: "a" :: "t" :: "c" :: "h" :: EmptyString)%utf8_scope => true
  | ("m" :: "o" :: "d" :: EmptyString)%utf8_scope => true
  | ("m" :: "o" :: "v" :: "e" :: EmptyString)%utf8_scope => true
  | ("m" :: "u" :: "t" :: EmptyString)%utf8_scope => true
  | ("p" :: "u" :: "b" :: EmptyString)%utf8_scope => true
  | ("r" :: "e" :: "f" :: EmptyString)%utf8_scope => true
  | ("r" :: "e" :: "t" :: "u" :: "r" :: "n" :: EmptyString)%utf8_scope => true
  | ("s" :: "t" :: "a" :: "t" :: "i" :: "c" :: EmptyString)%utf8_scope => true
  | ("s" :: "t" :: "r" :: "u" :: "c" :: "t" :: EmptyString)%utf8_scope => true
  | ("t" :: "r" :: "a" :: "i" :: "t" :: EmptyString)%utf8_scope => true
  | ("t" :: "r" :: "u" :: "e" :: EmptyString)%utf8_scope => true
  | ("t" :: "y" :: "p" :: "e" :: EmptyString)%utf8_scope => true
  | ("u" :: "n" :: "s" :: "a" :: "f" :: "e" :: EmptyString)%utf8_scope => true
  | ("u" :: "s" :: "e" :: EmptyString)%utf8_scope => true
  | ("w" :: "h" :: "e" :: "r" :: "e" :: EmptyString)%utf8_scope => true
  | ("w" :: "h" :: "i" :: "l" :: "e" :: EmptyString)%utf8_scope => true
  | ("a" :: "s" :: "y" :: "n" :: "c" :: EmptyString)%utf8_scope => true
  | ("a" :: "w" :: "a" :: "i" :: "t" :: EmptyString)%utf8_scope => true
  | ("d" :: "y" :: "n" :: EmptyString)%utf8_scope => true
  | _ => false
  end.

Definition is_forbidden_rust_keyword (s : utf8_string) : bool :=
  match s with
  | ("s" :: "e" :: "l" :: "f" :: EmptyString)%utf8_scope => true
  | ("S" :: "e" :: "l" :: "f" :: EmptyString)%utf8_scope => true
  | ("s" :: "u" :: "p" :: "e" :: "r" :: EmptyString)%utf8_scope => true
  | ("c" :: "r" :: "a" :: "t" :: "e" :: EmptyString)%utf8_scope => true
  | ("_" :: EmptyString)%utf8_scope => true
  | _ => false
  end.

Definition utf8_codepoint_to_hex (x : utf8_codepoint) : utf8_string :=
  match x with
  | ascii b =>
    let '(b0,(b1,(b2,(b3,(b4,(b5,(b6,b7))))))) := Byte.to_bits b in
    let h0 := hex_of_bits (b0,(b1,(b2,b3))) in
    let h1 := hex_of_bits (b4,(b5,(b6,b7))) in
    h1 :: h0 :: EmptyString
  | codepoint u v w x y z =>
    u :: v :: w :: x :: y :: z :: EmptyString
  end%utf8_scope.

Definition rust_esc (x : utf8_codepoint) : utf8_string :=
  match x with
  | (* "Ֆ" *) codepoint D0 D0 D0 D5 D5 D6 => String rust_delim EmptyString
  | (* "λ" *) codepoint D0 D0 D0 D3 Db Db => "l" :: "a" :: "m" :: EmptyString
  | (* "→" *) codepoint D0 D0 D2 D1 D9 D2 => "t" :: "o" :: EmptyString
  | (* "∷" *) codepoint D0 D0 D2 D2 D3 D7 => "c" :: "o" :: "n" :: "s" :: EmptyString
  | ascii "_" => "_" :: EmptyString
  | ascii "+" => "p" :: "l" :: "u" :: "s" :: EmptyString
  | ascii "-" => "s" :: "u" :: "b" :: EmptyString
  | ascii "*" => "m" :: "u" :: "l" :: "t" :: EmptyString
  | ascii "/" => "d" :: "i" :: "v" :: EmptyString
  | ascii "=" => "e" :: "q" :: EmptyString
  | ascii "<" => "l" :: "t" :: EmptyString
  | ascii ">" => "g" :: "t" :: EmptyString
  | ascii "?" => "q" :: "e" :: "n" :: EmptyString
  | ascii "!" => "b" :: "n" :: "g" :: EmptyString
  | ascii "#" => "h" :: "s" :: "h" :: EmptyString
  | ascii "." => "d" :: "o" :: "t" :: EmptyString
  | _ => String rust_delim (utf8_codepoint_to_hex x)
  end%utf8_scope.

Definition escape_rust_char (f : utf8_codepoint -> bool) (x : utf8_codepoint) : utf8_string :=
  if f x
  then String x EmptyString
  else String rust_delim (rust_esc x).

Definition rust_sanitizer_aux (s : utf8_string) : utf8_string :=
  if is_rust_keyword s then ("r" :: "#" :: s)%utf8_scope else
  if is_forbidden_rust_keyword s then (String rust_delim s)%utf8_scope else
  match s with
  | EmptyString => EmptyString
  | String x xs =>
    let x := escape_rust_char is_xid_start x in
    let xs := utf8_concat_map (escape_rust_char is_xid_continue) xs in
    utf8_append x xs
  end.

Definition rust_sanitizer (s : utf8_string) : string :=
  to_string (rust_sanitizer_aux s).

Definition skip_sanitize (s : utf8_string) : string :=
  to_string s.

Definition get_sanitizer (o : Config.config) : utf8_string -> string :=
  match o.(Config.backend_opts) with
  | Config.Rust _ => rust_sanitizer
  | Config.Elm _ => elm_sanitizer
  | Config.OCaml _ => ocaml_sanitizer
  | Config.CakeML _ => cakeml_sanitizer
  | Config.C _ => c_sanitizer
  | Config.Wasm _ => wasm_sanitizer
  | Config.Lean _ => lean_sanitizer
  (* Name sanitizing not necessary here *)
  | Config.Eval _ => skip_sanitize
  | Config.AST _ => skip_sanitize
  end.



Definition sanitize_name (f : utf8_string -> string) (n : name) : result' name :=
  match n with
  | nAnon => Ok nAnon
  | nNamed id =>
    id <- of_string id;;
    Ok (nNamed (f id))
  end.

Definition sanitize_dirpath (f : utf8_string -> string) (dp : dirpath) : result' dirpath :=
  monad_map (fun id => id <- of_string id;; Ok (f id)) dp.

Fixpoint sanitize_modpath (f : utf8_string -> string) (mp : modpath) : result' modpath :=
  match mp with
  | MPfile dp =>
    dp <- sanitize_dirpath f dp;;
    Ok (MPfile dp)
  | MPbound dp id n =>
    dp <- sanitize_dirpath f dp;;
    id <- of_string id;;
    Ok (MPbound dp (f id) n)
  | MPdot mp id =>
    mp <- sanitize_modpath f mp;;
    id <- of_string id;;
    Ok (MPdot mp (f id))
  end.

Definition sanitize_kername (f : utf8_string -> string) (k : kername) : result' kername :=
  let '(mp, id) := k in
  mp <- sanitize_modpath f mp;;
  id <- of_string id;;
  Ok (mp, f id).

Definition sanitize_inductive (f : utf8_string -> string) (i : inductive) : result' inductive :=
  kn <- sanitize_kername f i.(inductive_mind);;
  Ok {|
    inductive_mind := kn;
    inductive_ind := i.(inductive_ind);
  |}.

Definition sanitize_projection (f : utf8_string -> string) (p : projection) : result' projection :=
  ind <- sanitize_inductive f p.(proj_ind);;
  Ok {|
    proj_ind := ind;
    proj_npars := p.(proj_npars);
    proj_arg := p.(proj_arg);
  |}.

Fixpoint sanitize_term (f : utf8_string -> string) (t : EAst.term) : result' EAst.term :=
  match t with
  | EAst.tBox | EAst.tRel _ | EAst.tVar _ => Ok t
  | EAst.tEvar n l =>
    l <- monad_map (sanitize_term f) l;;
    Ok (EAst.tEvar n l)
  | EAst.tLambda na t =>
    na <- sanitize_name f na;;
    t <- sanitize_term f t;;
    Ok (EAst.tLambda na t)
  | EAst.tLetIn na b t =>
    na <- sanitize_name f na;;
    b <- sanitize_term f b;;
    t <- sanitize_term f t;;
    Ok (EAst.tLetIn na b t)
  | EAst.tApp u v =>
    u <- sanitize_term f u;;
    v <- sanitize_term f v;;
    Ok (EAst.tApp u v)
  | EAst.tConst k =>
    k <- sanitize_kername f k;;
    Ok (EAst.tConst k)
  | EAst.tConstruct ind n args =>
    ind <- sanitize_inductive f ind;;
    args <- monad_map (sanitize_term f) args;;
    Ok (EAst.tConstruct ind n args)
  | EAst.tCase indn c brs =>
    indn_1 <- sanitize_inductive f (fst indn);;
    c <- sanitize_term f c;;
    brs <- monad_map (fun '(ns, t) =>
        ns <- monad_map (sanitize_name f) ns;;
        t <- sanitize_term f t;;
        Ok (ns, t)
      ) brs;;
    Ok (EAst.tCase (indn_1, snd indn) c brs)
  | EAst.tProj p c =>
    p <- sanitize_projection f p;;
    c <- sanitize_term f c;;
    Ok (EAst.tProj p c)
  | EAst.tFix mfix idx =>
    mfix <- monad_map (fun d =>
        n <- sanitize_name f d.(EAst.dname);;
        t <- sanitize_term f d.(EAst.dbody);;
        Ok {|
          EAst.dname := n;
          EAst.dbody := t;
          EAst.rarg := d.(EAst.rarg);
        |}
      ) mfix;;
    Ok (EAst.tFix mfix idx)
  | EAst.tCoFix mfix idx =>
    mfix <- monad_map (fun d =>
        n <- sanitize_name f d.(EAst.dname);;
        t <- sanitize_term f d.(EAst.dbody);;
        Ok {|
          EAst.dname := n;
          EAst.dbody := t;
          EAst.rarg := d.(EAst.rarg);
        |}
      ) mfix;;
    Ok (EAst.tCoFix mfix idx)
  | EAst.tPrim prim => Ok (EAst.tPrim prim) (* TODO: we don't sanitize prim arrays yet *)
  | EAst.tLazy t =>
    t <- sanitize_term f t;;
    Ok (EAst.tLazy t)
  | EAst.tForce t =>
    t <- sanitize_term f t;;
    Ok (EAst.tForce t)
  end.

Definition sanitize_option {A : Type} (f : utf8_string -> string)
                          (fa : (utf8_string -> string) -> A -> result' A)
                          (o : option A)
                          : result' (option A) :=
  match o with
  | None => Ok None
  | Some a =>
    r <- fa f a;;
    Ok (Some r)
  end.

Definition sanitize_constant_body (f : utf8_string -> string) (cb : EAst.constant_body) : result' EAst.constant_body :=
  b <- sanitize_option f sanitize_term cb.(EAst.cst_body);;
  Ok {| EAst.cst_body := b |}.

Definition sanitize_constructor_body (f : utf8_string -> string) (cb : EAst.constructor_body) : result' EAst.constructor_body :=
  id <- of_string cb.(EAst.cstr_name);;
  Ok {| EAst.cstr_name := (f id); EAst.cstr_nargs := cb.(EAst.cstr_nargs) |}.

Definition sanitize_projection_body (f : utf8_string -> string) (pb : EAst.projection_body) : result' EAst.projection_body :=
  id <- of_string pb.(EAst.proj_name);;
  Ok {| EAst.proj_name := (f id) |}.

Definition sanitize_one_inductive_body (f : utf8_string -> string) (oib : EAst.one_inductive_body) : result' EAst.one_inductive_body :=
  ind_name <- of_string oib.(EAst.ind_name);;
  ctors <- monad_map (sanitize_constructor_body f) oib.(EAst.ind_ctors);;
  projs <- monad_map (sanitize_projection_body f) oib.(EAst.ind_projs);;
  Ok {|
    EAst.ind_name := f (ind_name);
    EAst.ind_propositional := oib.(EAst.ind_propositional);
    EAst.ind_kelim := oib.(EAst.ind_kelim);
    EAst.ind_ctors := ctors;
    EAst.ind_projs := projs;
  |}.

Definition sanitize_mutual_inductive_body (f : utf8_string -> string) (mib : EAst.mutual_inductive_body) : result' EAst.mutual_inductive_body :=
  bodies <- monad_map (sanitize_one_inductive_body f) mib.(EAst.ind_bodies);;
  Ok {|
    EAst.ind_finite := mib.(EAst.ind_finite);
    EAst.ind_npars := mib.(EAst.ind_npars);
    EAst.ind_bodies := bodies;
  |}.

Definition sanitize_global_decl (f : utf8_string -> string) (gd : EAst.global_decl) : result' EAst.global_decl :=
  match gd with
  | EAst.ConstantDecl cb =>
    cb <- sanitize_constant_body f cb;;
    Ok (EAst.ConstantDecl cb)
  | EAst.InductiveDecl mib =>
    mib <- sanitize_mutual_inductive_body f mib;;
    Ok (EAst.InductiveDecl mib)
  end.

Definition sanitize_untyped_env (f : utf8_string -> string) (env : PAst.untyped_env) : result' PAst.untyped_env :=
  monad_map (fun '(kn, gd) =>
    kn <- sanitize_kername f kn;;
    gd <- sanitize_global_decl f gd;;
    Ok (kn, gd)
  ) env.

Fixpoint sanitize_box_type (f : utf8_string -> string) (t : ExAst.box_type) : result' ExAst.box_type :=
  match t with
  | ExAst.TBox | ExAst.TAny | ExAst.TVar _ => Ok t
  | ExAst.TArr dom codom =>
    dom <- sanitize_box_type f dom;;
    codom <- sanitize_box_type f codom;;
    Ok (ExAst.TArr dom codom)
  | ExAst.TApp t1 t2 =>
    t1 <- sanitize_box_type f t1;;
    t2 <- sanitize_box_type f t2;;
    Ok (ExAst.TApp t1 t2)
  | ExAst.TInd ind =>
    ind <- sanitize_inductive f ind;;
    Ok (ExAst.TInd ind)
  | ExAst.TConst kn =>
    kn <- sanitize_kername f kn;;
    Ok (ExAst.TConst kn)
  end.

Definition sanitize_type_var_info (f : utf8_string -> string) (t : ExAst.type_var_info) : result' ExAst.type_var_info :=
  name <- sanitize_name f t.(ExAst.tvar_name);;
  Ok {|
    ExAst.tvar_name := name;
    ExAst.tvar_is_logical := t.(ExAst.tvar_is_logical);
    ExAst.tvar_is_arity := t.(ExAst.tvar_is_arity);
    ExAst.tvar_is_sort := t.(ExAst.tvar_is_sort);
  |}.

Definition sanitize_constant_body_t (f : utf8_string -> string) (cb : ExAst.constant_body) : result' ExAst.constant_body :=
  ns <- monad_map (sanitize_name f) (fst cb.(ExAst.cst_type));;
  type <- sanitize_box_type f (snd cb.(ExAst.cst_type));;
  body <- sanitize_option f sanitize_term cb.(ExAst.cst_body);;
  Ok {|
    ExAst.cst_type := (ns, type);
    ExAst.cst_body := body;
  |}.

Definition sanitize_one_inductive_body_t (f : utf8_string -> string) (oib : ExAst.one_inductive_body) : result' ExAst.one_inductive_body :=
  ind_name <- of_string oib.(ExAst.ind_name);;
  tvars <- monad_map (sanitize_type_var_info f) oib.(ExAst.ind_type_vars);;
  ctors <- monad_map (fun '(id, ctor, n) =>
    id <- of_string id;;
    ctor <- monad_map (fun '(n, t) =>
      n <- sanitize_name f n;;
      t <- sanitize_box_type f t;;
      Ok (n,t)
      ) ctor;;
    Ok (f id, ctor, n)
    ) oib.(ExAst.ind_ctors);;
  projs <- monad_map (fun '(id, t) =>
    id <- of_string id;;
    t <- sanitize_box_type f t;;
    Ok (f id, t)
    ) oib.(ExAst.ind_projs);;
  Ok {|
    ExAst.ind_name := f ind_name;
    ExAst.ind_propositional := oib.(ExAst.ind_propositional);
    ExAst.ind_kelim := oib.(ExAst.ind_kelim);
    ExAst.ind_type_vars := tvars;
    ExAst.ind_ctors := ctors;
    ExAst.ind_projs := projs;
  |}.

Definition sanitize_mutual_inductive_body_t (f : utf8_string -> string) (mib : ExAst.mutual_inductive_body) : result' ExAst.mutual_inductive_body :=
  oib <- monad_map (sanitize_one_inductive_body_t f) mib.(ExAst.ind_bodies);;
  Ok {|
    ExAst.ind_finite := mib.(ExAst.ind_finite);
    ExAst.ind_npars := mib.(ExAst.ind_npars);
    ExAst.ind_bodies := oib;
  |}.

Definition sanitize_global_decl_t (f : utf8_string -> string) (gd : ExAst.global_decl) : result' ExAst.global_decl :=
  match gd with
  | ExAst.ConstantDecl cb =>
    cb <- sanitize_constant_body_t f cb;;
    Ok (ExAst.ConstantDecl cb)
  | ExAst.InductiveDecl mib =>
    mib <- sanitize_mutual_inductive_body_t f mib;;
    Ok (ExAst.InductiveDecl mib)
  | ExAst.TypeAliasDecl o =>
    o <- sanitize_option f (fun f '(tvars, t) =>
      tvars <- monad_map (sanitize_type_var_info f) tvars;;
      t <- sanitize_box_type f t;;
      Ok (tvars, t)) o;;
    Ok (ExAst.TypeAliasDecl o)
  end.

Definition sanitize_typed_env (f : utf8_string -> string) (env : PAst.typed_env) : result' PAst.typed_env :=
  monad_map (fun '(kn, b, gd) =>
    kn <- sanitize_kername f kn;;
    gd <- sanitize_global_decl_t f gd;;
    Ok (kn, b, gd)
  ) env.

Definition sanitize_PAst (f : utf8_string -> string) (p : PAst.PAst) : result' PAst.PAst :=
  match p with
  | PAst.Untyped env t =>
    env <- sanitize_untyped_env f env;;
    t <- sanitize_option f sanitize_term t;;
    Ok (PAst.Untyped env t)
  | PAst.Typed env t =>
    env <- sanitize_typed_env f env;;
    t <- sanitize_option f sanitize_term t;;
    Ok (PAst.Typed env t)
  end.

Definition sanitize_extract_inductive (f : utf8_string -> string) (r : EProgram.extract_inductive) : result' EProgram.extract_inductive :=
  cstrs <- monad_map (sanitize_kername f) r.(EProgram.cstrs);;
  elim <- sanitize_kername f r.(EProgram.elim);;
  Ok {|
    EProgram.cstrs := cstrs;
    EProgram.elim := elim;
  |}.

Definition sanitize_remap_inductive (f : utf8_string -> string) (r : Config.remap_inductive) : result' Config.remap_inductive :=
  match r with
  | Config.KnIndRemap kn r =>
    kn <- sanitize_kername f kn;;
    r <- monad_map (sanitize_extract_inductive f) r;;
    Ok (Config.KnIndRemap kn r)
  | Config.StringIndRemap ind r =>
    ind <- sanitize_inductive f ind;;
    Ok (Config.StringIndRemap ind r)
  end.

Definition sanitize_config (f : utf8_string -> string) (c : Config.config) : result' Config.config :=
  inls <- monad_map (sanitize_kername f) c.(Config.inlinings_opts);;
  const_rmps <- monad_map (fun '(kn, r) =>
    kn <- sanitize_kername f kn;;
    Ok (kn, r)
    ) c.(Config.const_remappings_opts);;
  ind_rmps <- monad_map (sanitize_remap_inductive f) c.(Config.ind_remappings_opts);;
  cstr_reorders <- monad_map (fun '(ind, s) =>
    ind <- sanitize_inductive f ind;;
    Ok (ind, s)
    ) c.(Config.cstr_reorders_opts);;
  cust_attrs <- monad_map (fun '(kn, s) =>
    kn <- sanitize_kername f kn;;
    Ok (kn, s)
    ) c.(Config.custom_attributes_opts);;

  Ok {|
    Config.backend_opts           := c.(Config.backend_opts);
    Config.erasure_opts           := c.(Config.erasure_opts);
    Config.inlinings_opts         := inls;
    Config.const_remappings_opts  := const_rmps;
    Config.ind_remappings_opts    := ind_rmps;
    Config.cstr_reorders_opts     := cstr_reorders;
    Config.custom_attributes_opts := cust_attrs;
  |}.
