module TestPrinters

open Microsoft.FSharp.Reflection

// Universal s-expression printers over extracted obj values.  The F#
// backend emits each source inductive as a real DU whose case ORDER
// follows the source declaration (Bool: false@0/true@1; Nat: zero@0,
// succ@1 with 1 field; List: nil@0, cons@1 with 2 fields).  We read
// case tags and fields via FSharp.Reflection, so the printers are
// independent of the generated type/constructor NAMES — they work for
// any frontend (rocq, agda, lean, ...).  Output format matches the
// OCaml backend's s-expressions, so expected_output[0] stays shared.

let private tagFields (o: obj) : int * obj[] =
  let case, fs = FSharpValue.GetUnionFields(o, o.GetType())
  case.Tag, fs

let pp_bool (o: obj) : string =
  match tagFields o with
  | 0, _ -> "false"
  | _ -> "true"

let rec pp_nat (o: obj) : string =
  match tagFields o with
  | 0, _ -> "O"
  | _, fs -> "(S " + pp_nat fs.[0] + ")"

let rec pp_list (ppA: obj -> string) (o: obj) : string =
  match tagFields o with
  | 0, _ -> "nil"
  | _, fs -> "(cons " + ppA fs.[0] + " " + pp_list ppA fs.[1] + ")"
