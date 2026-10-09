(* Minimal JSON values and a compact, deterministic writer (object keys keep insertion order). *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Str of string
  | Arr of t list
  | Obj of (string * t) list

let escape buf s =
  Buffer.add_char buf '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | c when Char.code c < 0x20 -> Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.add_char buf '"'

let rec write buf = function
  | Null -> Buffer.add_string buf "null"
  | Bool b -> Buffer.add_string buf (if b then "true" else "false")
  | Int i -> Buffer.add_string buf (string_of_int i)
  | Str s -> escape buf s
  | Arr l ->
    Buffer.add_char buf '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char buf ','; write buf x) l;
    Buffer.add_char buf ']'
  | Obj l ->
    Buffer.add_char buf '{';
    List.iteri
      (fun i (k, v) -> if i > 0 then Buffer.add_char buf ','; escape buf k; Buffer.add_char buf ':'; write buf v)
      l;
    Buffer.add_char buf '}'

let to_string j =
  let buf = Buffer.create 4096 in
  write buf j;
  Buffer.contents buf

let opt f = function None -> Null | Some x -> f x
