{
open Parser

exception LexError of string

let keyword_table = Hashtbl.create 50
let () = List.iter (fun (k, v) -> Hashtbl.add keyword_table k v) [
  "module", MODULE;
  "where", WHERE;
  "open", OPEN;
  "import", IMPORT;
  "using", USING;
  "data", DATA;
  "record", RECORD;
  "field", FIELD;
  "let", LET;
  "in", IN;
  "case", CASE;
  "of", OF;
  "with", WITH;
  "infix", INFIX;
  "infixl", INFIXL;
  "infixr", INFIXR;
  "forall", FORALL;
  "Set", SET;
  "Prop", PROP;
  "refl", REFL;
  "fst", FST;
  "snd", SND;
  "inl", INL;
  "inr", INR;
]

let lookup_ident s =
  try Hashtbl.find keyword_table s
  with Not_found -> IDENT s

(* Layout state for indentation-sensitive parsing *)
type layout_state = {
  mutable pending_semi : bool;
  mutable last_line : int;
  mutable indent_col : int;
}

let state = {
  pending_semi = false;
  last_line = 1;
  indent_col = 0;
}

let reset_state () =
  state.pending_semi <- false;
  state.last_line <- 1;
  state.indent_col <- 0

(* Check if we should insert a semicolon before this token *)
let check_layout lexbuf =
  let pos = Lexing.lexeme_start_p lexbuf in
  let current_line = pos.Lexing.pos_lnum in
  let current_col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in

  if current_line > state.last_line && current_col <= state.indent_col then begin
    state.last_line <- current_line;
    state.indent_col <- current_col;
    true  (* Insert semicolon *)
  end else begin
    state.last_line <- current_line;
    if current_col > state.indent_col then
      state.indent_col <- current_col;
    false
  end

(* Mark that we've seen a token that can end a declaration *)
let can_end_decl = function
  | IDENT _ | RPAREN | RBRACE | RBRACKET | NUM _ | REFL | UNDERSCORE
  | TOP | BOT | SET | PROP | BBONE | BBZERO -> true
  | _ -> false
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let prime = '\''
let underscore = '_'
let ident_char = alpha | digit | underscore | prime

rule token = parse
  | white    { token lexbuf }
  | newline  { Lexing.new_line lexbuf; token lexbuf }
  | "--"     { line_comment lexbuf }
  | "{-"     { block_comment 1 lexbuf }

  (* Unicode symbols - must come before identifier rule *)
  | '\xce' '\xbb'              { LAMBDA }      (* λ *)
  | '\xe2' '\x88' '\x80'       { FORALL }      (* ∀ *)
  | '\xe2' '\x86' '\x92'       { ARROW }       (* → *)
  | '\xe2' '\x87' '\x92'       { DARROW }      (* ⇒ *)
  | '\xc3' '\x97'              { TIMES }       (* × *)
  | '\xe2' '\x8a' '\x8e'       { PLUS }        (* ⊎ *)
  | '\xe2' '\x8a' '\xa4'       { TOP }         (* ⊤ *)
  | '\xe2' '\x8a' '\xa5'       { BOT }         (* ⊥ *)
  | '\xc2' '\xb7'              { CDOT }        (* · *)
  | '\xc2' '\xac'              { NEG }         (* ¬ *)
  | '\xe2' '\x89' '\xa1'       { EQUIV }       (* ≡ *)
  | '\xe2' '\x89' '\xa4'       { LEQ }         (* ≤ *)
  | '\xe2' '\x8a' '\xa2'       { TURNSTILE }   (* ⊢ *)
  | '\xe2' '\x88' '\xb6'       { TYCOLON }     (* ∶ *)
  | '\xce' '\xa3'              { SIGMA }       (* Σ *)
  | '\xce' '\xa0'              { PI }          (* Π *)

  (* Blackboard bold - 4 bytes each *)
  | '\xf0' '\x9d' '\x9f' '\x98' { BBZERO }     (* 𝟘 *)
  | '\xf0' '\x9d' '\x9f' '\x99' { BBONE }      (* 𝟙 *)

  (* ASCII symbols *)
  | "->"     { ARROW }
  | "=>"     { DARROW }
  | "=="     { EQUIV }
  | "<="     { LEQ }
  | "|-"     { TURNSTILE }
  | "::"     { TYCOLON }
  | "+"      { PLUS }
  | "*"      { TIMES }
  | "="      { EQ }
  | ":"      { COLON }
  | ";"      { SEMI }
  | ","      { COMMA }
  | "."      { DOT }
  | "@"      { AT }
  | "|"      { BAR }
  | "\\"     { LAMBDA }
  | "("      { LPAREN }
  | ")"      { RPAREN }
  | "{"      { LBRACE }
  | "}"      { RBRACE }
  | "["      { LBRACKET }
  | "]"      { RBRACKET }
  | "_"      { UNDERSCORE }

  (* Numbers *)
  | digit+ as n { NUM (int_of_string n) }

  (* Unicode identifiers - Greek letters etc *)
  | ('\xce' ['\x91'-'\xbf'] | '\xcf' ['\x80'-'\x89'])
    (ident_char | '\xce' ['\x80'-'\xbf'] | '\xcf' ['\x80'-'\x89'] | '\xe2' ['\x80'-'\xbf'] ['\x80'-'\xbf'])* as s
    { lookup_ident s }

  (* Regular identifiers *)
  | (alpha | underscore) ident_char* as s
    { lookup_ident s }

  (* Operators like _+_ *)
  | underscore (alpha | digit | underscore | prime)+ underscore as s
    { OPERATOR s }

  | eof      { EOF }
  | _ as c   { raise (LexError (Printf.sprintf "Unexpected character: %c (0x%02x)" c (Char.code c))) }

and line_comment = parse
  | newline  { Lexing.new_line lexbuf; token lexbuf }
  | eof      { EOF }
  | _        { line_comment lexbuf }

and block_comment depth = parse
  | "{-"     { block_comment (depth + 1) lexbuf }
  | "-}"     { if depth = 1 then token lexbuf else block_comment (depth - 1) lexbuf }
  | newline  { Lexing.new_line lexbuf; block_comment depth lexbuf }
  | eof      { raise (LexError "Unterminated block comment") }
  | _        { block_comment depth lexbuf }
