
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode cl = String.concat "" (List.map (String.make 1) cl)


type stackVal =
INT of int
| STR of string
| BOOL of bool
| NAME of string
| ERROR
| UNIT
| CLOSURE of (stackVal * (command list) * (stackVal * stackVal) list list)
| IOCLOSURE of (stackVal * (command list) * (stackVal * stackVal) list list)
and command =
  ADD | SUB | MUL | DIV | REM | SWAP | POP | NEG | PUSH of stackVal | QUIT 
  | AND | OR | NOT | IF | EQUAL | LESSTHAN | CAT | BIND | LET | END 
  | FUN of stackVal * stackVal | INOUTFUN of stackVal * stackVal | FUNEND 
  | RETURN | IO of stackVal * stackVal |RETURN_IO of stackVal * stackVal | CALL (* function specific commands *)

exception Impossible of string

let rec toString(x : stackVal) : string =
  match x with
      INT(i) -> if i < 0 then "-"^string_of_int(-i) else string_of_int(i)
    | STR(s)  -> s
    | BOOL(b) -> ":"^string_of_bool(b)^":"
    | NAME(n) -> n
    | ERROR   -> ":error:"
    | UNIT    -> ":unit:"
    | CLOSURE _ -> "CLOSURE"
    | IOCLOSURE _ -> "IOCLOSURE"


let svTy sv =
  match sv with
    INT _ -> "INT"
  | STR _ -> "STR"
  | NAME _ -> "NAME"
  | BOOL _ -> "BOOL"
  | ERROR -> "ERROR"
  | UNIT -> "UNIT"
  | CLOSURE _ -> "CLOSURE"
  | IOCLOSURE _ -> "IOCLOSURE"

let comtoString (x) =
  match x with
    ADD         -> "ADD"
  | SUB         -> "SUB"
  | MUL         -> "MUL"
  | DIV         -> "DIV"
  | REM         -> "REM"
  | SWAP        -> "SWAP"
  | POP         -> "POP"
  | NEG         -> "NEG"
  | PUSH(s)     -> "PUSH " ^ toString(s)
  | QUIT        -> "QUIT"
  | RETURN      -> "RETURN"
  | CALL        -> "CALL"
  | IF          -> "IF"
  | EQUAL       -> "EQUAL"
  | LESSTHAN    -> "LESSTHAN"
  | CAT         -> "CAT"
  | BIND        -> "BIND"
  | LET         -> "LET"
  | END         -> "END"
  | FUNEND      -> "FUNEND"
  | IO _        -> "IO"
  | RETURN_IO _ -> "RETURN_IO"
  | FUN _       -> "FUN DECL"
  | AND         -> "AND"
  | OR          -> "OR"
  | NOT         -> "NOT"
  | INOUTFUN _  -> "INOUTFUN DECL"

(*************************************************************************************************)
(* BIND LOOKUP *)
(*************************************************************************************************)

let rec eval ((a : stackVal),(b : (stackVal * stackVal) list list)) : stackVal =
  match (a,b) with
    (NAME(x), environment) ->
    (
    match environment with
      ((NAME(y), value)::bs)::bss -> if y = x then value else eval(NAME(x), bs::bss)
    | ((inletid, _)::bs)::bss  -> ERROR
    | []::bss -> eval(NAME(x),bss)
    | [] -> ERROR
    )
    | _ -> ERROR

(*************************************************************************************************)
(* PARSING INPUT *)
(*************************************************************************************************)

let digits = explode "0123456789"
let alpha = explode "_ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
let alphanum = alpha @ digits

let stripnewline (s : string) : string =
    let rec strip (chs : char list) : char list =
      match chs with
        '\n'::cs -> strip(cs)
      | c::cs     -> c::strip(cs)
      | []        -> []
    in
      implode(strip(explode s))

let stripQuotes(s : string) : string =
  let stripHead (chs : char list) : char list =
      match chs with
        '\"'::xs -> xs
      | z         -> z
    in
    let rec stripTail (chs : char list) : char list =
      match chs with
        '\"'::[] -> []
      | c::cs     -> c::stripTail(cs)
      | []        -> []
  in
    implode(stripTail(stripHead(explode s)))


let rec checkCh ((set : char list), (ch : char)) : bool =
  match set with
    s::rest -> if s = ch then true else checkCh (rest, ch)
  | []    -> false

let rec checkChs ((set : char list), (chs : char list)) : bool =
  match chs with
    c::cs -> if checkCh(set, c) then checkChs(set, cs) else false
  | []    -> true

let rec stripLeadingWhitespace s =
  match s with
    ' '::x::xs  -> if checkCh(alphanum, x) then
	                  implode(x::xs)
				    else stripLeadingWhitespace(x::xs)
  | '\t'::x::xs -> if checkCh(alphanum, x) then
                      implode(x::xs)
					else stripLeadingWhitespace(x::xs)
  | x -> implode s

let parseInt str sign : stackVal =
  if checkChs(digits, explode str) then
    INT((int_of_string str) * sign)
  else ERROR

let parseName str : stackVal =
  match (explode str) with
    x::xs -> if checkCh(alpha, x) then
	           if checkChs(alphanum, xs) then
			       NAME(str)
			     else ERROR
			   else ERROR
   | _    -> ERROR

let parseBoolError (s : string) : stackVal = match explode(s) with
      (':')::('t')::cs -> BOOL(true)
    | (':')::('f')::cs -> BOOL(false)
    | (':')::('e')::cs -> ERROR
    | _              -> ERROR

let parseLiteral(s : string) : stackVal =
    match explode(s) with
        '-'::cs -> (parseInt (implode cs) (-1))
        | '\"'::cs -> STR(stripQuotes s)
        | ':'::cs  -> parseBoolError s
        | c::cs -> if checkCh(digits, c) then parseInt s 1 else parseName(s)
        | _ -> ERROR

(*************************************************************************************************)
(* FUNCTION PARSING *)
(*************************************************************************************************)
let rec removeFunStrings((strs : string list), n) =
  match (strs,n) with
      ("funEnd"::xs,0) -> xs
    | ("funEnd"::xs,z) -> removeFunStrings(xs, z-1)
    | (x::xs,_) -> removeFunStrings (xs,n)
    | _ -> []

    (* Modifies an inOutFun's last command to contain the name of the formal parameter and the name
     * of the argument it was passed.  That way, at the end of the execution we can easily look up
	 * the FP's binding and bind it to the argument at the call site.
	 *)
let rec bindReturn((commands : command list), (formalParameter : stackVal), (args : stackVal option))=
  match (commands, formalParameter, args) with
    (commands, formalParameter, Some arg) ->
  (
    match commands with
      RETURN::[] -> RETURN_IO(formalParameter, arg)::[]
    | []         -> IO(formalParameter, arg)::[]
    | x::xs      -> x::bindReturn(xs, formalParameter, Some arg)
    )
  | (c, _, _) -> c
(*************************************************************************************************)
(* PARSE STRINGS INTO command LIST *)
(*************************************************************************************************)
let rec parsecommands (l : string list) : (command list) =
  match l with
    |[] -> []
    | s::rest ->
        let tokens = String.split_on_char ' ' s (* creates a string list from the line of input, where each element was separated by a space *)
        in
        match tokens with
          "push"::xs     -> PUSH(parseLiteral (String.sub s 5 ((String.length(s) - 5))))::(parsecommands rest)
        | "add"::xs      -> ADD:: (parsecommands rest)
        | "sub"::xs      -> SUB::parsecommands rest
        | "mul"::xs      -> MUL::parsecommands rest
        | "div"::xs      -> DIV::parsecommands rest
        | "rem"::xs      -> REM::parsecommands rest
        | "swap"::xs     -> SWAP::parsecommands rest
        | "pop"::xs      -> POP::parsecommands rest
        | ":false:"::xs  -> PUSH(BOOL false)::parsecommands rest
        | ":true:"::xs   -> PUSH(BOOL true)::parsecommands rest
        | ":error:"::xs  -> PUSH (ERROR) :: parsecommands rest
        | "neg"::xs      -> NEG::parsecommands rest
        | "and"::xs      -> AND::parsecommands rest
        | "or"::xs       -> OR::parsecommands rest
        | "not"::xs      -> NOT::parsecommands rest
        | "if"::xs       -> IF::parsecommands rest
        | "equal"::xs    -> EQUAL::parsecommands rest
        | "lessThan"::xs -> LESSTHAN::parsecommands rest
        | "bind"::xs     -> BIND::parsecommands rest
        | "let"::xs      -> LET::parsecommands rest
        | "end"::xs      -> END::parsecommands rest
        | "call"::xs     -> CALL::parsecommands rest
        | "return"::xs   -> RETURN::parsecommands rest
        | "quit"::xs     -> QUIT::parsecommands rest
        | "fun"::funName::arg::xs -> FUN(parseLiteral funName, parseLiteral arg)::parsecommands rest
        | "inOutFun"::funName::arg::xs -> INOUTFUN(parseLiteral funName , parseLiteral arg)::parsecommands rest
        | "funEnd"::xs   -> FUNEND::parsecommands rest
        | "cat"::xs      -> CAT::parsecommands rest
        | ""::xs         -> parsecommands rest
        | x::xs          -> PUSH (ERROR) :: parsecommands rest
		    | _ -> []

(*************************************************************************************************)
(* PART 1 - ARITHMETIC & STACK MANIPULATION FUNCTIONS *)
(*************************************************************************************************)
let callPop (stk : stackVal list) =
  match stk with
    (s::t) -> t
  | _  -> ERROR::stk

let callSwap (stk : stackVal list) =
  match stk with
    (s1::s2::stk) -> s2::s1::stk
    | _             -> ERROR::stk

let callAdd (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::INT(y)::stk, bindings) -> INT(x+y)::stk
  | (INT(x)::NAME(y)::stk, bindings) ->
   (
      match eval(NAME y, bindings) with
        INT z -> INT(x+z)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk
        )
  | (NAME(x)::INT(y)::stk, bindings) ->
   (
      match eval(NAME x, bindings) with
        INT z -> INT(y+z)::stk
        | _    -> ERROR::NAME(x)::INT(y)::stk
        )
  | (NAME(x)::NAME(y)::stk, bindings) ->
   (
      match (eval(NAME x, bindings), eval(NAME(y), bindings)) with
        (INT z, INT z') -> INT(z+z')::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk
        )
  | (stk, bindings) -> ERROR::stk

let callSub (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::INT(y)::stk, bindings) -> INT(y-x)::stk
  | (INT(x)::NAME(y)::stk, bindings) ->
  (
      match eval(NAME y, bindings) with
        INT z -> INT(z-x)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk
        )

  | (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        INT z -> INT(y-z)::stk
        | _    -> ERROR::NAME(x)::INT(y)::stk)
  | (NAME(x)::NAME(y)::stk, bindings) ->
  (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (INT z, INT z') -> INT(z'-z)::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk
        )
  | (stk, bindings) -> ERROR::stk

let callMul (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::INT(y)::stk, bindings) -> INT(x*y)::stk
  |  (INT(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        INT z -> INT(x*z)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk)
  |  (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        INT z -> INT(y*z)::stk
        | _    -> ERROR::NAME(x)::INT(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (INT z, INT z') -> INT(z*z')::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callDiv (stk,bindings) =
  match (stk,bindings) with
    (INT(0)::stk, bindings) -> ERROR::INT(0)::stk
  |  (INT(x)::INT(y)::stk, bindings) -> INT(y / x)::stk
  |  (INT(x)::NAME(y)::stk, bindings) ->
  (
      match eval(NAME y, bindings) with
        INT z -> INT(z / x)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk
        )
  |  (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
          INT 0 -> ERROR::NAME(x)::INT(y)::stk
        | INT z -> INT(y / z)::stk
        | _    -> ERROR::NAME(x)::INT(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
          (INT 0, INT z') -> ERROR::NAME(x)::NAME(y)::stk
        | (INT z, INT z') -> INT(z' / z)::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callRem (stk,bindings) =
  match (stk,bindings) with
    (INT(0)::stk, bindings) -> ERROR::INT(0)::stk
  |  (INT(x)::INT(y)::stk, bindings) -> INT(y mod x)::stk
  |  (INT(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        INT(z) -> INT(z mod x)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk)
  |  (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
          INT 0 -> ERROR::NAME(x)::INT(y)::stk
        | INT z -> INT(y mod z)::stk
        | _      -> ERROR::NAME(x)::INT(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
          (INT 0, INT z') -> ERROR::NAME(x)::NAME(y)::stk
        | (INT z, INT z') -> INT(z' mod z)::stk
        | _                 -> ERROR::NAME(x)::NAME(y)::stk)
  | (stk, bindings) -> ERROR::stk

let callNeg (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::stk, bindings) -> INT(-x)::stk
  |  (NAME(x)::stk, bindings) -> (match eval(NAME(x), bindings) with
        INT z -> INT(-z)::stk
        | _    -> ERROR::NAME(x)::stk)
  |  (stk, bindings) -> ERROR::stk

(*************************************************************************************************)
(* PART 2 - LOGICAL/STRING FUNCTIONS, VARIABLES & SCOPING *)
(*************************************************************************************************)

let callAnd (stk,bindings) =
  match (stk,bindings) with
    (BOOL(x)::BOOL(y)::stk, bindings) -> BOOL(x && y)::stk
  |  (BOOL(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        BOOL z -> BOOL(x && z)::stk
        | _    -> ERROR::BOOL(x)::NAME(y)::stk)
  |  (NAME(x)::BOOL(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        BOOL z -> BOOL(y && z)::stk
        | _    -> ERROR::NAME(x)::BOOL(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (BOOL z, BOOL z') -> BOOL(z && z')::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callOr (stk,bindings) =
  match (stk,bindings) with
    (BOOL(x)::BOOL(y)::stk, bindings) -> BOOL(x || y)::stk
  |  (BOOL(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        BOOL z -> BOOL(x || z)::stk
        | _    -> ERROR::BOOL(x)::NAME(y)::stk)
  |  (NAME(x)::BOOL(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        BOOL z -> BOOL(y || z)::stk
        | _    -> ERROR::NAME(x)::BOOL(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (BOOL z, BOOL z') -> BOOL(z || z')::stk
        | _               -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callEqual (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::INT(y)::stk, bindings) -> BOOL(x=y)::stk
  |  (INT(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        INT z -> BOOL(x=z)::stk
        | _   -> ERROR::INT(x)::NAME(y)::stk)
  |  (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        INT z -> BOOL(y=z)::stk
        | _   -> ERROR::NAME(x)::INT(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (match (eval(NAME(x), bindings), eval(NAME(y), bindings)) with
        (INT z, INT z') -> BOOL(z=z')::stk
        | _             -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callLessThan (stk,bindings) =
  match (stk,bindings) with
    (INT(x)::INT(y)::stk, bindings) -> BOOL(y < x)::stk
  |  (INT(x)::NAME(y)::stk, bindings) -> (
      match eval(NAME y, bindings) with
        INT z  -> BOOL(z < x)::stk
        | _    -> ERROR::INT(x)::NAME(y)::stk)
  |  (NAME(x)::INT(y)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        INT z  -> BOOL(y < z)::stk
        | _    -> ERROR::NAME(x)::INT(y)::stk)
  |  (NAME(x)::NAME(y)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (INT z, INT z') -> BOOL(z' < z)::stk
        | _             -> ERROR::NAME(x)::NAME(y)::stk)
  |  (stk, bindings) -> ERROR::stk

let callIf (stk,bindings) =
  match (stk,bindings) with
    (x::y::BOOL(z)::stk, bindings) -> (
      match z with
        true  -> x::stk
      | false -> y::stk)
  |  (x::y::NAME(z)::stk, bindings) -> (
      match eval(NAME z, bindings) with
        BOOL true  -> x::stk
      | BOOL false -> y::stk
      | _           -> ERROR::x::y::NAME(z)::stk)
  |  (stk, bindings) -> ERROR::stk

let callNot (stk,bindings) =
  match (stk,bindings) with
    (BOOL(x)::stk, bindings) -> BOOL(not x)::stk
  |  (NAME(x)::stk, bindings) -> (
      match eval(NAME x, bindings) with
        BOOL z -> BOOL(not z)::stk
        | _    -> ERROR::NAME(x)::stk)
  |  (stk, bindings) -> ERROR::stk

let callCat (stk,bindings) =
  match (stk,bindings) with
    (STR(s2)::STR(s1)::stk, bindings) -> STR(s1^s2)::stk
  |  (NAME(x)::STR(s1)::stk, bindings) -> (
      match eval(NAME x, bindings) with
            STR s2 -> STR(s1^s2)::stk
          | _ -> ERROR::NAME(x)::STR(s1)::stk)
  |  (STR(s2)::NAME(x)::stk, bindings) -> (
      match eval(NAME x, bindings) with
            STR s1 -> STR(s1^s2)::stk
          | _ -> ERROR::STR(s2)::NAME(x)::stk)
  |  (NAME(y)::NAME(x)::stk, bindings) -> (
      match (eval(NAME x, bindings), eval(NAME y, bindings)) with
        (STR s1, STR s2) -> STR(s1^s2)::stk
      | _ -> ERROR::NAME(y)::NAME(x)::stk)
  |  (stk, bindings) -> ERROR::stk

let callBind (stk,bindings) =
  match (stk,bindings) with
    (ERROR::stk, currentScope::bindings) -> (ERROR::ERROR::stk, currentScope::bindings)
  | (NAME(x)::NAME(y)::stk, currentScope::bindings) -> (
      match eval(NAME x, currentScope::bindings) with
          ERROR -> (ERROR::NAME(x)::NAME(y)::stk, currentScope::bindings)
        | z     -> (UNIT::stk, ((NAME y, z)::currentScope)::bindings))
  | (x::NAME(y)::stk, currentScope::bindings) -> (UNIT::stk, ((NAME y, x)::currentScope)::bindings)
  | (stk, bindings) -> (ERROR::stk, bindings)

let callEnd (c, stk,bindings) =
  match (c, stk,bindings) with
    (c, (s::stack1)::stack2::stacks, (old::headBinds)::restBinds) -> (c, (s::stack2)::stacks, headBinds::restBinds)
  | (c, stack::stacks, (old::headBinds)::restBinds) -> (c, stacks, headBinds::restBinds)
  | (c,s,b) -> (c,s,b)

(*************************************************************************************************)
(* PART 3 - FUNCTIONS *)
(*************************************************************************************************)

let parseFunction (comm, st, tops) =
  match (comm, st, tops) with
  ((c::comms)::rest, stk::stks, (top::b)::bl) ->

  let rec parser(comms, n) =
      match (comms, n) with
        (FUNEND::cs,0)           -> []
      | (FUNEND::cs,_)           -> FUNEND::parser(cs, n-1)
      | (FUN(name,f)::cs,_)      -> FUN(name,f)::parser(cs, n+1)
      (*| (INOUTFUN(name,f)::cs,_) -> INOUTFUN(name,f)::parser(cs, n+1)*)
      | (x::cs,_)                -> x::parser(cs, n)
	    | _                        -> []
      in
    let rec getRest (comms, n) =
      (
        match (comms, n) with
              (FUNEND::cs,0)      -> cs
            | (FUNEND::cs,_)      -> getRest(cs, n-1)
            | (FUN(_)::cs,_)      -> getRest(cs, n+1)
            | (INOUTFUN(_)::cs,_) -> getRest(cs, n+1)
            | (x::cs,_)           -> getRest(cs, n)
            | _                   -> []
            )
    in
      (
        match c with
        FUN(funName, fp)      -> (getRest(comms, 0)::rest, (UNIT::stk)::stks, (((funName, (CLOSURE(fp, parser(comms, 0), top::b)))::top)::b)::bl)
      | INOUTFUN(funName, fp) -> (getRest(comms, 0)::rest, (UNIT::stk)::stks, (((funName, (IOCLOSURE(fp, parser(comms, 0), top::b)))::top)::b)::bl)
	    | _                     -> (print_endline("This should not have happened :("); raise (Impossible "Impossible raised in parseFunction\n"))
        )
   | _ -> (print_endline("This should not have happened :("); raise (Impossible "Impossible raised in parseFunction\n"))


let call (commands, st, b) =
  match (commands, st, b) with
  (commands, (ERROR::stk)::stks, b) -> (commands, (ERROR::ERROR::stk)::stks, b)
  |(commands, (NAME(arg)::NAME(funName)::stk)::stks, bindings::b) ->
  (
      match (eval(NAME(arg), bindings), eval(NAME(funName), bindings)) with
        (ERROR, _) -> (commands, (ERROR::NAME(arg)::NAME(funName)::stk)::stks, bindings::b)
      | (x, CLOSURE(fp, comms, e::env)) ->
      let c = comms::commands in
		  let stack = []::stk::stks in
		  let newEnv = ((((fp,x)::e)::env)@[[(NAME(funName), CLOSURE(fp, comms, e::env))]])::bindings::b
		  in (c,stack,newEnv)
      | (x, IOCLOSURE(fp, comms, e::env)) ->
		  let c    = bindReturn(comms, fp, Some (NAME (arg)))::commands in
        let stack  = []::stk::stks in
          let newEnv = ((((fp,x)::e)::env)@[[(NAME(funName),IOCLOSURE(fp, comms, e::env))]])::bindings::b
          in
            (c,stack,newEnv)
      | _ -> (commands, (ERROR::NAME(arg)::NAME(funName)::stk)::stks, bindings::b)
  )

  | (commands, (x::NAME(funName)::stk)::stks, bindings::b) ->
  (
      match eval(NAME(funName), bindings) with
        ERROR -> (commands, (ERROR::x::NAME(funName)::stk)::stks, bindings::b)
      | CLOSURE(arg, comms, e::env)   ->
            let c = (comms::commands) in
              let stack = []::stk::stks in
                let newEnv = ((((arg,x)::e)::env)@[[(NAME(funName),CLOSURE(arg, comms, e::env))]])::bindings::b
                in
                  (c,stack,newEnv)
      | IOCLOSURE(arg, comms, e::env) ->
            let c = bindReturn(comms, arg, Some x)::commands in
              let stack = []::stk::stks in
                let newEnv = ((((arg,x)::e)::env)@[[(NAME(funName),IOCLOSURE(arg, comms, e::env))]])::bindings::b
                in
                  (c,stack,newEnv)
      | _ -> (commands, (ERROR::x::NAME(funName)::stk)::stks, bindings::b)
      )

  | (commands, (NAME(arg)::CLOSURE(fp, comms, e::env)::stk)::stks, bindings::b) ->
   (
      match eval(NAME arg, bindings) with
        ERROR -> (commands, (ERROR::NAME(arg)::CLOSURE(fp, comms, e::env)::stk)::stks, bindings::b)
      | x     -> (comms::commands, []::stk::stks, (((fp,x)::e)::env)::bindings::b)
      )
  | (commands, (x::CLOSURE(fp, comms, e::env)::stk)::stks, bindings::b) -> (comms::commands, []::stk::stks, (((fp,x)::e)::env)::bindings::b)

  | (commands, (NAME(arg)::IOCLOSURE(fp, comms, e::env)::stk)::stks, bindings::b) ->
   (
      match eval(NAME arg, bindings) with
        ERROR -> (commands, (ERROR::NAME(arg)::IOCLOSURE(fp, comms, e::env)::stk)::stks, bindings::b)
      | x     ->
          let c = bindReturn(comms, fp, Some (NAME (arg)))::commands in
            let stack = []::stk::stks in
              let newEnv = (((fp,x)::e)::env)::bindings::b
              in
                (c,stack,newEnv)
          )
  |  (commands, (x::IOCLOSURE(fp, comms, e::env)::stk)::stks, bindings::b) -> (comms::commands, []::stk::stks, (((fp,x)::e)::env)::bindings::b)

  |  (commands, stk::stks, b) -> (commands, (ERROR::stk)::stks, b)
  |  (commands, [], b) -> (commands, [[ERROR]], b) (* This should never happen *)


let functionReturn (commands, stacks, bindings) =
  match (commands, stacks, bindings) with
    (comms::rest, (s::stk)::stk2::stks, funBinds::b) ->
  (
    match eval(s, funBinds) with
      ERROR -> (rest, (s::stk2)::stks, b)
    | x     -> (rest, (x::stk2)::stks, b)
    )
  | (comms::rest, stk::stk2::stks, funBinds::b) -> (rest, stk2::stks, b)
  | _ -> (print_endline("This should not have happened :(\n"); raise (Impossible "Impossible raised in functionReturn\n"))


let functionIOReturn (commands, stacks, bindings, para, arg) =
  match (commands, stacks, bindings, para, arg) with
  (comms::rest, (s::stk)::stk2::stks, (funBinds)::(topBinds::nextBinds)::b, formalparameter, argument) ->

    (
      match (eval(formalparameter, funBinds), argument, eval(s,funBinds)) with
        (ERROR, _, ERROR)   -> (rest, (s::stk2)::stks, (topBinds::nextBinds)::b)
      | (ERROR, _, x)       -> (rest, (x::stk2)::stks, (topBinds::nextBinds)::b)
      | (z, NAME(y), ERROR) -> (rest, (s::stk2)::stks, (((NAME y,z)::topBinds)::nextBinds)::b)
      | (z, NAME(y), x)     -> (rest, (x::stk2)::stks, (((NAME y,z)::topBinds)::nextBinds)::b)
      | (_, _, ERROR)       -> (rest, (s::stk2)::stks, (topBinds::nextBinds)::b)
      | (_, _, x)           -> (rest, (x::stk2)::stks, (topBinds::nextBinds)::b)
      )
  | _ -> (print_endline("This should not have happened :(\n"); raise (Impossible "Impossible raised in functionIOReturn\n"))

let functionIO (commands, stacks, bindings, para, arg) =
  match (commands, stacks, bindings, para, arg) with
  (comms::rest, stk::stks, (funBinds)::(topBinds::nextBinds)::b, formalparameter, argument) ->
    (
      match (eval(formalparameter, funBinds), argument) with
        (ERROR, _)   -> (rest, stks, (topBinds::nextBinds)::b)
      | (x, NAME(y)) -> (rest, stks, (((NAME y,x)::topBinds)::nextBinds)::b)
      | (_, _)       -> (rest, stks, (topBinds::nextBinds)::b)
      )
  | _ -> (print_endline("This should not have happened :(\n"); raise (Impossible "Impossible raised in functionIO\n"))

(*************************************************************************************************)
(* DRIVER FUNCTIONS *)
(*************************************************************************************************)

let rec interpret ((com : command list list),(stk: stackVal list list), (bindings: (stackVal * stackVal) list list list)): stackVal list =
  match (com,stk,bindings) with
  ((c::comms)::rest , stack::stacks , mainBinds::b )  ->
  (
    match c with
    PUSH(x)  -> interpret(comms::rest, (x::stack)::stacks, mainBinds::b)
  | ADD      -> interpret(comms::rest, callAdd(stack, mainBinds)::stacks, mainBinds::b)
  | SUB      -> interpret(comms::rest, callSub(stack, mainBinds)::stacks, mainBinds::b)
  | MUL      -> interpret(comms::rest, callMul(stack, mainBinds)::stacks, mainBinds::b)
  | DIV      -> interpret(comms::rest, callDiv(stack, mainBinds)::stacks, mainBinds::b)
  | REM      -> interpret(comms::rest, callRem(stack, mainBinds)::stacks, mainBinds::b)
  | SWAP     -> interpret(comms::rest, callSwap(stack)::stacks, mainBinds::b)
  | POP      -> interpret(comms::rest, callPop(stack)::stacks, mainBinds::b)
  | NEG      -> interpret(comms::rest, callNeg(stack, mainBinds)::stacks, mainBinds::b)
  | AND      -> interpret(comms::rest, callAnd(stack, mainBinds)::stacks, mainBinds::b)
  | OR       -> interpret(comms::rest, callOr(stack, mainBinds)::stacks, mainBinds::b)
  | NOT      -> interpret(comms::rest, callNot(stack, mainBinds)::stacks, mainBinds::b)
  | IF       -> interpret(comms::rest, callIf(stack, mainBinds)::stacks, mainBinds::b)
  | EQUAL    -> interpret(comms::rest, callEqual(stack, mainBinds)::stacks, mainBinds::b)
  | LESSTHAN -> interpret(comms::rest, callLessThan(stack, mainBinds)::stacks, mainBinds::b)
  | CAT      -> interpret(comms::rest, callCat(stack, mainBinds)::stacks, mainBinds::b)
  | BIND     -> (match callBind(stack, mainBinds) with
                        (newStack, newBinds) -> interpret(comms::rest, newStack::stacks, newBinds::b))
  | LET      -> interpret(comms::rest, []::stack::stacks, ([]::mainBinds)::b)
  | END      -> interpret (callEnd(comms::rest, stack::stacks, mainBinds::b))
  | FUN _      -> interpret(parseFunction((c::comms)::rest, stack::stacks, mainBinds::b))
  | INOUTFUN _ -> interpret(parseFunction((c::comms)::rest, stack::stacks, mainBinds::b))
  | RETURN     -> interpret(functionReturn(comms::rest, stack::stacks, mainBinds::b))
  | CALL       -> interpret(call(comms::rest, stack::stacks, mainBinds::b))
  | RETURN_IO(p,a) -> interpret(functionIOReturn(comms::rest, stack::stacks, mainBinds::b, p, a))
  | IO(p,a)        -> interpret(functionIO(comms::rest, stack::stacks, mainBinds::b, p, a))
  | QUIT               -> stack
  | _                  -> []
  )
  | _ -> (print_endline("This was not supposed to happen :(\n"); raise (Impossible ("Impossible raised at interpret, check initial arguments\n")))


(*************************************************************************************************)
(* WRITING AND READING HELPER FUNCTIONS *)
(*************************************************************************************************)

let read_lines inc =
  let rec loop_read acc =
    try
      let l=input_line inc in
      loop_read (l::acc)
    with
      | End_of_file -> List.rev acc
  in
    loop_read []

let rec write_all l oc=
   match l with
     | [] -> ()
     | hd::tl ->
             let () =Printf.fprintf oc "%s\n" hd  in
             write_all tl oc


(*************************************************************************************************)
(* INTERPRETER FUNCTION *)
(*************************************************************************************************)
let interpreter ((inputFile : string), (outputFile : string)) =
  let ic = open_in inputFile in
    let oc = open_out outputFile in
      let inList = read_lines ic in
        let commands = parsecommands(inList) in
          let finalStack = (interpret([commands], [[]], [[[]]])) in
	           let stringList = List.map toString finalStack in
                let _ = write_all stringList oc in
                  let _= close_in ic in
                    let _= close_out oc in ()

let _ = interpreter("read.txt", "testout.txt")
