(***************************************************)
(*                                                 *)
(*    Forward/Backward Tuple Analysis Iterator     *)
(*                                                 *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition
open Tuple
open ItoA

module TupleAnalysisIterator (B: TUPLE) =
struct

  module B = B

  let fwdInvMap = ref InvMap.empty
  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap
  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  module ExpMap = Map.Make(struct type t=bExp let compare=compare end)

  let assertExpMap = ref ExpMap.empty
  let addAssertInv (b:bExp) (a:B.t) = assertExpMap := ExpMap.add b a !assertExpMap
  let assertMap_print fmt m = ExpMap.iter (fun b a -> 
      Format.fprintf fmt "\nAssertion (%a): %a\n" bExp_print_aux b B.print_assert a) m


  (* Forward Iterator *)

  let rec fwdStm funcs env env_feat vars configs p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env vars configs
    | A_assign ((l,_),(e,_)) -> B.fwdAssign p (l,e)
    | A_assert (b,ba) -> (*B.filter p b*)
	      let p2' = (B.filter p b) in
      	  let p2 = B.filter p (fst (negBExp (b,ba))) in
		  addAssertInv b p2; p2'
		  (* if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) \n %a\n" bExp_print_aux b B.print_assert p2; p2') 
		  else (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; p2') *)	
    | A_if ((b,ba),s1,s2) ->
      let p1' = fwdBlk funcs env env_feat vars configs (B.filter p b) s1 in
      let p2 = B.filter p (fst (negBExp (b,ba))) in
      let p2' = fwdBlk funcs env env_feat vars configs p2 s2 in
      B.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) ->
	  let p1 = B.config_filter env_feat p b in 
      let p1' = fwdBlk funcs env env_feat vars configs p1 s1 in
      let p2 = B.config_filter_not env_feat p p1 in
      let p2' = fwdBlk funcs env env_feat vars configs p2 s2 in
      B.join p1' p2'	
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n =
        let i' = B.join p p2 in
        if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" B.print p;
          Format.fprintf !fmt "i: %a\n" B.print i;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "i': %a\n" B.print i'
        end;
        if B.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' else 
              B.widen i (B.join i i') in
          if !tracefwd && not !minimal then
            Format.fprintf !fmt "i'': %a\n" B.print i'';
          aux i'' (fwdBlk funcs env env_feat vars configs (B.filter i'' b) s) (n+1)
      in
      let i = B.bot env vars configs in
      let p2 = fwdBlk funcs env env_feat vars configs (B.filter i b) s in
      let p = aux i p2 1 in
	  let p_down = fwdBlk funcs env env_feat vars configs (B.filter p b) s in   (* this line is added additionally: performs narrowing  *)
	  (*Format.fprintf !fmt "Here = p: %a; p_down: %a\n" B.print p B.print p_down; *)
      addFwdInv l p_down; B.filter p_down (fst (negBExp (b,ba)))
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env env_feat vars configs p s) p ss in
      fwdBlk funcs env env_feat vars configs p f.funcBody
    | A_recall (f,ss) -> B.top env vars configs (* TODO *)

  and fwdBlk funcs env env_feat vars configs (p:B.t) (b:block) : B.t =
    let result_print l p =
      Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p
    in
    match b with
    | A_empty l ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; p
    | A_block (l,(s,_),b) ->
      if !tracefwd && not !minimal then result_print l p;
      addFwdInv l p; 
      fwdBlk funcs env env_feat vars configs (fwdStm funcs env env_feat vars configs p s) b


  (* Analyzer *)

let rec process list = 
	if List.length list = 0 then [[]]
	else match list with
		| [] -> []
		| hd :: tl -> 
			let tmp = ref [] in
			let dom = hd.featDom in
			for i = 0 to (List.length dom)-1 do
				let tmp1 = List.map (fun l -> (hd.featName,List.nth dom i) :: l) (process tl) in 
				tmp := !tmp @ tmp1
			done;
			!tmp;;
	
	(*let result = ref [] in 
	List.iter (fun hd -> List.iter (fun vl -> (Format.fprintf !fmt "%s{%d}" hd.featName vl); let tmp = List.map (fun I -> (hd.featName,vl)::I) !result) hd.featDom) lista; 
	!result;;*)
			
let print_configs l =
  print_endline ""; Format.fprintf !fmt "Configurations: ";
  List.iter (fun el -> print_endline ""; List.iter (fun (key,v) -> Format.fprintf !fmt "% s{%d}, " key v) el) l;;  			

(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main =
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars = List.append v1 v2 in
    let env = aux vars (Environment.make [||] [||]) in
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
	let list_feat = ref [] in
	let env_feat = ref (Environment.make [||] [||]) in 
	StringMap.iter (fun key value -> list_feat := value :: !list_feat; env_feat :=  Environment.add !env_feat [|(Var.of_string value.featId)|] [||]) !ItoA.features; 
	let list_configs = process !list_feat in print_configs list_configs;
	(*print_configs !list_configs;*) 
    let state = fwdBlk funcs env !env_feat vars list_configs (fwdBlk funcs env !env_feat vars list_configs (B.top env vars list_configs) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	  if (!assertExpMap != ExpMap.empty) then 
	  	begin
			Format.fprintf !fmt "\nAssertion Analysis:\n"; 
			assertMap_print !fmt !assertExpMap;
		end;
	  true

end
