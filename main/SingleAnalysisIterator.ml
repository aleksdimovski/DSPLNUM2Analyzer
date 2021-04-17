(***************************************************)
(*                                                 *)
(*    Forward/Backward Single Analysis Iterator    *)
(*                                                 *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition

module SingleAnalysisIterator (B: PARTITION) =
struct

  module B = B

  let fwdInvMap = ref InvMap.empty

  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap

  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  module ExpMap = Map.Make(struct type t=bExp let compare=compare end)

  let assertUnreachMap = ref InvMap.empty
  let addAssertUnreachInv l (a:B.t) = assertUnreachMap := InvMap.add l a !assertUnreachMap
  
  let assertCorrectMap = ref InvMap.empty
  let addAssertCorrectInv l (a:B.t) = assertCorrectMap := InvMap.add l a !assertCorrectMap  
  
  let assertErrorMap = ref InvMap.empty
  let addAssertErrorInv l (a:B.t) = assertErrorMap := InvMap.add l a !assertErrorMap 

  let assertDontKnowMap = ref InvMap.empty
  let addAssertDontKnowInv l (a:B.t) = assertDontKnowMap := InvMap.add l a !assertDontKnowMap

  let assertMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "Assertion (%a) - after filter: %a\n" label_print l B.print a) m


  let errorAss = ref false 


  (* Forward Iterator *)

  let rec fwdStm funcs env vars p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env vars
    | A_assign ((l,_),(e,_)) -> B.fwdAssign p (l,e)
    | A_assert (b,ba) ->
	      let p2' = (B.filter p b) in
		  let b_neg = fst (negBExp (b,ba)) in 
      	  let p2 = B.filter p b_neg in
		  if ((not (B.isBot p)) && (B.isBot p2') && (B.isLeq p p2)) then errorAss:=true; 
		  (*Format.fprintf !fmt "\n ASSERT (%a) before (%a) \n after - %a \n" bExp_print_aux b B.print p B.print p2';*)
		  (*addAssertInv b p2;*) p2'
    | A_if ((b,ba),s1,s2) ->
	  let p1 = B.filter p b in 
      let p1' = fwdBlk funcs env vars p1 s1 in
      let p2 = B.filter p (fst (negBExp (b,ba))) in
      let p2' = fwdBlk funcs env vars p2 s2 in 
	  (*Format.fprintf !fmt "\n filter(%a,%a) p1 = (%a), p1' = (%a), p2 = (%a), p2' = (%a):\n" B.print p bExp_print_aux b B.print p1 B.print p1' B.print p2 B.print p2';*)
      B.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) -> p  
    | A_while (l,(b,ba),s) ->
	  let p_in = p in 
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
          aux i'' (fwdBlk funcs env vars (B.filter i'' b) s) (n+1)
      in
      let i = B.bot env vars in
      let p2 = fwdBlk funcs env vars (B.filter i b) s in
      let p = aux i p2 1 in 
	  let p_down = fwdBlk funcs env vars (B.filter p b) s in 
	  let notb = fst (negBExp (b,ba)) in 
      addFwdInv l p_down; B.join (B.filter p_in notb) (B.filter p_down notb)
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env vars p s) p ss in
      fwdBlk funcs env vars p f.funcBody
    | A_recall (f,ss) -> B.top env vars (* TODO *)

  and fwdBlk funcs env vars (p:B.t) (b:block) : B.t =
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
	  match s with 
	  | A_assert (bb,bba) -> let p'= fwdStm funcs env vars p s in 
	  						(if (B.isBot p) then addAssertUnreachInv l p'
							 else (if (!errorAss) then (addAssertErrorInv l p'; errorAss := false)
									else (if (B.isLeq p p') then addAssertCorrectInv l p'
									else addAssertDontKnowInv l p')));
							fwdBlk funcs env vars p' b
	  | _ -> fwdBlk funcs env vars (fwdStm funcs env vars p s) b


  (* Analyzer *)


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
    let state = fwdBlk funcs env vars (fwdBlk funcs env vars (B.top env vars) stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\nForward Analysis:\n";
        fwdMap_print !fmt !fwdInvMap;
      end;
	(*if (!assertExpMap != ExpMap.empty) then *)
	  begin
			Format.fprintf !fmt "\nAssertion Analysis: \n"; 
			Format.fprintf !fmt "\nUnreachable Assertions: total=%d\n" (InvMap.cardinal !assertUnreachMap); 
			assertMap_print !fmt !assertUnreachMap;
			Format.fprintf !fmt "\nCorrect Assertions: total=%d\n" (InvMap.cardinal !assertCorrectMap); 
			assertMap_print !fmt !assertCorrectMap;		
			Format.fprintf !fmt "\nError Assertions: total=%d\n" (InvMap.cardinal !assertErrorMap);  
			assertMap_print !fmt !assertErrorMap;				
			Format.fprintf !fmt "\nDon't Know Assertions: total=%d\n" (InvMap.cardinal !assertDontKnowMap);  
			assertMap_print !fmt !assertDontKnowMap;			
	  end;  
	  true

end
