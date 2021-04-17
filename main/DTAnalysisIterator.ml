(***************************************************)
(*                                                 *)
(*    Forward/Backward DT Analysis Iterator        *)
(*                                                 *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition
open DTDomain
open ItoA

module DTAnalysisIterator (B: DTDomain) =
struct

  module B = B
  module P = B.P

  let fwdInvMap = ref InvMap.empty
  let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap
  let fwdMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "%a: %a\n" label_print l B.print a) m

  module ExpMap = Map.Make(struct type t=bExp let compare=compare end)

  let assertExpMap = ref ExpMap.empty
  let addAssertInv (b:bExp) (a:B.t) = assertExpMap := ExpMap.add b a !assertExpMap
  let assertMap_print fmt m = ExpMap.iter (fun b a -> 
      Format.fprintf fmt "\nAssertion (%a): %a\n" bExp_print_aux b B.print a) m
	  

  let assertUnreachMap = ref InvMap.empty
  let addAssertUnreachInv l (a:B.t) = assertUnreachMap := InvMap.add l a !assertUnreachMap
  
  let assertCorrectMap = ref InvMap.empty
  let addAssertCorrectInv l (a:B.t) = assertCorrectMap := InvMap.add l a !assertCorrectMap  
  
  let assertErrorMap = ref InvMap.empty
  let addAssertErrorInv l (a:B.t) = assertErrorMap := InvMap.add l a !assertErrorMap 

  let assertDontKnowMap = ref InvMap.empty
  let addAssertDontKnowInv l (a:B.t) = assertDontKnowMap := InvMap.add l a !assertDontKnowMap
  
  let assertMixed1Map = ref InvMap.empty
  let addAssertMixed1Inv l (a:B.t) = assertMixed1Map := InvMap.add l a !assertMixed1Map
  
  let assertMixed2Map = ref InvMap.empty
  let addAssertMixed2Inv l (a:B.t) = assertMixed2Map := InvMap.add l a !assertMixed2Map
  
  let assertMixed3Map = ref InvMap.empty
  let addAssertMixed3Inv l (a:B.t) = assertMixed3Map := InvMap.add l a !assertMixed3Map  

  let assertMap_print fmt m = InvMap.iter (fun l a -> 
      Format.fprintf fmt "Assertion (%a) - after filter: %a\n" label_print l B.print a) m
	  
  let assertMap_printMixed fmt m1 m2 m = InvMap.iter (fun l a -> let a1 = InvMap.find l m1 in let a2 = InvMap.find l m2 in 
  		Format.fprintf fmt "\nAssertion (%a): " label_print l;
		(*Format.fprintf fmt "before ass (%a): \n" B.print a;
		Format.fprintf fmt "filter ass (%a): \n" B.print a1;
		Format.fprintf fmt "filter neg ass (%a): \n" B.print a2; *)
		(B.print_assert fmt a1 a2 a)) m
      (*Format.fprintf fmt "Assertion (%a): %a\n" label_print l (B.print_assert a1 a2 a)) m*)

  let program_vars = ref []
  let resultAss = ref 0 
  let p_negAss = ref []  

  (* Forward Iterator *)

  let rec fwdStm funcs env_vars env_feats vars feats p s =
    match s with
    | A_label _ -> p
    | A_return -> B.bot env_vars env_feats vars feats
    | A_assign ((l,_),(e,_)) -> let featsIn = (AbstractSyntax.aExp_toFeats e feats true) in 
								let varsIn = (AbstractSyntax.aExp_toFeats e vars true) in
								let isFeat_l = ref false in 
								(match l with
    							| A_var l -> List.iter (fun ft -> if (l.varId==ft.varId) then isFeat_l:=true) feats 
								| _ -> isFeat_l := !isFeat_l);
								(*Format.fprintf Format.std_formatter "number of features in exp %d, number of vars in exp %d, is Lvar feature %b\n" (List.length featsIn) (List.length varsIn) !isFeat_l;  *)
								if (((List.length featsIn) = 0) && (not !isFeat_l)) then B.fwdAssign p (l,e)
								else if (((List.length featsIn) > 0) && (not !isFeat_l)) then B.fwdAssign_var p (l,e)
								else if (((List.length varsIn) = 0) && (!isFeat_l)) then ((*Format.fprintf !fmt "\n assign_feat %a \n" B.print p;*) B.fwdAssign_feat_var p (l,e))
								else (let pp = B.fwdAssign_feat_var p (l,e) in (*Format.fprintf !fmt "\n AssFV %a \n" B.print pp;*) pp)
    | A_assert (b,ba) -> (*B.filter p b*)
	      let p2' = (B.filter p b) in
		  let b_neg = fst (negBExp (b,ba)) in 
      	  let p2 = B.filter p b_neg in
		  (*Format.fprintf !fmt "\n ASSERT (%a) \n %a\n" bExp_print_aux b_neg B.print p2;*)
		  resultAss := B.analyzeAss p2' p2 p; 
		  p_negAss := [p2]; 
		  addAssertInv b p2; p2'
		  (* if (not (B.isBot p2)) then (Format.fprintf !fmt "\nassert (%a) \n %a\n" bExp_print_aux b B.print_assert p2; p2') 
		  else (Format.fprintf !fmt "\nassert (%a) CORRECT\n" bExp_print_aux b; p2') *)	
    | A_if ((b,ba),s1,s2) ->
	  let featsIn = (AbstractSyntax.bExp_toFeats b feats true) in 
	  let varsIn = (AbstractSyntax.bExp_toFeats b !program_vars true) in 
	  (*Format.fprintf !fmt "\n Bexp : (%a) \n " bExp_print_aux b; 
	  Format.fprintf Format.std_formatter "number of feats in Bexp %d, number of vars %d\n" (List.length featsIn) (List.length varsIn);  *)
	  if ((List.length featsIn) = 0) then ( 
      	let p1' = fwdBlk funcs env_vars env_feats vars feats (B.filter p b) s1 in
      	let p2 = B.filter p (fst (negBExp (b,ba))) in
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
      	B.compress (B.join p1' p2') )
	  else if ((List.length varsIn) = 0) then ( 
	  	let p1 = B.filter_config p b in 
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in 
	  	let b_neg = fst (negBExp (b,ba)) in 
      	let p2 = B.filter_config p b_neg in
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
	  	B.compress (B.join p1' p2')	  
	  )
	  else ( 
	  	let p1 = B.filter_general p b in 
      	let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in 
	  	let b_neg = fst (negBExp (b,ba)) in 
      	let p2 = B.filter_general p b_neg in
      	let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
	  	B.compress (B.join p1' p2')	  
	  ) 
    | A_ifdef ((b,ba),s1,s2) ->	  
	  (*Format.fprintf !fmt "\n config-filter anal %d\n" 1;*)
	  let p1 = B.filter_config p b in 
      let p1' = fwdBlk funcs env_vars env_feats vars feats p1 s1 in 
	  (*let cst = (match b with | A_bvar v -> 0 | _ -> 1) in *)
	  let b_neg = fst (negBExp (b,ba)) in 
      let p2 = B.filter_config p b_neg in (*!AbstractSyntax.cst in AbstractSyntax.cst:=1; *)
      let p2' = fwdBlk funcs env_vars env_feats vars feats p2 s2 in
	  let pp = B.compress (B.join p1' p2') in 
	  (*Format.fprintf !fmt "\n ifdef p1=%a p1'=%a\n p2=%a p2'=%a \n" B.print p1 B.print p1' B.print p2 B.print p2';*) (*Format.fprintf !fmt "\n ifdef join %a \n" B.print (B.join p1' p2');
	  Format.fprintf !fmt "\n ifdef compress %a \n" B.print pp; *)
      pp		  
    | A_while (l,(b,ba),s) ->
	  let p_in = p in 
      let rec aux i p2 n =
        let i' = B.join_while p p2 in
        (*if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" B.print p;
          Format.fprintf !fmt "i: %a\n" B.print i;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "i': %a\n" B.print i'
        end;  *)
        if B.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' else 
              B.widen i (B.join i i') in
          (*if !tracefwd && not !minimal then*)
            (*Format.fprintf !fmt "i'': %a\n" B.print i'';*)
		  let i''' = B.filter i'' b in (*Format.fprintf !fmt "i''': %a\n" B.print i'''; *)
          aux i'' (fwdBlk funcs env_vars env_feats vars feats (i''') s) (n+1)
      in
      let i = B.bot env_vars env_feats vars feats in
      let p2 = fwdBlk funcs env_vars env_feats vars feats (B.filter i b) s in
      let p = aux i p2 1 in
	  let p_down = fwdBlk funcs env_vars env_feats vars feats (B.filter p b) s in   (* this line is added additionally: performs narrowing  *)
      addFwdInv l p_down; 
	  let featsIn = (AbstractSyntax.bExp_toFeats b feats true) in 
	  let varsIn = (AbstractSyntax.bExp_toFeats b !program_vars true) in 	  
	  let notb = fst (negBExp (b,ba)) in 
	  if ((List.length featsIn) = 0) then ( 
      	let p2 = B.filter p_down notb in
      	let p2' = B.filter p_in notb in
      	B.compress (B.join p2 p2') )
	  else if ((List.length varsIn) = 0) then ( 
	  	let p2 = B.filter_config p_down notb in 
      	let p2' = B.filter_config p_in notb in
	  	B.compress (B.join p2 p2')	  
	  )
	  else ( 
	  	let p2 = B.filter_general p_down notb in 
      	let p2' = B.filter_general p_in notb in 
		(*Format.fprintf !fmt "While After: p2 = %a \n p2' = %a \n" B.print p2 B.print p2';  *)
	  	B.compress (B.join p2 p2')	  
	  ) 	  
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env_vars env_feats vars feats p s) p ss in
      fwdBlk funcs env_vars env_feats vars feats p f.funcBody
    | A_recall (f,ss) -> B.top env_vars env_feats vars feats (* TODO *) 
	| _ -> raise (Invalid_argument "\n Unhandled Statement\n")

  and fwdBlk funcs env_vars env_feats vars feats (p:B.t) (b:block) : B.t =
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
      (* fwdBlk funcs env_vars env_feats vars feats (fwdStm funcs env_vars env_feats vars feats p s) b *)
	  match s with 
	  | A_assert (bb,bba) -> let p = B.propagateCons p in 
	  						let p'= fwdStm funcs env_vars env_feats vars feats p s in 
	  						(*Format.fprintf !fmt "\nAssert result: %d\n" !resultAss;*)
	  						(if (!resultAss==5) then addAssertUnreachInv l p'
							 else (if (!resultAss==2) then addAssertErrorInv l p' 
									else (if (!resultAss==1) then addAssertCorrectInv l p'
									else (if (!resultAss==3) then addAssertDontKnowInv l p'
											else (addAssertMixed1Inv l p'; addAssertMixed2Inv l (List.hd !p_negAss); addAssertMixed3Inv l p)))));
							fwdBlk funcs env_vars env_feats vars feats p' b
	  | _ -> fwdBlk funcs env_vars env_feats vars feats (fwdStm funcs env_vars env_feats vars feats p s) b

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

let rec process_cons feats_list env_feats ll = 
		match feats_list with
		| [] -> ll
		| hd :: tl ->
			let tmp = ref [] in
			let typ = hd.featTyp in
			if (typ <> A_BOOL) then (
				let dom = hd.featDom in
				let cons1 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons1 [| ((Coeff.s_of_int 1), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (-(List.nth dom 0))));
				let cons2 = Lincons1.make (Linexpr1.make env_feats) Lincons1.SUPEQ in
  				Lincons1.set_array cons2 [| ((Coeff.s_of_int (-1)), (Var.of_string hd.featId)) |] (Some (Coeff.s_of_int (List.nth dom ((List.length dom)-1))));				
				tmp := cons1::cons2::!tmp
			); 
			process_cons tl env_feats (!tmp @ ll)


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
    let vars1 = List.append v1 v2 in 
	program_vars := vars1; 
    (*let env_vars = aux vars (Environment.make [||] [||]) in*)
    let s = f.funcBody in
    (*initBlk env vars stmts; initBlk env vars s; *)
    (* TODO: handle functions calls *)
    (* Forward Analysis *)
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace:\n";
    let startfwd = Sys.time () in
	let feats = ref [] in
	let feats_feat = ref [] in
	let env_feats = ref (Environment.make [||] [||]) in 
	StringMap.iter (fun key value -> feats_feat := value :: !feats_feat; feats := {varId = value.featId; varName = value.featName; varTyp = value.featTyp} :: !feats; 
									env_feats :=  Environment.add !env_feats [|(Var.of_string value.featId)|] [||]) !ItoA.features; 
	let vars = List.append vars1 !feats in 
    let env_vars = aux vars (Environment.make [||] [||]) in 
	let constraints_list = process_cons !feats_feat !env_feats [] in 
	let part_list = P.inner !env_feats !feats constraints_list in (*print_string "GOO"; P.print !fmt part_list;*)
	let leaf_list = P.inner env_vars vars (process_cons !feats_feat env_vars []) in
    let state = fwdBlk funcs env_vars !env_feats vars !feats (fwdBlk funcs env_vars !env_feats vars !feats (B.initial ~domain:part_list leaf_list env_vars !env_feats vars !feats) stmts) s in
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
			Format.fprintf !fmt "\nMixed Assertions: total=%d\n" (InvMap.cardinal !assertMixed1Map);  
			assertMap_printMixed !fmt !assertMixed1Map !assertMixed2Map !assertMixed3Map;
		end;
	  true

end
