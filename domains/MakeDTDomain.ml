(***************************************************)
(*                                                 *)
(*             MakeDTDomain.ml                    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open DTDomain
open ItoA
open Partition
open Constraints


let tracebwd = ref false
let retrybwd = ref 5
let fmt = ref Format.std_formatter

(** The ranking functions abstract domain is an abstract domain functor T. 
    It is parameterized by an auxiliary abstract domain for linear constraints 
    C, and an auxiliary abstract domains for functions F, both parameterized by 
    an auxiliary numerical abstract domain B. *)
module MakeDTDomain (P: PARTITION) : DTDomain =
struct

  module P = P	(* auxiliary numerical abstract domain *)
  module C = P.C	(* auxiliary linear constraints abstract domain *)
  module N = P.N  (* numerical domain *)

  module CMap = Map.Make(
    struct
      type t = C.t
      let compare = C.compare
    end)

  module L =
  struct
    type t = C.t * C.t
    let compare (c1,nc1) (c2,nc2) =
      if (C.isLeq nc1 c1) then
        if (C.isLeq nc2 c2) then 
          C.compare c1 c2 
        else C.compare c1 nc2
      else if (C.isLeq nc2 c2) 
      then C.compare nc1 c2 
      else C.compare nc1 nc2
  end

  module LSet = Set.Make(L)

  (** The abstract domain manipulates numerical properties of program families. 
      These are represented by decision trees, where the decision nodes are 
      labeled by Boolean features and linear constraints over the numerical features, and the leaf 
      nodes are labeled by linear constraints over the program variables. The decision 
      nodes recursively partition the space of possible values of the features and the linear constraints at the leaves provide 
	  the corresponding invariants. *)
  type tree = Leaf of P.t | Node of L.t * tree * tree

  (** An element of the decision tree abstract domain. *)
  type t = {
    domain : P.t option;	(* current reachable configurations - feature states *)
    tree : tree;			(* current tree *)
    env_vars : Environment.t;	(* current APRON environment for variables*)
	env_feats : Environment.t;	(* current APRON environment for features *)
    vars : var list;			(* current list of program variables *)
    feats : var list		(* current list of feature variables *)	
  }


  (** The current decision tree. *)
  let tree t = t.tree

  (** Prints the current decision tree. *)
  let print_tree vars feats fmt t =
    let rec aux ind fmt t =
      match t with
      | Leaf p ->  Format.fprintf fmt "\n%sLEAF %a" ind P.print p
      | Node ((c,_),l,r) -> Format.fprintf fmt "\n%sNODE %a%a%a" ind 
                              (C.print feats) c (aux (ind ^ "  ")) l (aux (ind ^ "  ")) r
    in aux "" fmt t

  (**
     Prints a tree in graphviz 'dot' format for visualization. 
     http://www.graphviz.org/content/dot-language
  *)
  let print_graphviz_dot fmt t = 
    let vars = t.vars in
	let feats = t.feats in
    let nodeId = ref 0 in
    let nextNodeId () =
      let id = !nodeId in
      nodeId := id + 1;
      Printf.sprintf "node%d" id
    in
    let rec aux id fmt t =
      match t with
      | Leaf p -> Format.fprintf fmt "%s[shape=box,label=\"%a\"]" id P.print p
      | Node ((c,_),l,r) -> 
        let leftId = nextNodeId () in
        let hiddenId = nextNodeId () in
        let rightId = nextNodeId () in
        Format.fprintf fmt "%s[shape=box,style=rounded,label=\"%a\"] ; %s [label=\"\",width=.1,style=invis] ; %s -- %s ; %s -- %s [style=invis] ; %s -- %s [style=dashed] {rank=same %s -- %s -- %s [style=invis]} ; %a; %a" 
            id
            (C.print vars) c
            hiddenId 
            id leftId 
            id hiddenId 
            id rightId 
            leftId hiddenId rightId 
            (aux leftId) l
            (aux rightId) r
    in Format.fprintf fmt "graph G { %a }" (aux (nextNodeId ())) t.tree


  (** Collects the linear constraints labeling the current decision tree. *)
  let tree_labels t =
    let ls = ref LSet.empty in
    let rec aux t =
      match t with
      | Leaf _ -> ()
      | Node (c,l,r) -> aux l; aux r; ls := LSet.add c !ls
    in aux t; !ls


  (* map function for decision tree*)
  let tree_map p_leaf t: t = 
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let rec aux (tree:tree) : tree = match tree with
      | Leaf p -> p_leaf p
      | Node (c,l,r) -> Node (c, aux l, aux r)
    in { domain = domain; tree = aux t.tree; 
		env_vars = env_vars;
	  	env_feats = env_feats;
      	vars = vars;
	  	feats = feats }

  (** Sorts (and normalizes the constraints within) a decision tree `t`. 

      Let x_1,...,x_k be program variables. We consider all linear 
      constraints in a decision tree to have the following normal form:
      m_1*x_1 + ... + m_k*x_k + q >= 0
      where m_1,...,m_k,q are integer coefficients. Moreover, in order to 
      ensure a canonical representation of the linear constraints, we require
      gcd(|m_1|,...,|m_k|,|q|) = 1
      We then impose a total order on the linear constraints. In particular, 
      we define such order to be the lexicographic order on the coefficients 
      m_1,...,m_k and constant q of the linear constraints. *)
  let rec sort_tree t =
    let rec swap_tree t =
      match t with
      | Node((c,nc),l,r) ->
        let sl = swap_tree l in
        let sr = swap_tree r in
        if (C.isLeq nc c)
        then (* t is normalized *)
          (match sl, sr with
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isEq c1 c2) (* c1 = c2 *) ->
             if (C.isLeq c c1)
             then (* c <= c1 = c2 *)
               if (C.isEq c c1)
               then (* c = c1 = c2 *) Node((c,nc),l1,r2)
               else (* c < c1 = c2 *) Node((c,nc),sl,sr)
             else (* c > c1 = c2 *)
             if (C.similar c c1) 
             then Node((c1,nc1),l1,Node((c,nc),r1,r2)) 
             else
               let rt = (c,nc) in 
               Node((c1,nc1),Node(rt,l1,l2),Node(rt,r1,r2))
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isLeq c1 c2) (* c1 < c2 *) ->
             if (C.isLeq c c1)
             then (* c <= c1 < c2 *)
               if (C.isEq c c1)
               then (* c = c1 < c2 *) Node((c,nc),l1,sr)
               else (* c < c1 < c2 *) Node((c,nc),sl,sr)
             else (* c > c1 < c2 *)
             if (C.isLeq c c2)
             then (* c1 < c <= c2 *)
               if (C.isEq c c2)
               then (* c1 < c = c2 *)
                 if (C.similar c c1) 
                 then Node((c1,nc1),l1,Node((c,nc),r1,r2)) 
                 else
                   let rt = (c,nc) in
                   let rt1 = (c1,nc1) in
                   Node(rt1,Node(rt,l1,r2),Node(rt,r1,r2))
               else (* c1 < c < c2 *)
               if (C.similar c2 c) && (C.similar c c1) 
               then Node((c1,nc1),l1,Node((c,nc),r1,sr)) 
               else
                 let rt = (c,nc) in
                 let rt1 = (c1,nc1) in
                 Node(rt1,Node(rt,l1,sr),Node(rt,r1,sr))
             else (* c1 < c2 < c *)
             if (C.similar c c2) && (C.similar c2 c1) 
             then Node((c1,nc1),l1,Node((c,nc),r1,r2))
             else
               let rt = (c,nc) in
               let rt2 = (c2,nc2) in 
               Node((c1,nc1),
                    Node(rt2,Node(rt,l1,l2),Node(rt,l1,r2)),
                    Node(rt2,Node(rt,r1,l2),Node(rt,r1,r2))
                   )
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isLeq c2 c1) (* c1 > c2 *) ->
             if (C.isLeq c c2)
             then (* c <= c2 < c1 *)
               if (C.isEq c c2)
               then (* c = c2 < c1 *) Node((c,nc),sl,r2)
               else (* c < c2 < c1 *) Node((c,nc),sl,sr)
             else (* c > c2 < c1 *)
             if (C.isLeq c c1)
             then (* c2 < c <= c1 *)
               if (C.isEq c c1)
               then (* c2 < c = c1 *)
                 if (C.similar c c2) 
                 then Node((c,nc),l1,r2) 
                 else
                   let rt = (c,nc) in
                   let rt2 = (c2,nc2) in
                   Node(rt2,Node(rt,l1,l2),Node(rt,l1,r2))
               else (* c2 < c < c1 *)
               if (C.similar c1 c) && (C.similar c c2) 
               then Node((c,nc),l1,r2) 
               else
                 let rt = (c,nc) in 
                 let rt2 = (c2,nc2) in 
                 Node(rt2,Node(rt,sl,l2),Node(rt,sl,r2))
             else (* c2 < c1 < c *)
             if (C.similar c c1) && (C.similar c1 c2) 
             then Node((c1,nc1),l1,Node((c,nc),r1,r2))
             else
               let rt = (c,nc) in
               let rt1 = (c1,nc1) in  
               Node((c2,nc2),
                    Node(rt1,Node(rt,l1,l2),Node(rt,r1,l2)),
                    Node(rt1,Node(rt,l1,r2),Node(rt,r1,r2))
                   )
           | Node((c1,nc1),l1,r1), _ ->
             if (C.isLeq c c1)
             then (* c <= c1 *)
               if (C.isEq c c1)
               then (* c = c1 *) Node((c,nc),l1,sr)
               else (* c < c1 *) Node((c,nc),sl,sr)
             else (* c > c1 *)
             if (C.similar c c1) 
             then Node((c1,nc1),l1,Node((c,nc),r1,sr)) 
             else
               let rt = (c,nc) in 
               Node((c1,nc1),Node(rt,l1,sr),Node(rt,r1,sr))
           | _, Node((c2,nc2),l2,r2) ->
             if (C.isLeq c c2)
             then (* c <= c2 *)
               if (C.isEq c c2)
               then (* c = c2 *) Node((c,nc),sl,r2)
               else (* c < c2 *) Node((c,nc),sl,sr)
             else (* c > c2 *)
             if (C.similar c c2) 
             then Node((c,nc),sl,r2) 
             else
               let rt = (c,nc) in 
               Node((c2,nc2),Node(rt,sl,l2),Node(rt,sl,r2))
           | _ -> Node((c,nc),sl,sr) (* same *))
        else (* t is not normalized *)
          (match sl,sr with
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isEq c1 c2) (* c1 = c2 *) ->
             if (C.isLeq nc c1)
             then (* nc <= c1 = c2 *)
               if (C.isEq nc c1)
               then (* nc = c1 = c2 *) Node((nc,c),l2,r1)
               else (* nc < c1 = c2 *) Node((nc,c),sr,sl)
             else (* nc > c1 = c2 *)
             if (C.similar nc c1) 
             then Node((c1,nc1),l2,Node((nc,c),r2,r1)) 
             else
               let rt = (nc,c) in
               let rt1 = (c1,nc1) in
               Node(rt1,Node(rt,l2,l1),Node(rt,r2,r1))
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isLeq c1 c2) (* c1 < c2 *) ->
             if (C.isLeq nc c1)
             then (* nc <= c1 < c2 *)
               if (C.isEq nc c1)
               then (* nc = c1 < c2 *) Node((nc,c),sr,r1)
               else (* nc < c1 < c2 *) Node((nc,c),sr,sl)
             else (* nc > c1 < c2 *)
             if (C.isLeq nc c2)
             then (* c1 < nc <= c2 *)
               if (C.isEq nc c2)
               then (* c1 < nc = c2 *)
                 if (C.similar nc c1) 
                 then Node((nc,c),l2,r1) 
                 else
                   let rt = (nc,c) in 
                   let rt1 = (c1,nc1) in	
                   Node(rt1,Node(rt,l2,l1),Node(rt,l2,r1))
               else (* c1 < nc < c2 *)
               if (C.similar c2 nc) && (C.similar nc c1) 
               then Node((nc,c),l2,r1) 
               else
                 let rt = (nc,c) in 
                 let rt1 = (c1,nc1) in
                 Node(rt1,Node(rt,sr,l1),Node(rt,sr,r1))
             else (* c1 < c2 < nc *)
             if (C.similar nc c2) && (C.similar c2 c1) 
             then Node((c2,nc2),l2,Node((nc,c),r2,r1))
             else
               let rt = (nc,c) in
               let rt2 = (c2,nc2) in 
               Node((c1,nc1),
                    Node(rt2,Node(rt,l2,l1),Node(rt,r2,l1)),
                    Node(rt2,Node(rt,l2,r1),Node(rt,r2,r1))
                   )
           | Node((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) 
             when (C.isLeq c2 c1) (* c1 > c2 *) ->
             if (C.isLeq nc c2)
             then (* nc <= c2 < c1 *)
               if (C.isEq nc c2)
               then (* nc = c2 < c1 *) Node((nc,c),l2,sl)
               else (* nc < c2 < c1 *) Node((nc,c),sr,sl)
             else (* nc > c2 < c1 *)
             if (C.isLeq nc c1)
             then (* c2 < nc <= c1 *)
               if (C.isEq nc c1)
               then (* c2 < nc = c1 *)
                 if (C.similar nc c2) 
                 then Node((c2,nc2),l2,Node((nc,c),r2,r1)) 
                 else
                   let rt = (nc,c) in
                   let rt2 = (c2,nc2) in
                   Node(rt2,Node(rt,l2,r1),Node(rt,r2,r1))
               else (* c2 < nc < c1 *)
               if (C.similar c1 nc) && (C.similar nc c2) 
               then Node((c2,nc2),l2,Node((nc,c),r2,sl)) 
               else
                 let rt = (nc,c) in
                 let rt2 = (c2,nc2) in 
                 Node(rt2,Node(rt,l2,sl),Node(rt,r2,sl))
             else (* c2 < c1 < nc *)
             if (C.similar nc c1) && (C.similar c1 c2) 
             then Node((c2,nc2),l2,Node((nc,c),r2,r1))
             else
               let rt = (nc,c) in
               let rt1 = (c1,nc1) in 
               Node((c2,nc2),
                    Node(rt1,Node(rt,l2,l1),Node(rt,l2,r1)),
                    Node(rt1,Node(rt,r2,l1),Node(rt,r2,r1))
                   )
           | Node((c1,nc1),l1,r1), _ ->
             if (C.isLeq nc c1)
             then (* nc <= c1 *)
               if (C.isEq nc c1)
               then (* nc = c1 *) Node((nc,c),sr,r1)
               else (* nc < c1 *) Node((nc,c),sr,sl)
             else (* nc > c1 *)
             if (C.similar nc c1) then Node((nc,c),sr,r1) 
             else
               let rt = (nc,c) in 		
               Node((c1,nc1),Node(rt,sr,l1),Node(rt,sr,r1))
           | _, Node((c2,nc2),l2,r2) ->
             if (C.isLeq nc c2)
             then (* nc <= c2 *)
               if (C.isEq nc c2)
               then (* nc = c2 *) Node((nc,c),l2,sl)
               else (* nc < c2 *) Node((nc,c),sr,sl)
             else (* nc > c2 *)
             if (C.similar nc c2)
             then Node((c2,nc2),l2,Node((nc,c),r2,sl)) 
             else
               let rt = (nc,c) in 	
               Node((c2,nc2),Node(rt,l2,sl),Node(rt,r2,sl))
           | _ -> Node((nc,c),sr,sl) (* it stays the same *))
      | _ -> t
    in
    let st = swap_tree t in (* root(st) is the smallest constraint in t *)
    match st with
    | Node(c,l,r) ->
      let sl = sort_tree l in
      let sr = sort_tree r in
      Node(c,sl,sr)
    | _ -> st


  let sorting_tree t: t = 
    let domain = t.domain in 
	let tree = t.tree in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    { domain = domain; 
		tree = sort_tree tree;
		env_vars = env_vars;
	  	env_feats = env_feats;
      	vars = vars;
	  	feats = feats }

  (** The bottom element of the abstract domain, i.e., a decision tree with a single `bottom` leaf. *)
  let bot ?domain ev ef vs fs = 
    { domain = domain; tree = Leaf (P.bot ev vs); env_vars = ev; env_feats = ef; vars = vs; feats =fs }


  (** The top element of the abstract domain. The totally unknown function, i.e., a decision tree with a single `top` leaf. *)
  let top ?domain ev ef vs fs = 
    { domain = domain; tree = Leaf (P.top ev vs); env_vars = ev; env_feats = ef; vars = vs; feats =fs }

  let initial ?domain leaf ev ef vs fs = 
    { domain = domain; tree = Leaf leaf; env_vars = ev; env_feats = ef; vars = vs; feats =fs }	

  (** BINARY OPERATORS *)

  let tree_unification_aux t1 t2 env_vars env_feats vars feats cs = 
    let rec aux (t1,t2) cs =
      match t1,t2 with
      | Leaf _,Leaf _ -> (t1,t2)
      | Node ((c1,nc1),l1,r1),Node((c2,nc2),l2,r2) when (C.isEq c1 c2) (* c1 = c2 *) ->
        let (ul1,ul2) = aux (l1,l2) (c1::cs) in
        let (ur1,ur2) = aux (r1,r2) (nc1::cs) in
        (Node((c1,nc1),ul1,ur1),Node((c2,nc2),ul2,ur2))
      | Node ((c1,nc1),l1,r1),Node((c2,nc2),l2,r2) when (C.isLeq c1 c2) (* c1 < c2 *) ->
        let bcs = P.inner env_feats feats cs in
        let bc1 = P.inner env_feats feats [c1] in
        if (P.isLeq bcs bc1) then (* c1 is redundant *) 
          aux (l1,t2) cs
        else (* c1 is not redundant *)
          let bnc1 = P.inner env_feats feats [nc1] in
          if (P.isLeq bcs bnc1) then (* nc1 is redundant *) 
            aux (r1,t2) cs
          else (* nc1 is not redundant *)
            let (ul1,ul2) = aux (l1,t2) (c1::cs) in
            let (ur1,ur2) = aux (r1,t2) (nc1::cs) in
            (Node((c1,nc1),ul1,ur1),Node((c1,nc1),ul2,ur2))
      | Node ((c1,nc1),l1,r1),Node((c2,nc2),l2,r2) 
        when (C.isLeq c2 c1) (* c1 > c2 *) ->
        let bcs = P.inner env_feats feats cs in
        let bc2 = P.inner env_feats feats [c2] in
        if (P.isLeq bcs bc2)
        then (* c2 is redundant *) aux (t1,l2) cs
        else (* c2 is not redundant *)
          let bnc2 = P.inner env_feats feats [nc2] in
          if (P.isLeq bcs bnc2)
          then (* nc2 is redundant *) aux (t1,r2) cs
          else (* nc2 is not redundant *)
            let (ul1,ul2) = aux (t1,l2) (c2::cs) in
            let (ur1,ur2) = aux (t1,r2) (nc2::cs) in
            (Node((c2,nc2),ul1,ur1),Node((c2,nc2),ul2,ur2))
      | Node ((c1,nc1),l1,r1),_ ->
        let bcs = P.inner env_feats feats cs in
        let bc1 = P.inner env_feats feats [c1] in
        if (P.isLeq bcs bc1)
        then (* c1 is redundant *) aux (l1,t2) cs
        else (* c1 is not redundant *)
          let bnc1 = P.inner env_feats feats [nc1] in
          if (P.isLeq bcs bnc1)
          then (* nc1 is redundant *) aux (r1,t2) cs
          else (* nc1 is not redundant *)
            let (ul1,ul2) = aux (l1,t2) (c1::cs) in
            let (ur1,ur2) = aux (r1,t2) (nc1::cs) in
            (Node((c1,nc1),ul1,ur1),Node((c1,nc1),ul2,ur2))
      | _,Node((c2,nc2),l2,r2) ->
        let bcs = P.inner env_feats feats cs in
        let bc2 = P.inner env_feats feats [c2] in
        if (P.isLeq bcs bc2)
        then (* c2 is redundant *) aux (t1,l2) cs
        else (* c2 is not redundant *)
          let bnc2 = P.inner env_feats feats [nc2] in
          if (P.isLeq bcs bnc2)
          then (* nc2 is redundant *) aux (t1,r2) cs
          else (* nc2 is not redundant *)
            let (ul1,ul2) = aux (t1,l2) (c2::cs) in
            let (ur1,ur2) = aux (t1,r2) (nc2::cs) in
            (Node((c2,nc2),ul1,ur1),Node((c2,nc2),ul2,ur2))
    in aux (t1,t2) cs

  (** The decision tree orderings and binary operators rely on tree 
      unification to find a common labeling for the decision trees. Given two 
      decision trees t1 and t2 the unification accumulates into a set `cs` 
      the linear constraints encountered along the paths of the decision 
      trees, possibly adding decision nodes or removing constraints that are 
      redundant or whose negation is redundant with respect to `cs`. 

      The implementation assumes that t1 and t2 are sorted and normalized. *)	
  let tree_unification t1 t2 env_vars env_feats vars feats = 
    tree_unification_aux t1 t2 env_vars env_feats vars feats [] 

  (** Given two decision trees t1 and t2, the ordering accumulates 
      into a set `cs` the linear constraints encountered along the paths of 
      the decision tree up to the leaf nodes, which are compared by means of 
      the leaf node ordering. 

      The implementation assumes that t1 and t2 are defined over the same 
      reachable states, the same APRON envorinment and the same list of 
      program variables. *)



let isLeq t1 t2 =
    let domain = t1.domain in 
    let env_vars = t1.env_vars in
    let env_feats = t1.env_feats in	
    let vars = t1.vars in 
	let feats = t1.feats in 
    let rec aux (t1,t2) cs = match t1,t2 with
      | Leaf p1, Leaf p2 ->
        let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        (*Format.fprintf !fmt "\n isLEQ %a\n" P.print p;*)
		if (P.isBot p) then true
        else
          (P.isLeq p1 p2 (* forall leafs x: P1(x) <= P2(x) *))
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        (aux (l1,l2) (c1::cs)) && (aux (r1,r2) (nc1::cs))
      | _ -> raise (Invalid_argument "isLeq:")
    in aux (tree_unification t1.tree t2.tree env_vars env_feats vars feats) []

	(**)

  	let rec join_t env_vars vars env_feats feats t1 t2 cs domain =
		 match t1,t2 with
      | Leaf p1, Leaf p2 ->
        (*let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
            (*P.meet (P.inner env_feats feats cs) domain in
		Format.fprintf !fmt "\n isJOIN old %a\n" P.print p;*)
        if (P.isBot p) then Leaf (P.bot env_vars vars)
        else	 *) 
          Leaf (P.join p1 p2 (* forall leafs x: join (P1(x), P2(x)) *))
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        let l = join_t env_vars vars env_feats feats l1 l2 (c1::cs) domain in 
		let r = join_t env_vars vars env_feats feats r1 r2 (nc1::cs) domain in 
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "isJoin:")


  	let join t1 t2 =
    let domain = t1.domain in 
    let env_vars = t1.env_vars in
    let env_feats = t1.env_feats in	
    let vars = t1.vars in 
	let feats = t1.feats in 
    let rec aux (t1,t2) cs = match t1,t2 with
      | Leaf p1, Leaf p2 ->
        let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
            (*P.meet (P.inner env_feats feats cs) domain in
		Format.fprintf !fmt "\n isJOIN old %a\n" P.print p;*)
        if (P.isBot p) then Leaf (P.bot env_vars vars)
        else
          Leaf (P.join p1 p2 (* forall leafs x: join (P1(x), P2(x)) *))
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        let l = aux (l1,l2) (c1::cs) in 
		let r = aux (r1,r2) (nc1::cs) in 
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "isJoin:")
    in 
	let (t1,t2) = tree_unification t1.tree t2.tree env_vars env_feats vars feats in 
	(*let rec aux2 t cs =
      match t with
      | Leaf p ->
        let b = P.inner env_feats feats cs in
        if P.isBot b then () else Format.fprintf !fmt "[%a HERE? %a] " P.print b P.print p
      | Node((c,nc),l,r) -> aux2 r (nc::cs); aux2 l (c::cs)
    in aux2 t1 []; aux2 t2 []; *)
	(*Format.fprintf !fmt "\n%a JOIN %a" DTDomain.print !fmt t1; DTDomain.print !fmt t2; *)
	let t = aux (t1,t2) [] in 
	{ domain = domain;
      tree = t;
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }	
	

  	let join_while t1 t2 =
    let domain = t1.domain in 
    let env_vars = t1.env_vars in
    let env_feats = t1.env_feats in	
    let vars = t1.vars in 
	let feats = t1.feats in 
    let rec aux (t1,t2) cs = match t1,t2 with
      | Leaf p1, Leaf p2 ->
        let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
            (*P.meet (P.inner env_feats feats cs) domain in
		Format.fprintf !fmt "\n isJOIN old %a\n" P.print p;*)
        if (P.isBot p) then Leaf (P.bot env_vars vars)
        else
          Leaf (P.join p1 p2 (* forall leafs x: join (P1(x), P2(x)) *))
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        let l = aux (l1,l2) (c1::cs) in 
		let r = aux (r1,r2) (nc1::cs) in 
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "isJoin:")
    in 
	let (t1,t2) = tree_unification t1.tree t2.tree env_vars env_feats vars feats in 
	(*let rec aux2 t cs =
      match t with
      | Leaf p ->
        let b = P.inner env_feats feats cs in
        if P.isBot b then () else Format.fprintf !fmt "[%a HERE? %a] " P.print b P.print p
      | Node((c,nc),l,r) -> aux2 r (nc::cs); aux2 l (c::cs)
    in aux2 t1 []; aux2 t2 []; *)
	(*Format.fprintf !fmt "\n%a JOIN %a" DTDomain.print !fmt t1; DTDomain.print !fmt t2; *)
	let t = aux (t1,t2) [] in (*Format.fprintf Format.std_formatter "\n join while: %a\n" (print_tree env_feats feats) t;*)
	{ domain = domain;
      tree = t;
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }

  (**)
	
  	let meet t1 t2 =
    let domain = t1.domain in 
    let env_vars = t1.env_vars in
    let env_feats = t1.env_feats in	
    let vars = t1.vars in 
	let feats = t1.feats in 
    let rec aux (t1,t2) cs = match t1,t2 with
      | Leaf p1, Leaf p2 ->
        let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        if (P.isBot p) then Leaf (P.bot env_vars vars)
        else
          Leaf (P.meet p1 p2 (* forall leafs x: join (P1(x), P2(x)) *))
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        let l = aux (l1,l2) (c1::cs) in 
		let r = aux (r1,r2) (nc1::cs) in 
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "isMeet:")
    in let t = aux (tree_unification t1.tree t2.tree env_vars env_feats vars feats) [] in 
	{ domain = domain;
      tree = t;
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }	

  (**)
  
  

  let left_unification t1 t2 env_vars env_feats vars feats domain =
    let ls1 = tree_labels t1 in
    let ls2 = tree_labels t2 in
    let ls = LSet.diff ls2 ls1 in
    (* Checks whether constraint c is redundant, given the constraints cs *)
    let is_redundant c cs =
      let bcs = P.inner env_feats feats cs in
      let bc = P.inner env_feats feats [c] in
      P.isLeq bcs bc
    in
    (* Compare l1 and l2, with labels not in t1 being greater
       * than all others, and thus will go to the bottom of the
       * tree
       *)
    let cmp l1 l2 =
      match (LSet.mem l1 ls, LSet.mem l2 ls) with
      | (false, false) -> L.compare l1 l2
      | (true, true) -> L.compare l1 l2
      | (false, true) -> -1
      | (true, false) -> 1
    in
    (* Removes redundant constraints in t *)
    let rec remove_redundant t cs =
      match t with
      | Leaf _ -> t
      | Node ((c, nc), l, r) ->
        if is_redundant c cs then
          remove_redundant l cs
        else if is_redundant nc cs then
          remove_redundant r cs
        else
          let ll = remove_redundant l (c :: cs) in
          let rr = remove_redundant r (nc :: cs) in
          Node ((c, nc), ll, rr)
    in
    let add_node (c, nc) (l, r) cs =
      if is_redundant c cs then
        l
      else if is_redundant nc cs then
        r
      else
        Node ((c, nc), l, r)
    in
    (* Creates a node, putting it in the right place so the tree
       * stays sorted
       *)
    let rec make_node (c, nc) (l, r) cs =
      let smallest t cc = match t with
        | Leaf _ -> cc
        | Node (cc1, l1, r1) ->
          if cmp cc cc1 > 0 then cc1 else cc
      in
      if is_redundant c cs then
        l
      else if is_redundant nc cs then
        r
      else
        let sc = smallest l (smallest r (c, nc)) in
        match (l, r) with
        | Node ((cl, ncl), ll, rl), Node ((cr, ncr), lr, rr) when
            cmp (cl, ncl) sc = 0 && cmp (cr, ncr) sc = 0 ->
          Node ((cl, ncl), make_node (c, nc) (ll, lr) (cl :: cs),
                make_node (c, nc) (rl, rr) (ncl :: cs))
        | Node ((cl, ncl), ll, rl), _ when cmp (cl, ncl) sc = 0 ->
          Node ((cl, ncl), make_node (c, nc) (ll, r) (cl :: cs),
                make_node (c, nc) (rl, r) (ncl :: cs))
        | _, Node ((cr, ncr), lr, rr) when cmp (cr, ncr) sc = 0 ->
          Node ((cr, ncr), make_node (c, nc) (l, lr) (cr :: cs),
                make_node (c, nc) (l, rr) (ncr :: cs))
        | _, _ -> Node ((c, nc), l, r)
    in
    (* Sort the tree completely; adding the new nodes *)
    let rec rebalance_tree t cs =
      match t with
      | Leaf _ -> t
      | Node ((c, nc), l, r) ->
        let ll = rebalance_tree l (c :: cs) in
        let rr = rebalance_tree r (nc :: cs) in
        make_node (c, nc) (ll, rr) cs
    in
    (* Collapse all leaves of t into a single one, making sure
       * all labels that are to be removed are deleted
       *)
    let rec collapse t cs =
      match t with
      | Leaf _ -> t
      | Node ((c, nc), l, r) ->
        assert (LSet.mem (c, nc) ls);
        if is_redundant c cs then
          collapse l cs
        else if is_redundant nc cs then
          collapse r cs
        else
          let ll = collapse l (c :: cs) in
          let rr = collapse r (nc :: cs) in
          match ll, rr with
          | Leaf p1, Leaf p2 ->
        		let p = match domain with 
          			| None -> P.inner env_feats feats cs 
          			| Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
        				if (P.isBot p) then Leaf (P.bot env_vars vars)
        				else Leaf (P.join p1 p2)
          | _, _ -> assert false
    in
    (* Finish t1 and t2 unification by doing a tree unification step
       * for labels that are in t1, and collapsing the others.
       *)
    let rec lunify t1 t2 cs =
      match (t1, t2) with
      | Leaf _, Leaf _ -> t2
      | Node ((c1, nc1), l1, r1), Leaf _ ->
        add_node (c1, nc1) (lunify l1 t2 (c1 :: cs), lunify r1 t2 (nc1 :: cs)) cs
      | Leaf _, Node ((c2, nc2), l2, r2) ->
        if LSet.mem (c2, nc2) ls then
          collapse t2 cs
        else
          add_node (c2, nc2) (lunify t1 l2 (c2 :: cs), lunify t1 r2 (nc2 :: cs)) cs
      | Node ((c1, nc1), l1, r1), Node ((c2, nc2), l2, r2) ->
        let w = cmp (c1, nc1) (c2, nc2) in
        if w = 0 then
          add_node (c1, nc1) (lunify l1 l2 (c1 :: cs), lunify r1 r2 (nc1 :: cs)) cs
        else if w < 0 then
          add_node (c1, nc1) (lunify l1 t2 (c1 :: cs), lunify r1 t2 (nc1 :: cs)) cs
        else (
          assert (not (LSet.mem (c2, nc2) ls));
          add_node (c2, nc2) (lunify t1 l2 (c2 :: cs), lunify t1 r2 (nc2 :: cs)) cs
        )
    in
    let t2 = lunify t1 (remove_redundant (rebalance_tree t2 []) []) [] in
    (* TODO: domain widening *)

    (* let t2 = left_unification t2 [] in *)
    (*Format.fprintf Format.std_formatter "\nt2[left_unification]: %a\n" (print_tree env_feats feats) t2;*)
    t2

  (**)
	
  	let widen t1 t2 =
    let domain = t1.domain in 
    let env_vars = t1.env_vars in
    let env_feats = t1.env_feats in	
    let vars = t1.vars in 
	let feats = t1.feats in 
    let rec aux (t1,t2) cs = match t1,t2 with
      | Leaf p1, Leaf p2 ->
        let p = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        if (P.isBot p) then Leaf (P.bot env_vars vars)
        else (
	 		(*let super_env = Environment.lce env_vars env_feats in 
			let cnstr = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints p) in (*EXTEND EVIRONMENT HERE*) 
			let cnstr1 = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints p1) in (*EXTEND EVIRONMENT HERE*)
			let cnstr2 = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints p2) in (*EXTEND EVIRONMENT HERE*)
			let super_cons1 = cnstr@cnstr1 in 					
			let super_cons2 = cnstr@cnstr2 in
			let super_vars = vars@feats in 
			let super_p1 = P.inner super_env super_vars super_cons1 in 
			let super_p2 = P.inner super_env super_vars super_cons2 in
			let super_p = P.widen super_p1 super_p2 in 
 			let p' = P.project super_p env_vars vars in
			let p'' = P.project super_p env_feats feats in 
			Format.fprintf !fmt "\n General widen_leaf super_p: %a :p': %a : p'': %a \n" P.print super_p P.print p' P.print p''; 		
			Leaf p' *)
            Leaf (P.widen p1 p2)
		)
      | Node ((c1,nc1),l1,r1), Node((c2,nc2),l2,r2) when (C.isEq c1 c2) ->
        let l = aux (l1,l2) (c1::cs) in 
		let r = aux (r1,r2) (nc1::cs) in 
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "isWiden:")
    in 
	let t1 = t1.tree in 
	let t2 = left_unification t1 t2.tree env_vars env_feats vars feats domain in 	
	let t = aux (tree_unification t1 t2 env_vars env_feats vars feats) [] in 
	{ domain = domain;
      tree = t;
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }

  (**)

  	let fwdAssign t (l,e) =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let rec aux t cs = match t with
      | Leaf p ->
        let p' = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        if (P.isBot p') then Leaf (P.bot env_vars vars)
        else Leaf (P.fwdAssign p (l,e))
      | Node ((c1,nc1),l1,r1) ->
        let l = aux l1 (c1::cs) in
		let r = aux r1 (nc1::cs) in
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "fwdAssign:")
    in { domain = domain;
      tree = aux t.tree [];
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }	  	

  (**)

  let rec fwdAssign_var t (l,e) =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	let rec aux t cs =
        (match t with
         | Leaf p -> 
		 			let b = match domain with | None -> P.inner env_feats feats cs | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in 
					if (P.isBot b) then Leaf (P.bot env_vars vars)
					else (
						let p' = P.fwdAssign p (l,e) in
						Leaf p'
				(*	let super_env = env_vars (*Environment.lce env_vars env_feats*) in 
			 		let cnstr1 = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints b) in (*EXTEND EVIRONMENT HERE*) 
			 		let cnstr2 = P.constraints p in (*List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints p) in*) (*EXTEND EVIRONMENT HERE*)
			 		let super_cons = cnstr1@cnstr2 in 					
			 		let super_vars = vars (*@feats*) in 
			 		let super_p = P.inner super_env super_vars super_cons in 
			 		let super_p' = P.fwdAssign super_p (l,e) in 
					 
		 			let p' = super_p' (*P.project super_p' env_vars vars*) in
					let p'' = P.project super_p' env_feats feats in 
					Format.fprintf !fmt "\n General assign_var super_p': %a :p': %a : p'': %a \n" P.print super_p' P.print p' P.print p''; 
					if (P.isLeq b p'') then (Leaf p') (*Format.fprintf !fmt "\n p'' is redundant \n" *)
					else ( 	toSort := true; 
							let dcs = match domain with | None -> [] | Some domain -> P.constraints domain in 
							let cs = ref [] in 
							List.iter (fun c -> if (not (List.mem c dcs)) then (let nc = C.negate c in cs:=(c,nc)::!cs)) (P.constraints p'');
							Node (List.hd !cs,Leaf p',Leaf (P.bot env_vars vars)) (*Format.fprintf !fmt "\n p'' is not redundant \n"; *)
						  )   *)
						  )
        | Node ((c1,nc1),l1,r1) ->
        			let l = aux l1 (c1::cs) in
					let r = aux r1 (nc1::cs) in
					Node ((c1,nc1),l,r)							
		   )
    in
		let t = aux t.tree [] in 
		(*Format.fprintf !fmt "\n toSort assign_var: %b \n" !toSort;*)
		let t' = (*if (!toSort) then (sort_tree t) else*) t in 
      { domain = domain; tree = t'; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }

  (**)

    let rec propagateCons t = 
    	let domain = t.domain in 
    	let env_vars = t.env_vars in
    	let env_feats = t.env_feats in	
    	let vars = t.vars in 
		let feats = t.feats in 	
		let rec aux t cs =
			(match t with
      		| Leaf p ->
				let cnstr_node = List.map (fun c -> Lincons1.extend_environment c env_vars) cs in (*EXTEND EVIRONMENT HERE*) 
				let p' = P.inner env_vars vars cnstr_node in
				Leaf (P.meet p p')
      		| Node ((c1,nc1),l1,r1) ->
       			let l = aux l1 (c1::cs) in
				let r = aux r1 (nc1::cs) in
				Node ((c1,nc1),l,r)
      		| _ -> raise (Invalid_argument "propagateCons:")		)
		in 
		{ domain = domain; tree = aux t.tree []; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats } 

  (**)

  	let fwdAssign_feat t (l,e) =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	let hasNode = ref false in 
	(*Format.fprintf !fmt "\n tree asg_feat: %a : \n" (print_tree env_feats feats) t.tree; *)
	
	let rec tree_r ccs2 cs r1 = 
	(match ccs2 with 
	| [] -> Leaf (P.bot env_vars vars) 
	| [(c,nc)] -> Node ((c,nc),Leaf (P.bot env_vars vars),r1) 
	| (c,nc)::xs -> Node ((c,nc), Leaf (P.bot env_vars vars), tree_r xs (nc::cs) r1) 
	| _ -> raise (Invalid_argument "tree_r:")) in 

	let rec tree_lj ccsj cs l1 r1 jj ccs2 = 
	(match ccsj with 
	| [] -> tree_r ccs2 cs r1 
	| [(c,nc)] -> Node ((c,nc),jj,tree_r ccs2 (nc::cs) r1) 
	| (c,nc)::xs -> Node ((c,nc),tree_lj xs (c::cs) l1 r1 jj ccs2, Leaf (P.bot env_vars vars)) ) in 

	let rec tree_l ccs1 cs l1 r1 jj ccsj ccs2 = 
	( match ccs1 with 
	| [] -> tree_lj ccsj cs l1 r1 jj ccs2 
	| [(c,nc)] -> Node ((c,nc),l1,tree_lj ccsj (nc::cs) l1 r1 jj ccs2) 
	| (c,nc)::xs -> Node ((c,nc),tree_l xs (c::cs) l1 r1 jj ccsj ccs2,Leaf (P.bot env_vars vars)) ) in 

	let rec tree2_l ccs1 cs l1 = 
	( match ccs1 with 
	| [] -> l1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),l1,Leaf (P.bot env_vars vars)) 
	| (c,nc)::xs -> Node ((c,nc),tree2_l xs (c::cs) l1,Leaf (P.bot env_vars vars)) ) in
	
	let rec tree2_r ccs2 cs r1 = 
	( match ccs2 with 
	| [] -> r1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),Leaf (P.bot env_vars vars),r1) 
	| (c,nc)::xs -> Node ((c,nc),Leaf (P.bot env_vars vars),tree2_r xs (nc::cs) r1) ) in

	let rec tree2_c ccscommon cs l1 r1 ccs1 ccs2 = 
	(match ccscommon with 
	| [] -> tree2_l ccs1 cs l1 
	| [(c,nc)] -> Node ((c,nc),tree2_l ccs1 (c::cs) l1,tree2_r ccs2 (nc::cs) r1) 
	| (c,nc)::xs -> Node ((c,nc),tree2_c xs (c::cs) l1 r1 ccs1 ccs2, Leaf (P.bot env_vars vars)) ) in 	
	
    let rec aux t cs = match t with
      | Leaf p ->
        let p' = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
		let p1 = P.fwdAssign p (l,e) in 
		if (!hasNode) then (
        	if (P.isBot p') then Leaf (P.bot env_vars vars)
        	else Leaf p1 )
		else (
			let p1' = P.fwdAssign p' (l,e) in 
			(*Format.fprintf !fmt "\n assign_feat hasNode=false: p1' %a : \n" P.print p1'; *)
			let dcs = ref [] in let ccs1 = ref [] in
			dcs:=(match domain with | None -> [] | Some domain -> P.constraints domain); 	
			List.iter (fun c -> if (not (List.mem c !dcs)) then if (not (P.isLeq p' (P.meet p' (P.inner env_feats feats [c])))) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1)) (P.constraints p1');
			(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; *)
			tree2_l !ccs1 [] (Leaf p1)
		)
      | Node ((c1,nc1),l1,r1) ->
	  	hasNode:=true; 
        let lt = aux l1 (c1::cs) in
		let rt = aux r1 (nc1::cs) in 	
		
		let pin1,pin2 = (match domain with 
          				| None -> P.inner env_feats feats (c1::cs), P.inner env_feats feats (nc1::cs) 
          				| Some domain -> P.inner env_feats feats ((c1::cs)@(P.constraints domain)), P.inner env_feats feats ((nc1::cs)@(P.constraints domain))) in 
						
		(*Format.fprintf !fmt "\n Enter assign_feat: p_in1 %a : p_in2 %a : c1: %a : nc1: %a\n" P.print pin1 P.print pin2 (C.print feats) c1 (C.print feats) nc1;*)
		if (P.isBot pin1) then (
			Node ((c1,nc1),lt,rt) ) 
		else (
		let p1,p2 = (match domain with 
          				| None -> P.fwdAssign pin1 (l,e), P.fwdAssign pin2 (l,e) 
						| Some domain -> P.meet domain (P.fwdAssign pin1 (l,e)), P.meet domain (P.fwdAssign pin2 (l,e)) ) in 
		(*Format.fprintf !fmt "\n Enter assign_feat: p_1 %a : p_2 %a :\n" P.print p1 P.print p2;*)
		let (b1,b2) = (match l with
    			| A_var l -> (C.var l c1, C.var l nc1)
				| _ -> (false,false)) in 
		(*Format.fprintf !fmt "\n Enter : b1 %b : b2 %b :\n" b1 b2;*)
		let dcs = ref [] in 
		dcs:=(match domain with | None -> [] | Some domain -> P.constraints domain);  


		if (b1 && b2) then ( 
				
			let p1p2 = P.meet p1 p2 in 
			if (P.isBot p1p2) then (
			
				let ccs1 = ref [] in let ccs2 = ref [] in let ccs_common = ref [] in 
				List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1)) (P.constraints p1);
				(*if (not (P.isBot p2)) then *)
				List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in if (List.mem (c,nc) !ccs1) then (ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) else ccs2:=(c,nc)::!ccs2)) (P.constraints p2); 
				(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;*)
				
				tree2_c !ccs_common [] lt rt !ccs1 !ccs2 
				
 			) else (
			
				(*Format.fprintf !fmt "\n here Case p1p2: %a :\n" P.print p1p2; *)
				let ccs1 = ref [] in let ccs2 = ref [] in let ccs_common = ref [] in 
				let p1pure = ref [] in let p2pure = ref [] in 
				List.iter (fun c -> if (not (List.mem c !dcs)) then let p = P.meet p1 (P.inner env_feats feats [C.negate c]) in if (not (P.isBot p)) then p1pure:=p::!p1pure) (P.constraints p1p2);
				List.iter (fun c -> if (not (List.mem c !dcs)) then let p = P.meet p2 (P.inner env_feats feats [C.negate c]) in if (not (P.isBot p)) then p2pure:=p::!p2pure) (P.constraints p1p2);
				(*List.iter (fun p -> Format.fprintf !fmt "\n p1pure: %a :\n" P.print p) !p1pure;
				List.iter (fun p -> Format.fprintf !fmt "\n p2pure: %a :\n" P.print p) !p2pure;*)

				List.iter (fun p1 -> List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1)) (P.constraints p1)) !p1pure;
				List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs_common:=(c,nc)::!ccs_common)) (P.constraints p1p2);
				List.iter (fun p2 -> List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in 
								if (List.mem (c,nc) !ccs1) then (if (not (List.mem (c,nc) !ccs_common)) then ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) 
														   else if (not (List.mem (c,nc) !ccs_common)) then  ccs2:=(c,nc)::!ccs2)) (P.constraints p2)) !p2pure; 
				(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;  *)
				let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in 
				let jj = join_t env_vars vars env_feats feats lt rt [] domain in 
				tree_l !ccs1 [] lt rt jj !ccs_common !ccs2			
			
			)
		) else (

			let ccs1 = ref [(c1,nc1)] in let ccs2 = ref [] in let ccs_common = ref [] in
			List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in if (not (List.mem (c,nc) !ccs1)) then ccs1:=(c,nc)::!ccs1)) (P.constraints p1);			
			List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in if (List.mem (c,nc) !ccs1) then (ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) else ccs2:=(c,nc)::!ccs2)) (P.constraints p2);  
			(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common; *)
			
			tree2_c !ccs_common [] lt rt !ccs1 !ccs2 			
			)  )
      | _ -> raise (Invalid_argument "fwdAssign_feat:")
    in let t = { domain = domain;
      tree = aux t.tree [];
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats } in propagateCons t
  


  (**)

  	let fwdAssign_feat_var t (l,ee) =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	let isRoot = ref true in 
	
	let rec tree_r ccs2 cs r1 = 
	(match ccs2 with 
	| [] -> Leaf (P.bot env_vars vars) 
	| [(c,nc)] -> Node ((c,nc),Leaf (P.bot env_vars vars),r1) 
	| (c,nc)::xs -> Node ((c,nc), Leaf (P.bot env_vars vars), tree_r xs (nc::cs) r1) 
	| _ -> raise (Invalid_argument "tree_r:")) in 

	let rec tree_lj ccsj cs l1 r1 jj ccs2 = 
	(match ccsj with 
	| [] -> tree_r ccs2 cs r1 
	| [(c,nc)] -> Node ((c,nc),jj,tree_r ccs2 (nc::cs) r1) 
	| (c,nc)::xs -> Node ((c,nc),tree_lj xs (c::cs) l1 r1 jj ccs2, Leaf (P.bot env_vars vars)) ) in 

	let rec tree_l ccs1 cs l1 r1 jj ccsj ccs2 = 
	( match ccs1 with 
	| [] -> tree_lj ccsj cs l1 r1 jj ccs2 
	| [(c,nc)] -> Node ((c,nc),l1,tree_lj ccsj (nc::cs) l1 r1 jj ccs2) 
	| (c,nc)::xs -> Node ((c,nc),tree_l xs (c::cs) l1 r1 jj ccsj ccs2,Leaf (P.bot env_vars vars)) ) in 

	let rec tree2_l ccs1 cs l1 = 
	( match ccs1 with 
	| [] -> l1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),l1,Leaf (P.bot env_vars vars)) 
	| (c,nc)::xs -> Node ((c,nc),tree2_l xs (c::cs) l1,Leaf (P.bot env_vars vars)) ) in
	
	let rec tree2_r ccs2 cs r1 = 
	( match ccs2 with 
	| [] -> r1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),Leaf (P.bot env_vars vars),r1) 
	| (c,nc)::xs -> Node ((c,nc),Leaf (P.bot env_vars vars),tree2_r xs (nc::cs) r1) ) in

	let rec tree2_ll ccs1 cs l1 r1 ccs2 = 
	( match ccs1 with 
	| [] -> l1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),l1,tree2_l ccs2 (nc::cs) r1) 
	| (c,nc)::xs -> Node ((c,nc),tree2_l xs (c::cs) l1,tree2_l ccs2 (nc::cs) r1) ) in

	let rec tree2_c ccscommon cs l1 r1 ccs1 ccs2 = 
	(match ccscommon with 
	| [] -> tree2_ll ccs1 cs l1 r1 ccs2
	| [(c,nc)] -> Node ((c,nc),tree2_l ccs1 (c::cs) l1,tree2_l ccs2 (nc::cs) r1) 
	| (c,nc)::xs -> Node ((c,nc),tree2_c xs (c::cs) l1 r1 ccs1 ccs2, Leaf (P.bot env_vars vars)) ) in 
	
	
    let rec aux t cs = match t with
      | Leaf p ->
        let ccs = match domain with 
          | None -> cs 
          | Some domain -> (cs@(P.constraints domain)) in 			
		let p' = P.inner env_feats feats ccs in 
		let dcs = ref [] in let ccs1 = ref [] in
		dcs:=(match domain with | None -> [] | Some domain -> P.constraints domain);		
		let cnstr = List.map (fun c -> Lincons1.extend_environment c env_vars) !dcs in (*EXTEND EVIRONMENT HERE*) 
					
		let p1 = P.meet (P.fwdAssign p (l,ee)) (P.inner env_feats feats cnstr) in
		
		let p1' = P.project p1 env_feats feats in 
 	
		List.iter (fun c -> if ((not (List.mem c !dcs)) && (not (C.isBot c))) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1)) (P.constraints p1');
		(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1;		
		Format.fprintf !fmt "\n Assign_feat_var leaf: %a : decision node: p1': %a :\n" P.print p1 P.print p1'; *)
		
		if (P.isBot p') then (Leaf (P.bot env_vars vars), true, [])
		else if (not !isRoot) then (Leaf p1, false, !ccs1) 
		else (tree2_l !ccs1 [] (Leaf p1), true, []) 
      | Node ((c1,nc1),l1,r1) ->
	  
	    let root = if (!isRoot) then (isRoot:=false; true) else false in 
	  	(*Format.fprintf !fmt "\n Enter aux Node: c1 %a :\n l1 %a :\n r1 %a :\n" (C.print feats) c1 (print_tree env_feats feats) l1 (print_tree env_feats feats) r1;  *)
        let (lt,pl1,ccs1) = aux l1 (c1::cs) in
		let (rt,pr1,ccs2) = aux r1 (nc1::cs) in 			  
	     
		let ccs1 = ref ccs1 in let ccs2 = ref ccs2 in let ccs_common = ref [] in let ccs_same = ref [] in
		
		if ((List.length !ccs2)>0) then 
		List.iter (fun (nc,c) -> if (List.mem (c,nc) !ccs1) then (ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1)) !ccs1; ccs2:=List.filter (fun (nc1,c1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs2) 
								else if (List.mem (nc,c) !ccs1) then (ccs_same:=(nc,c)::!ccs_same; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq nc c1 && C.isEq c nc1)) !ccs1; ccs2:=List.filter (fun (nc1,c1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs2) ) !ccs2; 		

		(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n 1 ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
		List.iter (fun (c,nc) -> Format.fprintf !fmt "\n 1 ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
		List.iter (fun (c,nc) -> Format.fprintf !fmt "\n 1 ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;
		List.iter (fun (c,nc) -> Format.fprintf !fmt "\n 1 ccs_same: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_same;
		Format.fprintf !fmt "\n root : %b\n" root;  *)
		(*Format.fprintf !fmt "\n lt %a :\n rt %a :\n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt; *)
		if ((List.length !ccs_same)>0) then (
			if (((List.length !ccs_common)=0) && ((List.length !ccs1)=0) && ((List.length !ccs2)=0)) then
				( let (lt,rt) = (tree_unification lt rt env_vars env_feats vars feats) in let jj = join_t env_vars vars env_feats feats lt rt [] domain in (tree2_l !ccs_same [] jj,true,[]))
				else (let ft = tree2_c !ccs_common [] lt rt !ccs1 !ccs2 in (tree2_l !ccs_same [] ft,true,[]))  ) 
		else (
		if (((List.length !ccs_common)=0) && ((List.length !ccs2)=0) && ((List.length !ccs1)=0)) then ( 
			if (pl1 && pr1) then (let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in let jj = join_t env_vars vars env_feats feats lt rt [] domain in (jj,true,[])) else (lt,true,[]))
		else if (((List.length !ccs_common)=0) && ((List.length !ccs2)=0)) then (let lt=tree2_l !ccs1 [] lt in if (pr1) then 
																												(let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in let jj = join_t env_vars vars env_feats feats lt rt [] domain in (jj,true,[])) 		
																												else (lt,true,[]) )
		else if (((List.length !ccs_common)=0) && ((List.length !ccs1)=0)) then (let rt=tree2_l !ccs2 [] rt in if (pl1) then 
																												(let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in let jj = join_t env_vars vars env_feats feats lt rt [] domain in (jj,true,[])) 		
																												else (rt,true,[]) )		
		else (let ft=tree2_c !ccs_common [] lt rt !ccs1 !ccs2 in 
			(*Format.fprintf !fmt "\n ft %a :\n" (print_tree env_feats feats) ft; *)
			(ft,true,!ccs_same) )  )
		
	(*	
		let pin1_c,pin2_c = ( match domain with 
          				| None -> (c1::cs), (nc1::cs) 
          				| Some domain -> ((c1::cs)@(P.constraints domain)), ((nc1::cs)@(P.constraints domain)) ) in 					
		
		let super_env = env_vars in (*Environment.lce env_vars env_feats in *)
		let cnstr1_node = List.map (fun c -> Lincons1.extend_environment c super_env) pin1_c in (*EXTEND EVIRONMENT HERE*) 
		let cnstr1_leaf = pl1 (*List.map (fun c -> Lincons1.extend_environment c super_env) pl1*) in (*EXTEND EVIRONMENT HERE*)
		let cnstr2_node = List.map (fun c -> Lincons1.extend_environment c super_env) pin2_c in (*EXTEND EVIRONMENT HERE*) 
		let cnstr2_leaf = pr1 (*List.map (fun c -> Lincons1.extend_environment c super_env) pr1*) in (*EXTEND EVIRONMENT HERE*)
		
 		let super_cons1 = cnstr1_node@cnstr1_leaf in 					
		let super_cons2 = cnstr2_node@cnstr2_leaf in
		let super_vars = vars(*@feats*) in 
		let super_pin1 = P.inner super_env super_vars super_cons1 in 
		let super_pin2 = P.inner super_env super_vars super_cons2 in 
		let super_p1 = P.fwdAssign super_pin1 (l,ee) in 
		let super_p2 = P.fwdAssign super_pin2 (l,ee) in 
					 
		let p1 = P.project super_p1 env_feats feats in
		let p2 = P.project super_p2 env_feats feats in 
		
		let (lt,rt) = (match lt,rt with
      			| Leaf p1, Leaf p2 -> (Leaf super_p1,Leaf super_p2)
				| Leaf p1, _ -> (Leaf super_p1,rt)
				| _, Leaf p2 -> (lt,Leaf super_p2)
				| _ -> (lt,rt) ) in 		
		
		let dcs = ref [] in 
		dcs:=(match domain with | None -> [] | Some domain -> P.constraints domain);
		
		Format.fprintf !fmt "\n Enter assign_feat_var: super_pin1 %a : super_pin2 %a : c1: %a : nc1: %a\n" P.print super_pin1 P.print super_pin2 (C.print feats) c1 (C.print feats) nc1;
		Format.fprintf !fmt "\n Enter assign_feat_var: p1 %a : p2 %a :\n" P.print p1 P.print p2;
		if ((P.isBot super_pin1)) then (
			if ((P.isBot super_pin2)) then (
			(*let ft =  Node ((c1,nc1),lt,rt) in *)
			(*let (lt,rt) = (sort_tree lt, sort_tree rt) in *)
			(*Format.fprintf !fmt "\n Enter isBot super_pin1: lt %a :\n rt %a :\n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt;*)
			let ft = (match lt,rt with
      			| Leaf p, _ when P.isBot p -> rt
				| _, Leaf p when P.isBot p -> lt
				| _, _ -> let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in join_t env_vars vars env_feats feats lt rt [] domain ) in
			(*let (lt,rt) = tree_unification lt rt env_vars env_feats vars feats in 
			Format.fprintf !fmt "\n after uification: lt %a :\n rt %a :\n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt;
			let ft = join_t env_vars vars env_feats feats lt rt [] domain (*(match lt with
      			| Leaf p -> if (P.isBot p) then rt else lt 
				| _ -> lt ) *) in  *)		
			(*Format.fprintf !fmt "\n Enter isBot super_pin1 & super_pin2: ft %a :\n" (print_tree env_feats feats) ft;*)
			(ft,pl1@pr1) ) else ( 		
				let ccs2 = ref [] in 
				List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs2:=(c,nc)::!ccs2)) (P.constraints p2);
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
				let ft' = tree2_l !ccs2 [] rt in 
				
				let pc1 = P.inner super_env super_vars [Lincons1.extend_environment c1 super_env] in 
				let super_pc1 = P.fwdAssign pc1 (l,ee) in
				let c1' = List.hd (P.constraints (P.project super_pc1 env_feats feats)) in
				let nc1' = C.negate c1' in			
				Format.fprintf !fmt "\n Enter isBot super_pin1: c1': %a : nc1': %a\n" (C.print feats) c1' (C.print feats) nc1';
				let ft = Node ((c1',nc1'),lt,rt) in 
				Format.fprintf !fmt "\n Enter isBot super_pin1: ft %a :\n" (print_tree env_feats feats) ft; 
				Format.fprintf !fmt "\n Enter isBot super_pin1: ft' %a :\n" (print_tree env_feats feats) ft';
				(ft',pl1@pr1) ) 
		)	
			else ( 
		
		let (b1,b2) = (match l with
    			| A_var l -> (C.var l c1, C.var l nc1)
				| _ -> (false,false)) in 
		Format.fprintf !fmt "\n Enter : b1 %b : b2 %b :\n" b1 b2;
  		
		
		if (b1 && b2) then ( 
			
			let p1p2 = P.meet p1 p2 in 
			if (P.isBot p1p2) then (
				let ccs1 = ref [] in let ccs2 = ref [] in let ccs_common = ref [] in
				(*List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in dcs:=c::nc::!dcs; if (C.isLeq nc c) then ccs1:=(c,nc)::!ccs1 else ccs1:=(nc,c)::!ccs1)) (P.constraints p1); 		*)
				(*if (not (P.isBot p1)) then *)
				List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1)) (P.constraints p1);
				if (not (P.isBot p2)) then List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in if (List.mem (c,nc) !ccs1) then (ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) else ccs2:=(c,nc)::!ccs2)) (P.constraints p2); 
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
				List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;
				
				(*Format.fprintf !fmt "\n assign_feat_var: lt %a : rt %a :\n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt;*)
				let ft = tree2_c !ccs_common [] lt rt !ccs1 !ccs2 in (*tree_l !ccs1 [] (Leaf (P.bot env_vars vars)) rt lt !ccs_common !ccs2 in *)
				(*Format.fprintf !fmt "\n result: ft %a :\n" (print_tree env_feats feats) ft;*)
				(ft,pl1@pr1)
				
		) else ( (*Case when P.meet p1 p2 is not bottom*)
			Format.fprintf !fmt "\n Case p1p2: %a :\n" P.print p1p2; 
			let ccs1 = ref [] in let ccs2 = ref [] in let ccs_common = ref [] in 
			let p1pure = ref [] in let p2pure = ref [] in 
			List.iter (fun c -> if (not (List.mem c !dcs)) then let p = P.meet p1 (P.inner env_feats feats [C.negate c]) in if (not (P.isBot p)) then p1pure:=p::!p1pure) (P.constraints p1p2);
			List.iter (fun c -> if (not (List.mem c !dcs)) then let p = P.meet p2 (P.inner env_feats feats [C.negate c]) in if (not (P.isBot p)) then p2pure:=p::!p2pure) (P.constraints p1p2);
			(*List.iter (fun c -> Format.fprintf !fmt "\n cs1not: c: %a \n" (C.print feats) c) !cs1not;*)
			List.iter (fun p -> Format.fprintf !fmt "\n p1pure: %a :\n" P.print p) !p1pure;
			List.iter (fun p -> Format.fprintf !fmt "\n p2pure: %a :\n" P.print p) !p2pure;

			List.iter (fun p1 -> List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs1:=(c,nc)::!ccs1 )) (P.constraints p1)) !p1pure;
			List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in ccs_common:=(c,nc)::!ccs_common)) (P.constraints p1p2);
			List.iter (fun p2 -> List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in 
								if (List.mem (c,nc) !ccs1) then (if (not (List.mem (c,nc) !ccs_common)) then ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) 
														   else if (not (List.mem (c,nc) !ccs_common)) then  ccs2:=(c,nc)::!ccs2)) (P.constraints p2)) !p2pure; 
														   
			ccs1:=List.sort (fun (c1,nc1) (c2,nc2) -> if (C.isLeq c1 c2) then 1 else -1) !ccs1;												   
			ccs_common:=List.sort (fun (c1,nc1) (c2,nc2) -> if (C.isLeq c1 c2) then 1 else -1) !ccs_common;		
														   
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;
			
			let cnstr1_node = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints (List.hd !p1pure)) in 
			let cnstr2_node = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints (List.hd !p2pure)) in 
			let cnstr_common_node = List.map (fun c -> Lincons1.extend_environment c super_env) (P.constraints p1p2) in 
			
			let p1_leaf = P.meet super_p1 (P.inner super_env super_vars cnstr1_node) in (*P.project (P.meet super_p1 (P.inner super_env super_vars cnstr1_node)) env_vars vars in *)
			let p2_leaf = P.meet super_p2 (P.inner super_env super_vars cnstr2_node) in (*P.project (P.meet super_p2 (P.inner super_env super_vars cnstr2_node)) env_vars vars in *)
			let p1p2_leaf = P.meet super_p2 (P.inner super_env super_vars cnstr_common_node) in (*P.project (P.meet super_p2 (P.inner super_env super_vars cnstr_common_node)) env_vars vars in *)
			
			let (lt,rt,jj) = (match lt,rt with
      			| Leaf p1, Leaf p2 -> (Leaf p1_leaf,Leaf p2_leaf,Leaf p1p2_leaf)
				| _ -> (lt,rt,join_t env_vars vars env_feats feats lt rt [] domain) ) in 
			
			(*let jj = join_t env_vars vars env_feats feats lt rt [] domain in  *)
			Format.fprintf !fmt "\n lt: %a : \n rt: %a : \n jj: %a \n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt (print_tree env_feats feats) jj;
			let ft = tree_l !ccs1 [] lt rt jj !ccs_common !ccs2 in 
			Format.fprintf !fmt "\n result ft : %a : \n" (print_tree env_feats feats) ft;
			(ft,pl1@pr1)
			
		)		
		) else (		
			Format.fprintf !fmt "\n Enters here! \n";
			let ccs1 = ref [(c1,nc1)] in let ccs2 = ref [] in let ccs_common = ref [] in
			if (not (P.isBot p1)) then List.iter (fun c -> if (not (List.mem c !dcs)) then (let nc = C.negate c in if (not (List.mem (c,nc) !ccs1)) then ccs1:=(c,nc)::!ccs1)) (P.constraints p1);			
			if (not (P.isBot p2)) then List.iter (fun nc -> if (not (List.mem nc !dcs)) then (let c = C.negate nc in if (List.mem (c,nc) !ccs1) then (ccs_common:=(c,nc)::!ccs_common; ccs1:=List.filter (fun (c1,nc1) -> not (C.isEq c c1 && C.isEq nc nc1) ) !ccs1) else ccs2:=(c,nc)::!ccs2)) (P.constraints p2);  
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs1; 
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs2: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs2;
			List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs_common: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !ccs_common;
			
			Format.fprintf !fmt "\n lt: %a : \n rt: %a : \n" (print_tree env_feats feats) lt (print_tree env_feats feats) rt;
			let ft = tree2_c !ccs_common [] lt rt !ccs1 !ccs2 in Format.fprintf !fmt "\n ft: %a :\n" (print_tree env_feats feats) ft; 
			(ft,pl1@pr1)
		
			(*(Node ((c1,nc1),lt,rt),pl1@pr1)*) )  )    *)
      | _ -> raise (Invalid_argument "fwdAssign_feat_var:")  
    in 
	let (tt,p,ccs) = aux t.tree [] in (*Format.fprintf !fmt "\n returns: %a : \n" (print_tree env_feats feats) tt; *)
	(*let t' = propagateCons env_feats feats env_vars vars tt [] in Format.fprintf !fmt "\n after propagate: %a : \n" (print_tree env_feats feats) t'; 
	let t'' = sort_tree tt in Format.fprintf !fmt "\n after sort: %a : \n" (print_tree env_feats feats) t''; *)
	{ domain = domain;
      tree = tt; (*propagateCons env_feats feats env_vars vars tt [];*)
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }



  (**)


  let bwdAssign t e = 
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let rec aux t cs = match t with
      | Leaf p ->
        let p' = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        if (P.isBot p') then Leaf (P.bot env_vars vars)
        else
          Leaf (P.bwdAssign p e)
      | Node ((c1,nc1),l1,r1) ->
        let l = aux l1 (c1::cs) in
		let r = aux r1 (nc1::cs) in
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "bwdAssign:")
    in { domain = domain;
      tree = aux t.tree [];
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }

  (**)
  
  
  let rec filter t e =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let rec aux t cs = match t with
      | Leaf p ->
        let p' = match domain with 
          | None -> P.inner env_feats feats cs 
          | Some domain -> 
            P.inner env_feats feats (cs@(P.constraints domain)) in
        if (P.isBot p') then Leaf (P.bot env_vars vars)
        else
          Leaf (P.filter p e (* forall leafs x: widen ( P1(x), P2(x)) *))
      | Node ((c1,nc1),l1,r1) ->
        let l = aux l1 (c1::cs) in
		let r = aux r1 (nc1::cs) in
		Node ((c1,nc1),l,r)
      | _ -> raise (Invalid_argument "fwdAssign:")
    in { domain = domain;
      tree = aux t.tree [];
      env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }


  let rec filter_config t e =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	(* THIS IS RESTRICT FUNCTION from the paper *)
	let rec aux t bs (*constraints in expression e*) cs (*constraints collected up to the node*) =
	  let bcs = P.inner env_feats feats cs in 
      match bs with
      | [] ->
        (match t with
         | Leaf p -> let cs1 = List.map (fun c -> Lincons1.extend_environment c env_vars) cs in 
		 			 let bcs1 = P.inner env_vars vars cs1 in 
					 Leaf (P.meet p bcs1)
         | Node((c,nc),l,r) ->
           let bc = P.inner env_feats feats [c] in  (* Environmet features *)
           if (P.isLeq bcs bc)
           then (* c is redundant *) aux l bs cs
           else (* c is not redundant *)
             (* if (B.isBot (B.meet bc bcs))
                then (* c is conflicting *) aux r bs cs
                else *)
             let l = aux l bs (c::cs) in
             let r = aux r bs (nc::cs) in
			 Node((c,nc),l,r))
      | (x,nx)::xs ->
	    (*C.print feats !fmt x; Format.fprintf !fmt "\n config-filter %b\n" (Lincons1.get_typ x = Lincons1.EQ); *)
        let bx = P.inner env_feats feats [x] in
        if (P.isLeq bcs bx)
        then (* x is redundant *) aux t xs cs
        else (* x is not redundant *)
        if (P.isBot (P.meet bx bcs))
        then (* x is conflicting *) Leaf (P.bot env_vars vars) (* This introduces a NIL leaf to the tree *)
        else
        if (C.isLeq nx x) || (Lincons1.get_typ x = Lincons1.EQ)
        then (* x is normalized *)
          (match t with
           | Node ((c,nc),l,r) when (C.isEq c x) (* c = x *) ->
             let l = aux l xs (c::cs) in
			 Node((c,nc),l,Leaf (P.bot env_vars vars))
           | Node ((c,nc),l,r) when (C.isLeq c x) (* c < x *) ->
             let bc = P.inner env_vars vars [c] in
             if (P.isLeq bcs bc)
             then (* c is redundant *) aux l bs cs
             else (* c is not redundant *)
               (* if (B.isBot (B.meet bc bcs))
                  then (* c is conflicting *) aux r bs cs
                  else *)
               let l = aux l bs (c::cs) in
               let r = aux r bs (nc::cs) in
			   Node((c,nc),l,r)
           | _ ->
             let l = aux t xs (x::cs) in
			 Node((x,nx),l,Leaf (P.bot env_vars vars)) )
        else (* x is not normalized *)
          (match t with
           | Node ((c,nc),l,r) when (C.isEq c nx) (* c = nx *) ->
             let r = aux r xs (nc::cs) in
			 Node((c,nc),Leaf (P.bot env_vars vars),r)
           | Node ((c,nc),l,r) when (C.isLeq c nx) (* c < nx *) ->
             let bc = P.inner env_vars vars [c] in
             if (P.isLeq bcs bc)
             then (* c is redundant *) aux l bs cs
             else (* c is not redundant *)
               (* if (B.isBot (B.meet bc bcs))
                  then (* c is conflicting *) aux r bs cs
                  else *)
               let l = aux l bs (c::cs) in
               let r = aux r bs (nc::cs) in
			   Node((c,nc),l,r)
           | _ ->
             let r = aux t xs (x::cs) in
			 Node((nx,x),Leaf (P.bot env_vars vars),r) )
    in
    match e with
    | A_TRUE | A_MAYBE -> { domain = domain; tree = t.tree; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }
    | A_FALSE -> { domain = domain; tree = Leaf (P.bot env_vars vars); env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }
	| A_bvar v -> 	let cons = Lincons1.make (Linexpr1.make env_feats) Lincons1.EQ in
  					Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string v.varId)) |] (Some (Coeff.s_of_int (-1))); 
					let neg_cons = Lincons1.make (Linexpr1.make env_feats) Lincons1.EQ in
  					Lincons1.set_array neg_cons [| ((Coeff.s_of_int 1), (Var.of_string v.varId)) |] (Some (Coeff.s_of_int 0)); 
					(*C.print feats !fmt cons; C.print feats !fmt neg_cons; Format.fprintf !fmt "\n config-filter b-var %d\n" cst;*)
					let bs = if (!AbstractSyntax.cst=1) then [(cons,neg_cons)] else [(neg_cons,cons)] in AbstractSyntax.cst:=1; 
					{ domain = domain; tree = aux t.tree bs []; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }
    | A_bunary (o,e) ->
      (match o with
       | A_NOT -> let (e, _) = negBExp e in filter_config t e )
    | A_bbinary (o,(e1,_),(e2,_)) ->
      let t1 = filter_config t e1 and t2 = filter_config t e2 in
      (match o with
       | A_AND -> meet t1 t2
       | A_OR -> join t1 t2)
    | A_rbinary (_,_,_) ->
      let bp = match domain with
        | None -> P.inner env_feats feats []
        | Some domain -> P.inner env_feats feats (P.constraints domain)
      in
	  (*let pp = P.filter bp e in Format.fprintf !fmt "\n here filter %a %a" P.print pp bExp_print_aux e;*)
      let bs = List.map (fun c -> let nc = C.negate c in (c,nc)) (P.constraints (P.filter bp e)) in
      let bs = List.sort L.compare bs in
      { domain = domain; tree = aux t.tree bs []; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }
 


  let rec filter_general t e =
    let domain = t.domain in 
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	let toSort = ref false in 
	
	let rec tree2_l ccs1 cs l1 = 
	( match ccs1 with 
	| [] -> l1 (*Leaf (P.bot env_vars vars) *)
	| [(c,nc)] -> Node ((c,nc),l1,Leaf (P.bot env_vars vars)) 
	| (c,nc)::xs -> Node ((c,nc),tree2_l xs (c::cs) l1,Leaf (P.bot env_vars vars)) ) in  	
	
	let rec aux t e cs =
        (match t with
         | Leaf p -> 
		 			let ccs = match domain with | None -> cs | Some domain -> cs@(P.constraints domain) in 
					let b = P.inner env_feats feats ccs in 
			 		let cnstr = List.map (fun c -> Lincons1.extend_environment c env_vars) ccs in (*EXTEND EVIRONMENT HERE*) 
			 		let super_p = P.meet p (P.inner env_feats feats cnstr) in 
			 		let super_p' = P.filter super_p e in 
					 
					let p' = P.project super_p' env_feats feats in 
					(*Format.fprintf !fmt "\n General filter super_p' leaf: %a : p' node: %a \n" P.print super_p' P.print p'; *)
					if (P.isLeq b p') then (Leaf super_p') (*Format.fprintf !fmt "\n p'' is redundant \n" *)
					else ( 	
							let cs = ref [] in 
							List.iter (fun c -> if ((not (List.mem c ccs)) && (not (C.isBot c))) then (let nc = C.negate c in cs:=(c,nc)::!cs)) (P.constraints p');
							let ft2 = tree2_l !cs [] (Leaf super_p') in 
							(*List.iter (fun (c,nc) -> Format.fprintf !fmt "\n ccs1: c: %a : nc: %a \n" (C.print feats) c (C.print feats) nc) !cs;*)
							(*Format.fprintf !fmt "\n ft1: %a : \n ft2: %a : \n" (print_tree env_feats feats) ft1 (print_tree env_feats feats) ft2;*)
							ft2
						  )
        | Node ((c1,nc1),l1,r1) ->
        			let l = aux l1 e (c1::cs) in
					let r = aux r1 e (nc1::cs) in
					Node ((c1,nc1),l,r)							
		   )
    in
		let t = aux t.tree e [] in 
		(*Format.fprintf !fmt "\n after Sort: %a : \n" (print_tree env_feats feats) t';*)
      { domain = domain; tree = t; env_vars = env_vars; env_feats = env_feats; vars = vars; feats = feats }
 







  let rec print_tree fmt env_feats feats t =
    let rec aux t cs =
      match t with
      | Leaf p ->
        let b = P.inner env_feats feats cs in
        if P.isBot b then () else Format.fprintf fmt "[%a ? %a] " P.print b P.print p
      | Node((c,nc),l,r) -> aux r (nc::cs); aux l (c::cs)
    in aux t []

  (**)

  let compress t =
    let domain = t.domain in
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let rec aux t cs =
      match t with
      | Leaf _ -> t
      | Node((c,nc),l,r) ->
        let l = aux l (c::cs) in
        let r = aux r (nc::cs) in
		(*print_string "in compress, before match \n";
		print_string " node: "; C.print feats !fmt c; print_string " left: "; print_tree !fmt env_feats feats l; print_string " right: "; print_tree !fmt env_feats feats r; *)
        match l,r with
        | Leaf f1,Leaf f2 when (P.isBot f1) && (P.isBot f2) -> Leaf f1
        | Leaf f1,Leaf f2 when (P.isLeq f1 f2) && (P.isLeq f2 f1) -> print_string "in compress, eq leaves \n"; P.print !fmt f1; P.print !fmt f2; Leaf f1		
        | Leaf f1,Leaf f2 ->
		  (*print_string "in compress, leaves \n"; P.print !fmt f1; P.print !fmt f2; *)
          let b1 = match domain with | None -> P.inner env_feats feats (c::cs) | Some domain -> P.inner env_feats feats ((c::cs)@(P.constraints domain)) in
          if (P.isBot b1) then Leaf f2 else
            let b2 = match domain with | None -> P.inner env_feats feats (nc::cs) | Some domain -> P.inner env_feats feats ((nc::cs)@(P.constraints domain)) in
            if (P.isBot b2) then Leaf f1 else Node((c,nc),l,r)
        (*| Leaf f1,Node((c2,nc2),Leaf f2,r2) when (P.isBot f1) && (P.isBot f2) -> aux (Node((c2,nc2),Leaf f1,r2)) cs
        | Leaf f1,Node((c2,nc2),Leaf f2,r2) when (P.isLeq f1 f2) && (P.isLeq f2 f1) -> aux (Node((c2,nc2),Leaf f1,r2)) cs *)
          (* e.g., NODE( y >= 2, LEAF 3y+2, NODE( y >= 1, LEAF 5, LEAF 1 )) *)
        | Leaf f1,Node((c2,nc2),Leaf f2,r2) when (P.isLeq f1 f2) && (P.isLeq f2 f1) && (C.isLeq c c2) -> Node((c2,nc2),Leaf f1,r2)
		| Node((c1,nc1),l1,Leaf f1),Leaf f2 when (P.isLeq f1 f2) && (P.isLeq f2 f1) && (C.isLeq c1 c) -> Node((c1,nc1),l1,Leaf f1)
        | Node((c1,nc1),Leaf f1,Leaf f2),Node((c2,nc2),Leaf f3,Leaf f4) when (C.isEq c1 c2) && (P.isLeq f1 f3) && (P.isLeq f2 f4) && (P.isLeq f3 f1) && (P.isLeq f4 f2) -> Node((c1,nc1),Leaf f1,Leaf f2)	
        | _ -> Node((c,nc),l,r)
    in { domain = domain; tree = aux t.tree [];       
	  env_vars = env_vars;
	  env_feats = env_feats;
      vars = vars;
	  feats = feats }


  let rec print fmt t =
    let domain = t.domain in
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
    let print_domain fmt domain =
      match domain with
      | None -> ()
      | Some domain -> P.print fmt domain
    in
    let rec aux t cs =
      match t with
      | Leaf p ->
        let b = match domain with | None -> P.inner env_feats feats cs | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
        if P.isBot b then () else Format.fprintf fmt "[%a ? %a] " P.print b P.print p
      | Node((c,nc),l,r) -> aux r (nc::cs); aux l (c::cs)
    (* in aux t.tree []; Format.fprintf fmt "\nDOMAIN = {%a}%a\n" print_domain domain (print_tree vars) t.tree *)
    (* Format.fprintf fmt "\nDOMAIN = {%a}%a\n" print_domain domain (print_tree vars) t.tree; *)
    in aux t.tree []


  let analyzeAss t1 t2 t =
    let domain = t.domain in
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	let res = ref 0 in 
		
    let rec aux t1 t2 t cs = 
      match t1,t2,t with
      | Leaf p1,Leaf p2,Leaf p ->
        let b = match domain with | None -> P.inner env_feats feats cs | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in 
		(* Format.fprintf !fmt "LEaf: b - %a ! p - %a ; res - %d \n" P.print b P.print p !res; *) 
		if (not (P.isBot b)) then 
        (if ((P.isBot p) && ((!res==0) || (!res==5))) then (res:=5;) 
		else (if ((P.isBot p) && (!res!=0) && (!res!=5)) then (res:=4;) 
			else (if ((P.isLeq p p1) && ((!res==0) || (!res==1))) then (res:=1;) 
				else (if ((P.isLeq p p1) && (!res!=0) && (!res!=1)) then (res:=4;) 
		      		else (if (P.isBot p1) && (P.isLeq p p2) && ((!res==0) || (!res==2)) then (res:=2;)
			        	else (if ((P.isBot p1) && (P.isLeq p p2) && (!res!=0) && (!res!=2)) then (res:=4;) 
					      	else (if ((!res==0) || (!res==3)) then (res:=3;) else (if ((!res!=0) && (!res!=3)) then (res:=4;)))))))))
      | Node((c1,nc1),l1,r1),Node((c2,nc2),l2,r2),Node((c,nc),l,r) when (C.isEq c c1) && (C.isEq c c2)  -> aux r1 r2 r (nc::cs); aux l1 l2 l (c::cs) 
	  (*| _ -> (res:=4;) *)
    in 
	aux t1.tree t2.tree t.tree [];
	!res


  let print_assert fmt t1 t2 t =
    let domain = t.domain in
    let env_vars = t.env_vars in
    let env_feats = t.env_feats in	
    let vars = t.vars in 
	let feats = t.feats in 
	
    let rec aux t1 t2 t cs = 
      match t1,t2,t with
      | Leaf p1,Leaf p2,Leaf p ->
        let b = match domain with | None -> P.inner env_feats feats cs | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in 
		if (not (P.isBot b)) then 
		(if (P.isBot p) then Format.fprintf fmt "Unreachable: %a ? ; " P.print b 
        else (if (P.isLeq p p1) then Format.fprintf fmt "CORRECT: %a ? ; " P.print b 
		      else (if (P.isBot p1) && (P.isLeq p p2) then Format.fprintf fmt "ERROR: %a ? ; " P.print b (*P.print p1*)
			        else (Format.fprintf fmt "DontKnow: %a ? ; " P.print b (*P.print p1*)))))
      | Node((c1,nc1),l1,r1),Node((c2,nc2),l2,r2),Node((c,nc),l,r) when (C.isEq c c1) && (C.isEq c c2)  -> aux r1 r2 r (nc::cs); aux l1 l2 l (c::cs) 
	  | _ -> ()
    in 	
	
    (*let rec aux t cs =
      match t with
      | Leaf p ->
        let b = match domain with | None -> P.inner env_feats feats cs | Some domain -> P.inner env_feats feats (cs@(P.constraints domain)) in
        if P.isBot b then () else (if (P.isBot p) then Format.fprintf fmt "CORRECT: %a ? ; " P.print b else (Format.fprintf fmt "ERROR: %a ? %a;" P.print b P.print p))
      | Node((c,nc),l,r) -> aux r (nc::cs); aux l (c::cs)*)
	Format.fprintf fmt "{ "; 
	aux t1.tree t2.tree t.tree [];
	Format.fprintf fmt " }"
    

end

(** Decision Tree-based domain parameterized by the boxes numerical abstract domain. *)
 module DTB = MakeDTDomain(Numerical.B)

(** Decision Tree-based domain parameterized by the octagons abstract domain. *)
module DTO = MakeDTDomain(Numerical.O)

(** Decision Tree-based domain parameterized by the polyhedra abstract domain. *)
module DTP = MakeDTDomain(Numerical.P)
