(***************************************************)
(*                                                 *)
(*                 DTDomain.ml                    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Partition
open ItoA

module type DTDomain =
sig

  module P : PARTITION

  type t

  val bot : ?domain:P.t -> Environment.t -> Environment.t -> var list -> var list -> t
  val top : ?domain:P.t -> Environment.t -> Environment.t -> var list -> var list -> t
  val initial : ?domain:P.t -> P.t -> Environment.t -> Environment.t -> var list -> var list -> t
  
  val isLeq : t -> t -> bool
  val join : t -> t -> t
  val join_while : t -> t -> t  
  val meet : t -> t -> t
  val widen : t -> t -> t

  val fwdAssign : t -> aExp * aExp -> t
  val fwdAssign_var : t -> aExp * aExp -> t 
  val fwdAssign_feat : t -> aExp * aExp -> t
  val fwdAssign_feat_var : t -> aExp * aExp -> t
  
  val bwdAssign : t -> aExp * aExp -> t

  val filter : t -> bExp -> t
  val filter_config : t -> bExp -> t  
  val filter_general : t -> bExp -> t

  val compress : t -> t
  val sorting_tree : t -> t
  val print : Format.formatter -> t -> unit
  val print_assert : Format.formatter -> t -> t -> t -> unit
  val analyzeAss : t -> t -> t -> int  
  val print_graphviz_dot : Format.formatter -> t -> unit
  val propagateCons : t -> t

end
