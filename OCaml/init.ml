(* ========================================================================= *)
(* Initialize theorem proving example code.                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#use "topfind";;
#require "num-top";;
#require "camlp5";;

#load "camlp5o.cma";;

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;
#use "initialization.ml";;
#use "Quotexpander.ml";;
