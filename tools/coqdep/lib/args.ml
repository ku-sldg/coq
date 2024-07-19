(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  { boot : bool
  ; sort : bool
  ; vos : bool
  ; noglob : bool
  ; coqproject : string option
  ; ml_path : string list
  ; vo_path : (bool * bool * string * string) list
  ; dyndep : string
  ; meta_files : string list
  ; files : string list
  }

let make () =
  { boot = false
  ; sort = false
  ; vos = false
  ; noglob = false
  ; coqproject = None
  ; ml_path = []
  ; vo_path = []
  ; dyndep = "both"
  ; meta_files = []
  ; files = []
  }


let usage () =
  let open Printf in
  eprintf " usage: coqdep [options] <filename>+\n";
  eprintf " options:\n";
  eprintf "  -boot : For coq developers, prints dependencies over coq library files (omitted by default).\n";
  eprintf "  -sort : output the given file name ordered by dependencies\n";
  eprintf "  -noglob | -no-glob : \n";
  eprintf "  -noinit : currently no effect\n";
  eprintf "  -f file : read -I, -Q, -R and filenames from _CoqProject-formatted file.\n";
  eprintf "  -I dir : add (non recursively) dir to ocaml path\n";
  eprintf "  -L dir logname : build and import 'dir' recursively to coq load path under logical name logname (builds with a _CoqProject file in 'dir')\n";
  eprintf "  -R dir logname : add and import dir recursively to coq load path under logical name logname\n";
  eprintf "  -Q dir logname : add (recursively) and open (non recursively) dir to coq load path under logical name logname\n";
  eprintf "  -vos : also output dependencies about .vos files\n";
  eprintf "  -exclude-dir dir : skip subdirectories named 'dir' during -R/-Q search\n";
  eprintf "  -coqlib dir : set the coq standard library directory\n";
  eprintf "  -dyndep (opt|byte|both|no|var) : set how dependencies over ML modules are printed\n";
  eprintf "  -m META : resolve plugins names using the META file\n";
  exit 1

let parse st args =
  let rec parse st =
    function
    | "-boot" :: ll -> parse { st with boot = true } ll
    | "-sort" :: ll -> parse { st with sort = true } ll
    | "-vos" :: ll -> parse { st with vos = true } ll
    | ("-noglob" | "-no-glob") :: ll -> parse { st with noglob = true } ll
    | "-noinit" :: ll -> (* do nothing *) parse st ll
    | "-f" :: f :: ll -> parse { st with coqproject = Some f } ll
    | "-I" :: r :: ll -> parse { st with ml_path = r :: st.ml_path } ll
    | "-I" :: [] -> usage ()
    | "-L" :: r :: ln :: ll -> parse { st with vo_path = (true, false, r, ln) :: st.vo_path } ll
    | "-R" :: r :: ln :: ll -> parse { st with vo_path = (false, true, r, ln) :: st.vo_path } ll
    | "-Q" :: r :: ln :: ll -> parse { st with vo_path = (false, false, r, ln) :: st.vo_path } ll
    | "-R" :: ([] | [_]) -> usage ()
    | "-exclude-dir" :: r :: ll -> System.exclude_directory r; parse st ll
    | "-exclude-dir" :: [] -> usage ()
    | "-coqlib" :: r :: ll -> Boot.Env.set_coqlib r; parse st ll
    | "-coqlib" :: [] -> usage ()
    | "-dyndep" :: dyndep :: ll -> parse { st with dyndep } ll
    | "-m" :: m :: ll -> parse { st with meta_files = st.meta_files @ [m]} ll
    | ("-h"|"--help"|"-help") :: _ -> usage ()
    | opt :: ll when String.length opt > 0 && opt.[0] = '-' ->
      Warning.give "unknown option %s" opt;
      parse st ll
    | f :: ll -> parse { st with files = f :: st.files } ll
    | [] -> st
  in
  let st = parse st args in
  { st with
    ml_path = List.rev st.ml_path
  ; vo_path = List.rev st.vo_path
  ; files = List.rev st.files
  }
