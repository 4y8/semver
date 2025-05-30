(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend
open Domains

(* parse filename *)
let doit filename =
  let prog = FileParser.parse_file filename in
  let cfg = Tree_to_cfg.prog prog in
  if !Options.verbose then
    Format.printf "%a" ControlFlowGraphPrinter.print_cfg cfg ;
  ControlFlowGraphPrinter.output_dot !Options.cfg_out cfg ;
  let module D =
    (val
    (match !Options.domain with
    | "interval" ->
      (module (Non_relational.NonRelational
                (struct let support = cfg.cfg_vars end)
                (Interval.Interval)) : Domain.DOMAIN)
    | "constants" ->
      (module (Non_relational.NonRelational
                (struct let support = cfg.cfg_vars end)
                (Constant.Constant)))
    | "product" ->
      (module (Non_relational.NonRelational
                (struct let support = cfg.cfg_vars end)
                (Reduced_product.RedProd)))
    | "sign" ->
      (module (Non_relational.NonRelational
                (struct let support = cfg.cfg_vars end)
                (Sign.Sign)))
    | "congruence" ->
      (module (Non_relational.NonRelational
                (struct let support = cfg.cfg_vars end)
                (Congruence.Congruence)))
    | "polyhedral" ->
      (module (Polyhedral.Polyhedral
                (struct let support = cfg.cfg_vars end) ()))
    | _ -> failwith "unknown domain"))
  in
  Iterator.iterate cfg (module D)

(* parses arguments to get filename *)
let main () =
  let _ = Options.init () in
  doit !Options.file

let _ = main ()
