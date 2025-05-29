open Frontend
open AbstractSyntax
open Apron
open ControlFlowGraph

module NonRelational (V : Domain.VARS) : Domain.DOMAIN = struct
  type t = Polka.loose Polka.t Abstract1.t
  let init =
    let manager = Polka.manager_alloc_loose () in
    let vars = List.map
        (fun {var_id; _} -> Apron.Var.of_string @@ string_of_int var_id)
        V.support |> Array.of_list in
    
    ()
end
