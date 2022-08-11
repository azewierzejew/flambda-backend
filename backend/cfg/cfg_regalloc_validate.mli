[@@@ocaml.warning "+a-4-30-40-41-42"]

module Description : sig
  type t

  val create : Cfg_with_layout.t -> t
end

val verify : Description.t -> Cfg_with_layout.t -> Cfg_with_layout.t
