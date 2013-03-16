val assign_map_counter : int ref
module type KeyEl =
  sig
    type t
    type e
    val compare : t -> t -> int
    val assign_fast_key : e -> int -> unit
    val assign_db_id : e -> int -> unit
  end
module Make :
  functor (MKey : KeyEl) ->
    sig
      type key = MKey.t
      type e = MKey.e
      module M :
        sig
          type key = MKey.t
          type 'a t = 'a Map.Make(MKey).t
          val empty : 'a t
          val is_empty : 'a t -> bool
          val mem : key -> 'a t -> bool
          val add : key -> 'a -> 'a t -> 'a t
          val singleton : key -> 'a -> 'a t
          val remove : key -> 'a t -> 'a t
          val merge :
            (key -> 'a option -> 'b option -> 'c option) ->
            'a t -> 'b t -> 'c t
          val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
          val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
          val iter : (key -> 'a -> unit) -> 'a t -> unit
          val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
          val for_all : (key -> 'a -> bool) -> 'a t -> bool
          val exists : (key -> 'a -> bool) -> 'a t -> bool
          val filter : (key -> 'a -> bool) -> 'a t -> 'a t
          val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
          val cardinal : 'a t -> int
          val bindings : 'a t -> (key * 'a) list
          val min_binding : 'a t -> key * 'a
          val max_binding : 'a t -> key * 'a
          val choose : 'a t -> key * 'a
          val split : key -> 'a t -> 'a t * 'a option * 'a t
          val find : key -> 'a t -> 'a
          val map : ('a -> 'b) -> 'a t -> 'b t
          val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
        end
      type assign_map = {
        mutable map : e M.t;
        name : string;
        map_id : int;
        mutable key_counter : int;
      }
      type t = assign_map
      val create_name : string -> assign_map
      val get_name : assign_map -> string
      val get_map_id : assign_map -> int
      val mem : assign_map -> M.key -> bool
      val find : assign_map -> M.key -> e
      val size : assign_map -> int
      val fold : (M.key -> e -> 'a -> 'a) -> assign_map -> 'a -> 'a
      val iter : (M.key -> e -> unit) -> assign_map -> unit
      val add : assign_map -> M.key -> e -> e
      val remove : assign_map -> M.key -> unit
      val to_stream :
        'a Lib.string_stream ->
        ('a Lib.string_stream -> e -> unit) -> string -> assign_map -> unit
      val out :
        (out_channel Lib.string_stream -> e -> unit) ->
        string -> assign_map -> unit
      val to_string :
        (Buffer.t Lib.string_stream -> e -> unit) ->
        string -> assign_map -> string
      val get_key_counter : assign_map -> int
    end
