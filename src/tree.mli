



exception Tree_add_already_in


module type Key =
  sig
    type t
    val compare : t -> t -> int
  end


      
module type Tree =
  sig
    type key
    type +'a tree  
    val create : unit  -> 'a tree
    val is_empty : 'a tree -> bool
    val find : key -> 'a tree -> 'a
    val mem  : key -> 'a tree -> bool
    val add  : key -> 'a -> 'a tree -> 'a tree
    val remove :  key -> 'a tree -> 'a tree
    val findf_leq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_geq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_all_geq :  (key -> 'a -> 'b list) -> key -> 'a tree -> 'b list 
    val findf_all     :  (key -> 'a -> 'b list)  -> 'a tree -> 'b list 
(*    val findf_all_leq :  ('a -> 'b list) -> key -> 'a tree -> 'b list *)
  end

module Make(Key:Key): (Tree with type key=Key.t) 
