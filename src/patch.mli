open Typegist

type 'a t

val empty : 'a t
(** The empty patch *)

val join : 'a t -> 'a t -> 'a t
(** Combines two patches into one. *)

val diff : 'a Type.Gist.t -> 'a -> 'a -> 'a t
(** [diff typ v1 v2] computes a patch that when applied to [v1]
    produces [v2]. *)

val apply : 'a t -> 'a -> 'a
(** [patch p v1] applies the patch [p] to [v1]. The following invariant
    must hold [ patch v1 (diff typ v1 v2) = v2 ] *)
