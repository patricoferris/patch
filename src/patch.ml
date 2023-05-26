open Typegist

type 'a t =
  | Scalar : 'a Type.Gist.scalar * 'a -> 'a t
  | List : [ `Patch of 'a t | `Value of 'a ] list -> 'a list t
  | Record : 'a record -> 'a t
  | Empty

and 'a record = { fields : ('a, 'a) field_patches }

and ('a, 'b) field_patches =
  | Ctor : 'c -> ('a, 'c) field_patches
  | App :
      ('a, 'b) Type.Gist.field * 'b t * ('a, 'b -> 'c) field_patches
      -> ('a, 'c) field_patches

let empty = Empty

module Record_witness = Type.Gist.Meta.Key (Type.Id)

let rec join : type a. a t -> a t -> a t =
 fun a b ->
  match (a, b) with
  | a, Empty -> a
  | Empty, b -> b
  | Scalar (Unit m, ()), Scalar (Unit _, ()) -> Scalar (Unit m, ())
  | Scalar (Bool b, _), Scalar (Bool _, b2) -> Scalar (Bool b, b2)
  | Scalar (Char c, _), Scalar (Char _, b2) -> Scalar (Char c, b2)
  | Scalar (Int i, i1), Scalar (Int _, i2) -> Scalar (Int i, i1 + i2)
  | List l1, List l2 ->
      let rec aux acc a b =
        match (a, b) with
        | [], l2s -> List.rev acc @ l2s
        | l1s, [] -> List.rev acc @ l1s
        | `Patch p1 :: l1s, `Patch p2 :: l2s ->
            aux (`Patch (join p1 p2) :: acc) l1s l2s
        | `Patch _ :: l1s, `Value v2 :: l2s -> aux (`Value v2 :: acc) l1s l2s
        | `Value v1 :: l1s, `Patch _ :: l2s -> aux (`Value v1 :: acc) l1s l2s
        | `Value v1 :: l1s, `Value _ :: l2s -> aux (`Value v1 :: acc) l1s l2s
      in
      List (aux [] l1 l2)
  | Record p1, Record p2 ->
      let rec merge :
          type a b.
          (a, b) field_patches -> (a, b) field_patches -> (a, b) field_patches =
       fun a b ->
        match (a, b) with
        | Ctor c, Ctor _ -> Ctor c
        | App (f1, p1, next1), App (f2, p2, next2) -> (
            (* TODO: Do we HAVE to have type witnesses here ? :( *)
            let m1 = Type.Gist.Field.meta f1 in
            let m2 = Type.Gist.Field.meta f2 in
            let w1 = Record_witness.find m1 in
            let w2 = Record_witness.find m2 in
            match (w1, w2) with
            | Some w1, Some w2 -> (
                match Type.Id.provably_equal w1 w2 with
                | Some Equal -> App (f1, join p1 p2, merge next1 next2)
                | None -> failwith "Types of record fields are not equal")
            | _ ->
                failwith
                  "Records must be augmented with type witnesses to join \
                   patches")
        | _ -> assert false
      in
      Record { fields = merge p1.fields p2.fields }
  | _ -> assert false

let rec diff : type a. a Type.Gist.t -> a -> a -> a t =
 fun typ v1 v2 ->
  match typ with
  | Scalar (Unit v) -> Scalar (Unit v, ())
  | Scalar (Int v) -> Scalar (Int v, v2 - v1)
  | Scalar (Int32 v) -> Scalar (Int32 v, Int32.sub v2 v1)
  | Scalar (Int64 v) -> Scalar (Int64 v, Int64.sub v2 v1)
  | Scalar (Char v) -> Scalar (Char v, v2)
  | Scalar (Bool v) -> Scalar (Bool v, v2)
  | Scalar (Float v) -> Scalar (Float v, v2 -. v1)
  | Record r -> diff_record r v1 v2
  | _ -> assert false

and diff_record : type a. a Type.Gist.record -> a -> a -> a t =
 fun record v1 v2 ->
  let fields = Type.Gist.Record.fields record in
  let rec loop : type f. (a, f) Type.Gist.fields -> (a, f) field_patches =
    function
    | Ctor c -> Ctor c
    | App (fs, field) ->
        let fpatch = loop fs in
        let ftype = Type.Gist.Field.gist field in
        let p =
          diff ftype
            (Type.Gist.Field.project field v1)
            (Type.Gist.Field.project field v2)
        in
        App (field, p, fpatch)
  in
  Record { fields = loop fields }

and apply : type a. a t -> a -> a =
 fun p v ->
  match p with
  | Scalar (Int _, i) -> v + i
  | Scalar (Bool _, i) -> i
  | List lst ->
      let rec aux acc patches vs =
        match (patches, vs) with
        | `Patch p :: ps, v :: vs -> aux (apply p v :: acc) ps vs
        | `Value v :: ps, [] -> aux (v :: acc) ps []
        | [], vs -> List.rev acc @ vs
        | _, [] -> assert false
        | `Value v :: ps, _ :: _ -> aux (v :: acc) ps []
      in
      aux [] lst v
  | Record re ->
      let rec loop : type f. (a, f) field_patches -> f = function
        | Ctor constructor -> constructor
        | App (field, p, fs) ->
            let f = loop fs in
            let p = apply p (Type.Gist.Field.project field v) in
            f p
      in
      loop re.fields
  | _ -> assert false
