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

(* A notion of equality across all constructors for type gists... maybe? *)
type (_, _) eq =
  | Eq : ('a, 'a) eq


let fun_eq : type a b c d. (a -> b, c -> d) eq -> (a, c) eq -> (b, d) eq = fun Eq Eq -> Eq

exception Not_equal

let rec eq_gist : type a b. a Type.Gist.t -> b Type.Gist.t -> (a, b) eq = fun v1 v2 ->
  let open Type.Gist in
  match v1, v2 with
  | Scalar (Int _), Scalar (Int _) -> Eq
  | Scalar (Float _), Scalar (Float _) -> Eq
  | Scalar (Unit _), Scalar (Unit _) -> Eq
  | Scalar (Bool _), Scalar (Bool _) -> Eq
  | Scalar (Char _), Scalar (Char _) -> Eq
  | Scalar (Uchar _), Scalar (Uchar _) -> Eq
  | Scalar (Nativeint _), Scalar (Nativeint _) -> Eq
  | Scalar (Int64 _), Scalar (Int64 _) -> Eq
  | Scalar (Int32 _), Scalar (Int32 _) -> Eq
  | Record r1, Record r2 -> eq_record r1 r2
  | _ -> raise Not_equal


  and eq_record : type a b. a Type.Gist.record -> b Type.Gist.record -> (a, b) eq = fun r1 r2 ->
    let open Type.Gist in
    let fields1 = Record.fields r1 in
    let fields2 = Record.fields r2 in
    let rec loop : type a b f g. (a, f) Type.Gist.fields -> (b, g) Type.Gist.fields -> (f, g) eq = fun f1 f2 ->
      match f1, f2 with
      | Ctor _, Ctor _ -> Obj.magic Eq
      | App (next1, f1), App (next2, f2) -> (
        let name_eq = String.equal (Type.Gist.Field.name f1) (Type.Gist.Field.name f2) in
        if not name_eq then raise Not_equal;
        let f = eq_gist (Type.Gist.Field.gist f1) (Type.Gist.Field.gist f2) in
        let f_next = loop next1 next2 in
        fun_eq f_next f
      )
      | _ -> raise Not_equal
    in
    loop fields1 fields2


let equal_gist v1 v2 = try Some (eq_gist v1 v2) with Not_equal -> None

let rec join : type a. a t -> a t -> a t =
 fun a b ->
  match (a, b) with
  | a, Empty -> a
  | Empty, b -> b
  | Scalar (Unit m, ()), Scalar (Unit _, ()) -> Scalar (Unit m, ())
  | Scalar (Bool b, _), Scalar (Bool _, b2) -> Scalar (Bool b, b2)
  | Scalar (Char c, _), Scalar (Char _, b2) -> Scalar (Char c, b2)
  | Scalar (Float f, _), Scalar (Float _, f2) -> Scalar (Float f, f2)
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
          match equal_gist (Type.Gist.Field.gist f1) (Type.Gist.Field.gist f2) with
          | Some Eq -> App (f1, join p1 p2, merge next1 next2)
          | None -> failwith "Failed to prove fields equal type!"
          )
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
  | Scalar (Uchar v) -> Scalar (Uchar v, v2)
  | Scalar (Bool v) -> Scalar (Bool v, v2)
  | Scalar (Nativeint v) -> Scalar (Nativeint v, Nativeint.sub v2 v1)
  (* Probably better off just keeping the second value for floats *)
  | Scalar (Float v) -> Scalar (Float v, v2)
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
