import Lean

open Lean

class JSONable (α : Type U) where
  json : α → String
open JSONable

instance : JSONable Bool where json b := if b then "True" else "False"
instance : JSONable Nat where json n := toString n
instance : JSONable Name where json n := s!"\"{n}\""
instance : JSONable String where json s := s

def JSONkvpair (k : String) (v : String) : String :=s!"\"{k}\": {v}"
#eval JSONkvpair "a" "b"
def JSONcommaJoin (xs : List String) : String := xs.foldr (fun acc x => acc ++ ", " ++ x) ""
#eval JSONcommaJoin ["a", "b", "c"]
def JSONkvpairs (kvs : List (String × String)) : List String := kvs.map (fun ⟨k, v⟩ => JSONkvpair k v)
#eval JSONkvpairs [("a", "b"), ("c", "d")]

def jsonListAsJSONList {α : Type} [JSONable α] (xs : List α) : String :=
  "[" ++ JSONcommaJoin (xs.map json) ++ "]"

instance : JSONable (String × String) where json := fun ⟨k, v⟩ => JSONkvpair k v
instance [JSONable α] : JSONable (List α) where json xs := "{" ++ JSONcommaJoin (xs.map json) ++ "}"

def jsonLevel (l : Level) : String :=
  let kvpairs := match l with
  | Level.zero => [("tag", "LevelZero")]
  | Level.mvar _ => panic! "mvars cannot be exported"
  | Level.succ l => [("tag", "LevelSucc"), ("anc", (jsonLevel l))]
  | Level.max l1 l2 => [("tag", "LevelMax"), ("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))]
  | Level.imax l1 l2 => [("tag", "LevelIMax"), ("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))]
  | Level.param n => [("tag", "LevelParam"), ("name", (json n))]
  json kvpairs
#eval jsonLevel (mkLevelSucc (mkLevelParam `l))

instance : JSONable Level where json l := jsonLevel l

def jsonExpr (e : Expr) : String :=
  -- currently ignoring binder infos
  let kvpairs := match e with
    | .mdata .. => panic! "mdata cannot be exported"
    | .fvar .. => panic! "fvars cannot be exported"
    | .mvar .. => panic! "mvars cannot be exported"
    | .bvar i => [("tag", "BVar"), ("idx", json i)]
    | .sort l => [("tag", "Sort"), ("level", json l)]
    | .const n us => [("tag", "Const"), ("name", json n), ("us", jsonListAsJSONList us)]
    | .lit (.natVal i) => [("tag", "NatLit"), ("val", json i)]
    | .lit (.strVal s) => [("tag", "StrLit"), ("val", s)]
    | .app f a => [("tag", "App"), ("fn", jsonExpr f), ("arg", jsonExpr a)]
    | .lam n d b _bi =>
      --[("tag", "Lambda"), ("info", json bi), ("name", json n), ("domain", json d), ("body", json b)]
      [("tag", "Lambda"), ("bname", json n), ("arg_type", jsonExpr d), ("body", jsonExpr b)]
    | .letE n d v b _ =>
      [("tag", "Let"), ("bname", json n), ("arg_type", jsonExpr d), ("val", jsonExpr v), ("body", jsonExpr b)]
    | .forallE n d b _bi =>
      [("tag", "Pi"), ("bname", json n), ("arg_type", jsonExpr d), ("body_type", jsonExpr b)]
    | .proj s i e2 => [("tag", "Proj"), ("struct", json s), ("idx", json i), ("expr", jsonExpr e2)]
  json kvpairs

instance : JSONable Expr where json e := jsonExpr e

instance : JSONable ReducibilityHints where
  json := fun
    | ReducibilityHints.opaque => "O"
    | ReducibilityHints.abbrev => "A"
    | ReducibilityHints.regular n => s!"R {n}"

--instance : Hashable RecursorRule where hash r := hash (r.ctor, r.nfields, r.rhs)

def jsonNameAsLevelParam (n : Name) : String :=
  let kvpairs := [("tag", "LevelParam"), ("name", json n)]
  json kvpairs

def jsonNameListAsLevelParamList (ns : List Name) : String := jsonListAsJSONList (ns.map jsonNameAsLevelParam)

instance : JSONable ConstantVal where
  json cv :=
    let kvpairs := [("tag", "DeclarationInfo"), ("name", json cv.name), ("level_params", jsonNameListAsLevelParamList cv.levelParams ), ("type", jsonExpr cv.type)]
    json kvpairs

instance : JSONable AxiomVal where
  json ai :=
    let kvpairs := [("tag", "Axiom"), ("info", json ai.toConstantVal)]
    json kvpairs

instance : JSONable DefinitionVal where
  json di :=
    if di.safety != .safe then unreachable!
    else
      let kvpairs := [("tag", "Definition"), ("info", json di.toConstantVal), ("value", jsonExpr di.value), ("hints", json di.hints)]
      json kvpairs

instance : JSONable TheoremVal where
  json ti :=
    let kvpairs := [("tag", "Theorem"), ("info", json ti.toConstantVal), ("value", jsonExpr ti.value)]
    json kvpairs

instance : JSONable OpaqueVal where
  json oi :=
    let kvpairs := [("tag", "Opaque"), ("info", json oi.toConstantVal), ("value", jsonExpr oi.value)]
    json kvpairs

instance : JSONable QuotVal where
  json qi :=
    let kvpairs := [("tag", "Quot"), ("info", json qi.toConstantVal)]
    json kvpairs

instance : JSONable InductiveVal where
  json ii :=
    let kvpairs := [("tag", "Inductive"), ("info", json ii.toConstantVal), ("is_recursive", json ii.isRec), ("num_params", json ii.numParams), ("num_indices", json ii.numIndices), ("inductive_names", jsonListAsJSONList (ii.all.map json)), ("constructor_names", json ii.ctors)]
    json kvpairs

instance : JSONable ConstructorVal where
  json ci :=
    let kvpairs := [("tag", "Constructor"), ("info", json ci.toConstantVal), ("inductive_name", json ci.induct), ("c_index", json ci.cidx), ("num_params", json ci.numParams), ("num_fields", json ci.numFields)]
    json kvpairs

instance : JSONable RecursorRule where
  json rr :=
    let kvpairs := [("tag", "RecursorRule"), ("constructor", json rr.ctor), ("num_fields", json rr.nfields), ("value", jsonExpr rr.rhs)]
    json kvpairs

instance : JSONable RecursorVal where
  json ri :=
    -- what about ri.all?
    let kvpairs := [("tag", "Recursor"), ("info", json ri.toConstantVal), ("num_params", json ri.numParams), ("num_indices", json ri.numIndices), ("num_motives", json ri.numMotives), ("num_minors", json ri.numMinors), ("recursor_rules", json ri.rules), ("isK", json ri.k)]
    json kvpairs

instance : JSONable ConstantInfo where
  json ci :=
    if ci.isUnsafe then panic! "Don't export unsafe constant"
    else
      match ci with
      | .axiomInfo val => json val
      | .defnInfo val => json val
      | .thmInfo val => json val
      | .opaqueInfo val => json val
      | .quotInfo val => json val
      | .inductInfo val => json val
      | .ctorInfo val => json val
      | .recInfo val => json val
