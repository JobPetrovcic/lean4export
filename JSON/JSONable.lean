import Lean

open Lean

class JSONable (α : Type U) where
  json : α → String
open JSONable

def surroundWithQuotes (s : String) : String := s!"\"{s}\""

instance : JSONable Bool where json b := toString b
instance : JSONable Nat where json n := toString n
instance : JSONable Name where json n := surroundWithQuotes n.toString
instance : JSONable String where json s := s

inductive Tag
| LevelZero | LevelSucc | LevelMax | LevelIMax | LevelParam
| BVar | Sort | Const | NatLit | StrLit | App | Lambda | Let | Pi | Proj
| DeclarationInfo | Axiom | Definition | Theorem | Opaque | Quot | Inductive | Constructor | RecursorRule | Recursor | DeclarationProfile

instance : JSONable Tag where
  json := fun
    | Tag.LevelZero => surroundWithQuotes "LevelZero"
    | Tag.LevelSucc => surroundWithQuotes "LevelSucc"
    | Tag.LevelMax => surroundWithQuotes "LevelMax"
    | Tag.LevelIMax => surroundWithQuotes "LevelIMax"
    | Tag.LevelParam => surroundWithQuotes "LevelParam"
    | Tag.BVar => surroundWithQuotes "BVar"
    | Tag.Sort => surroundWithQuotes "Sort"
    | Tag.Const => surroundWithQuotes "Const"
    | Tag.NatLit => surroundWithQuotes "NatLit"
    | Tag.StrLit => surroundWithQuotes "StrLit"
    | Tag.App => surroundWithQuotes "App"
    | Tag.Lambda => surroundWithQuotes "Lambda"
    | Tag.Let => surroundWithQuotes "Let"
    | Tag.Pi => surroundWithQuotes "Pi"
    | Tag.Proj => surroundWithQuotes "Proj"
    | Tag.DeclarationInfo => surroundWithQuotes "DeclarationInfo"
    | Tag.Axiom => surroundWithQuotes "Axiom"
    | Tag.Definition => surroundWithQuotes "Definition"
    | Tag.Theorem => surroundWithQuotes "Theorem"
    | Tag.Opaque => surroundWithQuotes "Opaque"
    | Tag.Quot => surroundWithQuotes "Quot"
    | Tag.Inductive => surroundWithQuotes "Inductive"
    | Tag.Constructor => surroundWithQuotes "Constructor"
    | Tag.RecursorRule => surroundWithQuotes "RecursorRule"
    | Tag.Recursor => surroundWithQuotes "Recursor"
    | Tag.DeclarationProfile => surroundWithQuotes "DeclarationProfile"

def JSONkvpair (k : String) (v : String) : String :=s!"{surroundWithQuotes k}: {v}"
--#eval JSONkvpair "a" "b"
def JSONcommaJoin (xs : List String) : String := String.intercalate ", " xs
--#eval JSONcommaJoin ["a", "b", "c"]

instance [JSONable α]: JSONable (String × α) where json := fun ⟨k, v⟩ => JSONkvpair k (json v)

def jsonListAsList {α : Type} [JSONable α] (xs : List α) : String :=
  "[" ++ JSONcommaJoin (xs.map json) ++ "]"
def jsonListAsDict [JSONable α] (xs :List α) : String := "{" ++ JSONcommaJoin (xs.map json) ++ "}"

def jsonLevel (l : Level) : String :=
  let kvpairs := match l with
  | Level.zero => [("tag", json Tag.LevelZero)]
  | Level.mvar _ => panic! "mvars cannot be exported"
  | Level.succ l => [("tag", json Tag.LevelSucc), ("anc", (jsonLevel l))]
  | Level.max l1 l2 => [("tag", json Tag.LevelMax), ("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))]
  | Level.imax l1 l2 => [("tag", json Tag.LevelIMax), ("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))]
  | Level.param n => [("tag", json Tag.LevelParam), ("name", (json n))]
  jsonListAsDict kvpairs
--#eval jsonLevel (mkLevelSucc (mkLevelParam `l))

instance : JSONable Level where json l := jsonLevel l

def jsonExpr (e : Expr) : String :=
  -- currently ignoring binder infos
  match e with
  | .mdata _ e => jsonExpr e
  | .fvar .. => panic! "fvars cannot be exported"
  | .mvar .. => panic! "mvars cannot be exported"
  | .bvar i => jsonListAsDict [("tag", json Tag.BVar), ("idx", json i)]
  | .sort l => jsonListAsDict [("tag", json Tag.Sort), ("level", json l)]
  | .const n us => jsonListAsDict [("tag", json Tag.Const), ("name", json n), ("us", jsonListAsList us)]
  | .lit (.natVal i) => jsonListAsDict [("tag", json Tag.NatLit), ("val", json i)]
  | .lit (.strVal s) => jsonListAsDict [("tag", json Tag.StrLit), ("val", s)]
  | .app f a => jsonListAsDict [("tag", json Tag.App), ("fn", jsonExpr f), ("arg", jsonExpr a)]
  | .lam n d b _bi =>
      --[("tag", json Tag.Lambda), ("info", json bi), ("name", json n), ("domain", json d), ("body", json b)]
      jsonListAsDict [("tag", json Tag.Lambda), ("bname", json n), ("arg_type", jsonExpr d), ("body", jsonExpr b)]
  | .letE n d v b _ =>
      jsonListAsDict [("tag", json Tag.Let), ("bname", json n), ("arg_type", jsonExpr d), ("val", jsonExpr v), ("body", jsonExpr b)]
  | .forallE n d b _bi =>
      jsonListAsDict [("tag", json Tag.Pi), ("bname", json n), ("arg_type", jsonExpr d), ("body_type", jsonExpr b)]
  | .proj s i e2 => jsonListAsDict [("tag", json Tag.Proj), ("struct", json s), ("idx", json i), ("expr", jsonExpr e2)]

instance : JSONable Expr where json e := jsonExpr e

instance : JSONable ReducibilityHints where
  json := fun
    | ReducibilityHints.opaque => surroundWithQuotes "O"
    | ReducibilityHints.abbrev => surroundWithQuotes "A"
    | ReducibilityHints.regular n => surroundWithQuotes s!"R {n}"

--instance : Hashable RecursorRule where hash r := hash (r.ctor, r.nfields, r.rhs)

def jsonNameAsLevelParam (n : Name) : String :=
  jsonListAsDict [("tag", json Tag.LevelParam), ("name", json n)]

def jsonNameListAsLevelParamList (ns : List Name) : String := jsonListAsList (ns.map jsonNameAsLevelParam)

instance : JSONable ConstantVal where
  json cv :=
    jsonListAsDict [("tag", json Tag.DeclarationInfo), ("name", json cv.name), ("level_params", jsonNameListAsLevelParamList cv.levelParams ), ("type", jsonExpr cv.type)]

instance : JSONable AxiomVal where
  json ai := jsonListAsDict [("tag", json Tag.Axiom), ("info", json ai.toConstantVal)]

instance : JSONable DefinitionVal where
  json di :=
    if di.safety != .safe then unreachable!
    else
      jsonListAsDict [("tag", json Tag.Definition), ("info", json di.toConstantVal), ("value", jsonExpr di.value), ("hints", json di.hints)]

instance : JSONable TheoremVal where
  json ti :=
    jsonListAsDict [("tag", json Tag.Theorem), ("info", json ti.toConstantVal), ("value", jsonExpr ti.value)]

instance : JSONable OpaqueVal where
  json oi :=
    jsonListAsDict [("tag", json Tag.Opaque), ("info", json oi.toConstantVal), ("value", jsonExpr oi.value)]

instance : JSONable QuotVal where
  json qi :=
    jsonListAsDict [("tag", json Tag.Quot), ("info", json qi.toConstantVal)]

instance : JSONable InductiveVal where
  json ii :=
    jsonListAsDict [("tag", json Tag.Inductive), ("info", json ii.toConstantVal), ("is_recursive", json ii.isRec), ("num_params", json ii.numParams), ("num_indices", json ii.numIndices), ("inductive_names", jsonListAsList (ii.all.map json)), ("constructor_names", jsonListAsList ii.ctors)]

instance : JSONable ConstructorVal where
  json ci :=
   jsonListAsDict [("tag", json Tag.Constructor), ("info", json ci.toConstantVal), ("inductive_name", json ci.induct), ("c_index", json ci.cidx), ("num_params", json ci.numParams), ("num_fields", json ci.numFields)]

instance : JSONable RecursorRule where
  json rr :=
    jsonListAsDict [("tag", json Tag.RecursorRule), ("constructor", json rr.ctor), ("num_fields", json rr.nfields), ("value", jsonExpr rr.rhs)]

instance : JSONable RecursorVal where
  json ri :=
    -- what about ri.all?
    jsonListAsDict [("tag", json Tag.Recursor), ("info", json ri.toConstantVal), ("num_params", json ri.numParams), ("num_indices", json ri.numIndices), ("num_motives", json ri.numMotives), ("num_minors", json ri.numMinors), ("recursor_rules", jsonListAsList ri.rules), ("isK", json ri.k)]

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
