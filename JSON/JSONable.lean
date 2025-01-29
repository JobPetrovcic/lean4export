import Lean

open Lean

class JSONable (α : Type U) where
  json : α → String
open JSONable

def surroundWithQuotes (s : String) : String := s!"\"{s}\""

instance : JSONable Bool where json b := toString b
instance : JSONable Nat where json n := toString n
instance : JSONable String where json s := s

inductive Tag
| LevelZero | LevelSucc | LevelMax | LevelIMax | LevelParam
| BVar | Sort | Const | NatLit | StrLit | App | Lambda | Let | Pi | Proj
| DeclarationInfo | Axiom | Definition | Theorem | Opaque | Quot | Inductive | Constructor | RecursorRule | Recursor  | ExprRef | Anonymous | SubName | OpaqueHint | Abbrev | Regular

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
    | Tag.ExprRef => surroundWithQuotes "ExprRef"
    | Tag.Anonymous => surroundWithQuotes "Anonymous"
    | Tag.SubName => surroundWithQuotes "SubName"
    | Tag.OpaqueHint => surroundWithQuotes "OpaqueHint"
    | Tag.Abbrev => surroundWithQuotes "Abbrev"
    | Tag.Regular => surroundWithQuotes "Regular"

def JSONkvpair (k : String) (v : String) : String :=s!"{surroundWithQuotes k}: {v}"
--#eval JSONkvpair "a" "b"
def JSONcommaJoin (xs : List String) : String := String.intercalate ", " xs
--#eval JSONcommaJoin ["a", "b", "c"]

instance [JSONable α]: JSONable (String × α) where json := fun ⟨k, v⟩ => JSONkvpair k (json v)

def jsonListAsList {α : Type} [JSONable α] (xs : List α) : String :=
  "[" ++ JSONcommaJoin (xs.map json) ++ "]"
def jsonListAsDict [JSONable α] (xs :List α) : String := "{" ++ JSONcommaJoin (xs.map json) ++ "}"

def JSONName (n : Name) : String :=
  match n with
  | Name.anonymous =>
    jsonListAsDict [
      ("tag", json Tag.Anonymous),
      ("args", jsonListAsDict ([] : List String))
    ]
  | Name.str p s =>
    jsonListAsDict [
      ("tag", json Tag.SubName),
      ("args", jsonListAsDict [("str", surroundWithQuotes s), ("anc", JSONName p)])
    ]
  | Name.num p i =>
    jsonListAsDict [
      ("tag", json Tag.SubName),
      ("args", jsonListAsDict [("str", surroundWithQuotes s!"{i}"), ("anc", JSONName p)])
    ]
instance : JSONable Name where json n := JSONName n

-- This two functions are used to then more conveniently parse the json objects of constants.
-- Maybe TODO: instead of exporting as LevelParams, we could export as a list of names. This would be more standard, but requires special handling on the parser side.
def jsonNameAsLevelParam (n : Name) : String :=
  jsonListAsDict [
    ("tag", json Tag.LevelParam),
    ("args", jsonListAsDict [("pname", json n)])
  ]

def jsonLevel (l : Level) : String :=
  match l with
  | Level.zero => jsonListAsDict [
    ("tag", json Tag.LevelZero),
    ("args", jsonListAsDict ([] : List String))
  ]
  | Level.mvar _ => panic! "mvars cannot be exported"
  | Level.succ l => jsonListAsDict [
      ("tag", json Tag.LevelSucc),
      ("args", jsonListAsDict [("anc", (jsonLevel l))]),
    ]
  | Level.max l1 l2 => jsonListAsDict [
      ("tag", json Tag.LevelMax),
      ("args", jsonListAsDict [("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))])
    ]
  | Level.imax l1 l2 => jsonListAsDict [
      ("tag", json Tag.LevelIMax),
      ("args", jsonListAsDict [("lhs", (jsonLevel l1)), ("rhs", (jsonLevel l2))])
    ]
  | Level.param n => jsonNameAsLevelParam n
--#eval jsonLevel (mkLevelSucc (mkLevelParam `l))

instance : JSONable Level where json l := jsonLevel l

structure Repeated where
  expr2index : HashMap Expr Nat := {}

abbrev RM := StateM Repeated

-- "\r","\n","\t","'","\"","\\","\t"
def handleSpecialChar (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\r' => acc ++ "\\r"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | '\'' => acc ++ "\\'"
    | '\"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | _ => acc.push c
  ) ""

partial def jsonExpr (e : Expr) : RM String := do
  let st ← get
  -- handle mdata before assigning an index
  if let Expr.mdata _ e := e then
    jsonExpr e
  else
  if st.expr2index.contains e then
    let index := st.expr2index.find! e
    return jsonListAsDict [("tag", json Tag.ExprRef), ("ei", json index)]
  else

  let index := st.expr2index.size
  -- insert the current expression into the hashmap
  modify fun st => { expr2index := st.expr2index.insert e index }
  let json_str : RM String :=
    match e with -- ignoring binder infos
    | .mdata _ e => panic! "mdata should have been handled"
    | .fvar .. => panic! "fvars cannot be exported"
    | .mvar .. => panic! "mvars cannot be exported"
    | .bvar i =>
      return jsonListAsDict
        [
          ("tag", json Tag.BVar),
          ("ei", json index),
          ("args", jsonListAsDict [("db_index", json i)])
        ]
    | .sort l =>
      return jsonListAsDict
        [
          ("tag", json Tag.Sort),
          ("ei", json index),
          ("args", jsonListAsDict [("level", json l)])
        ]
    | .const n us =>
      return jsonListAsDict
        [
          ("tag", json Tag.Const),
          ("ei", json index),
          ("args", jsonListAsDict [("cname", json n), ("lvl_params", jsonListAsList us)])
        ]
    | .lit (.natVal i) =>
      return jsonListAsDict
        [
          ("tag", json Tag.NatLit),
          ("ei", json index),
          ("args", jsonListAsDict [("val", json i)])
        ]
    | .lit (.strVal s) =>
      return jsonListAsDict
        [
          ("tag", json Tag.StrLit),
          ("ei", json index),
          ("args", jsonListAsDict [("val", surroundWithQuotes (handleSpecialChar s))])
        ]
    | .app f a => do
      let rm_f ← jsonExpr f
      let rm_a ← jsonExpr a
      return jsonListAsDict
          [
            ("tag", json Tag.App),
            ("ei", json index),
            ("args", jsonListAsDict [("fn", rm_f), ("arg", rm_a)])
          ]
    | .lam n d b _bi => do
      let rm_d ← jsonExpr d
      let rm_b ← jsonExpr b

        -- [("tag", json Tag.Lambda), ("info", json bi), ("name", json n), ("domain", rm_d), ("body", rm_b)]
      return jsonListAsDict
        [
          ("tag", json Tag.Lambda),
          ("ei", json index),
          ("args", jsonListAsDict [("bname", json n), ("arg_type", rm_d), ("body", rm_b)])
        ]
    | .letE n d v b _ => do
      let rm_d ← jsonExpr d
      let rm_v ← jsonExpr v
      let rm_b ← jsonExpr b
      return jsonListAsDict
        [
          ("tag", json Tag.Let),
          ("ei", json index),
          ("args", jsonListAsDict [("bname", json n), ("arg_type", rm_d), ("val", rm_v), ("body", rm_b)])
        ]
    | .forallE n d b _bi => do
      let rm_d ← jsonExpr d
      let rm_b ← jsonExpr b
      return jsonListAsDict
        [
          ("tag", json Tag.Pi),
          ("ei", json index),
          ("args", jsonListAsDict [("bname", json n), ("arg_type", rm_d), ("body_type", rm_b)])
        ]
    | .proj sn i e => do
      let rm_e ← jsonExpr e
      return jsonListAsDict
        [
          ("tag", json Tag.Proj),
          ("ei", json index),
          ("args", jsonListAsDict [("sname", json sn), ("index", json i), ("expr", rm_e)])
        ]
  json_str

-- To extract an expression we use a hashmap to keep track of the expressions that repeat.
-- We do this for each expression separately: if we did this for all expressions at once, the hashmap would be too large, which leads to very slow performance and high memory usage.
instance : JSONable Expr where json e := (jsonExpr e).run' {}

instance : JSONable ReducibilityHints where
  json := fun
    | ReducibilityHints.opaque => jsonListAsDict [
        ("tag", json Tag.OpaqueHint),
        ("args", jsonListAsDict ([] : List String))
      ]
    | ReducibilityHints.abbrev => jsonListAsDict [
        ("tag", json Tag.Abbrev),
        ("args", jsonListAsDict ([] : List String))
      ]
    | ReducibilityHints.regular n =>
      jsonListAsDict [
        ("tag", json Tag.Regular),
        ("args", jsonListAsDict [("depth", s!"{n}")])
      ]

def jsonNameListAsLevelParamList (ns : List Name) : String := jsonListAsList (ns.map jsonNameAsLevelParam)

instance : JSONable ConstantVal where
  json cv :=
    jsonListAsDict [
      ("tag", json Tag.DeclarationInfo),
      ("args", jsonListAsDict [("ciname", json cv.name),("lvl_params", jsonNameListAsLevelParamList cv.levelParams), ("type", json cv.type)])
    ]

instance : JSONable AxiomVal where
  json ai := jsonListAsDict [
    ("tag", json Tag.Axiom),
    ("args", jsonListAsDict [("info", json ai.toConstantVal)])
  ]

instance : JSONable DefinitionVal where
  json di :=
    if di.safety != .safe then unreachable!
    else
      jsonListAsDict [
        ("tag", json Tag.Definition),
        ("args", jsonListAsDict [("info", json di.toConstantVal), ("value", json di.value), ("hint", json di.hints)])
      ]

instance : JSONable TheoremVal where
  json ti :=
    jsonListAsDict [
      ("tag", json Tag.Theorem),
      ("args", jsonListAsDict [("info", json ti.toConstantVal), ("value", json ti.value)])
    ]

instance : JSONable OpaqueVal where
  json oi :=
    jsonListAsDict [
      ("tag", json Tag.Opaque),
      ("args", jsonListAsDict [("info", json oi.toConstantVal), ("value", json oi.value)])
    ]

instance : JSONable QuotVal where
  json qi :=
    jsonListAsDict [
      ("tag", json Tag.Quot),
      ("args", jsonListAsDict [("info", json qi.toConstantVal)])
    ]

instance : JSONable InductiveVal where
  json ii :=
    jsonListAsDict [
      ("tag", json Tag.Inductive),
      ("args", jsonListAsDict [("info", json ii.toConstantVal), ("is_recursive", json ii.isRec), ("num_params", json ii.numParams), ("num_indices", json ii.numIndices), ("inductive_names", jsonListAsList (ii.all.map json)), ("constructor_names", jsonListAsList ii.ctors)])
    ]

instance : JSONable ConstructorVal where
  json ci :=
   jsonListAsDict [("tag", json Tag.Constructor),
    ("args", jsonListAsDict [("info", json ci.toConstantVal), ("inductive_name", json ci.induct), ("c_index", json ci.cidx), ("num_params", json ci.numParams), ("num_fields", json ci.numFields)])
  ]

instance : JSONable RecursorRule where
  json rr :=
    jsonListAsDict [
      ("tag", json Tag.RecursorRule),
      ("args", jsonListAsDict [("constructor", json rr.ctor), ("num_fields", json rr.nfields), ("value", json rr.rhs)]),
    ]

instance : JSONable RecursorVal where
  json ri :=
    -- what about ri.all?
    jsonListAsDict [
      ("tag", json Tag.Recursor),
      ("args", jsonListAsDict [("info", json ri.toConstantVal), ("num_params", json ri.numParams), ("num_indices", json ri.numIndices), ("num_motives", json ri.numMotives), ("num_minors", json ri.numMinors), ("recursor_rules", jsonListAsList ri.rules), ("isK", json ri.k)])
    ]

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
