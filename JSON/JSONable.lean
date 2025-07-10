import Lean
import Batteries.Data.HashMap.Basic

open Lean

class JSONable (α : Type U) where
  json : α → String
open JSONable

def surroundWithQuotes (s : String) : String := s!"\"{s}\""

instance : JSONable Bool where json b := toString b
instance : JSONable Nat where json n := toString n
instance : JSONable String where json s := s

-- "\r","\n","\t","'","\"","\\","\t" are handled specially, since they require the "\" character to be escaped.
def handleSpecialChar (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '\r' => acc ++ "\\r"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | '\'' => acc ++ "\'"
    | '\"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | _ => acc.push c
  ) ""

-- All the tags that can be used in the JSON representation of a Lean Expression
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

-- The main building blocks for the JSON representation of a Lean Expression
-- Given a string A and B, it returns the string "A" : B
def JSONkvpair (k : String) (v : String) : String :=s!"{surroundWithQuotes k}: {v}"
--Test1 : #eval JSONkvpair "a" "b"
-- Join the string with a ", " separator
def JSONcommaJoin (xs : List String) : String := String.intercalate ", " xs
--Test2: #eval JSONcommaJoin ["a", "b", "c"]

instance [JSONable α]: JSONable (String × α) where json := fun ⟨k, v⟩ => JSONkvpair k (json v)

-- convert a list of strings to a JSON list
def jsonListAsList {α : Type} [JSONable α] (xs : List α) : String :=
  "[" ++ JSONcommaJoin (xs.map json) ++ "]"
-- convert a list of strings to a JSON dictionary
def jsonListAsDict [JSONable α] (xs : List α) : String := "{" ++ JSONcommaJoin (xs.map json) ++ "}"

-- The JSON representation of a Lean Name
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
      ("args", jsonListAsDict [("str", surroundWithQuotes (handleSpecialChar s)), ("anc", JSONName p)])
    ]
  | Name.num p i =>
    jsonListAsDict [
      ("tag", json Tag.SubName),
      ("args", jsonListAsDict [("str", surroundWithQuotes s!"{i}"), ("anc", JSONName p)])
    ]
instance : JSONable Name where json n := JSONName n

-- This two functions are used to more conveniently parse the json objects of constants.

-- a name is exported as: Anonymous or SubName (a string concatenated to another name anc with separator ".")
def jsonNameAsLevelParam (n : Name) : String :=
  jsonListAsDict [
    ("tag", json Tag.LevelParam),
    ("args", jsonListAsDict [("pname", json n)])
  ]

-- The JSON representation of a Lean Level:
-- LevelZero does not have any arguments
-- LevelSucc has one argument: the ancestor level
-- LevelMax and LevelIMax have two arguments: the left-hand side and the right-hand side
-- LevelParam is exported along with its name
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
--Test3: #eval jsonLevel (mkLevelSucc (mkLevelParam `l))

instance : JSONable Level where json l := jsonLevel l

-- The structure Repeated is used to keep track of the expressions that repeat. Avoids exponential blowup in the JSON representation of expressions.
structure Repeated where
  expr2index : Std.HashMap Expr Nat := {}

-- The StateM monad is used to keep track of the hashmap that maps expressions to their index.
abbrev RM := StateM Repeated

-- The JSON representation of a Lean Expression always contains a tag and a list of arguments and "ei" (the index of the expression in the hashmap).
-- BVar has one argument: the de Bruijn index
-- Sort has one argument: the level
-- Const has two arguments: the constant name and the list of level parameters
-- NatLit has one argument: the value
-- StrLit has one argument: the string value
-- App has two arguments: the function and the argument
-- Lambda has three arguments: the binder name, the domain, and the body
-- Let has four arguments: the binder name, the domain, the value, and the body
-- Pi has three arguments: the binder name, the domain, and the codomain
-- Proj has three arguments: the structure name, the index, and the expression

-- ExprRef is used to refer to an expression that has already been exported. It has one argument: the index "ei" of the expression in the hashmap.

partial def jsonExpr (e : Expr) : RM String := do
  let st ← get
  -- handle mdata before assigning an index
  if let Expr.mdata _ e := e then
    jsonExpr e
  else
  if st.expr2index.contains e then
    let index := st.expr2index.get! e
    return jsonListAsDict [("tag", json Tag.ExprRef), ("ei", json index)]
  else

  let index := st.expr2index.size
  -- insert the current expression into the hashmap
  modify fun st => { expr2index := st.expr2index.insert e index }
  let json_str : RM String :=
    match e with -- ignoring binder infos
    | .mdata _ _ => panic! "mdata should have been handled"
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
          ("args", jsonListAsDict [("bname", json n), ("domain", rm_d), ("body", rm_b)])
        ]
    | .letE n d v b _ => do
      let rm_d ← jsonExpr d
      let rm_v ← jsonExpr v
      let rm_b ← jsonExpr b
      return jsonListAsDict
        [
          ("tag", json Tag.Let),
          ("ei", json index),
          ("args", jsonListAsDict [("bname", json n), ("domain", rm_d), ("val", rm_v), ("body", rm_b)])
        ]
    | .forallE n d b _bi => do
      let rm_d ← jsonExpr d
      let rm_b ← jsonExpr b
      return jsonListAsDict
        [
          ("tag", json Tag.Pi),
          ("ei", json index),
          ("args", jsonListAsDict [("bname", json n), ("domain", rm_d), ("codomain", rm_b)])
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

-- For each expression separately, we need to reset the hashmap (since it becomes too large otherwise)
instance : JSONable Expr where json e := (jsonExpr e).run' {}

-- The JSON representation of a ReducibilityHint
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

-- Special case for the JSON representation of a list of level parameters
def jsonNameListAsLevelParamList (ns : List Name) : String := jsonListAsList (ns.map jsonNameAsLevelParam)

-- The JSON representation of a Lean ConstantVal that is used in the JSON representation of all declarations
instance : JSONable ConstantVal where
  json cv :=
    jsonListAsDict [
      ("tag", json Tag.DeclarationInfo),
      ("args", jsonListAsDict [("ciname", json cv.name),("lvl_params", jsonNameListAsLevelParamList cv.levelParams), ("type", json cv.type)])
    ]

-- The JSON representation of a Lean AxiomVal:
-- It has argument: the constant info
instance : JSONable AxiomVal where
  json ai := jsonListAsDict [
    ("tag", json Tag.Axiom),
    ("args", jsonListAsDict [("info", json ai.toConstantVal)])
  ]

-- The JSON representation of a Lean DefinitionVal
-- It has arguments: the constant info, the value of the definition, and the reducibility hint
instance : JSONable DefinitionVal where
  json di :=
    if di.safety != .safe then unreachable!
    else
      jsonListAsDict [
        ("tag", json Tag.Definition),
        ("args", jsonListAsDict [("info", json di.toConstantVal), ("value", json di.value), ("hint", json di.hints)])
      ]

-- The JSON representation of a Lean TheoremVal
-- It has arguments: the constant info and the value of the theorem, i.e., the proof
instance : JSONable TheoremVal where
  json ti :=
    jsonListAsDict [
      ("tag", json Tag.Theorem),
      ("args", jsonListAsDict [("info", json ti.toConstantVal), ("value", json ti.value)])
    ]

-- The JSON representation of a Lean OpaqueVal
-- It has two arguments: the constant info and the value of the opaque definition
-- the only difference between OpaqueVal and DefinitionVal is that opaque declarations should not be unfolded
instance : JSONable OpaqueVal where
  json oi :=
    jsonListAsDict [
      ("tag", json Tag.Opaque),
      ("args", jsonListAsDict [("info", json oi.toConstantVal), ("value", json oi.value)])
    ]

-- The JSON representation of a Lean QuotVal
-- It has argument: the constant info
instance : JSONable QuotVal where
  json qi :=
    jsonListAsDict [
      ("tag", json Tag.Quot),
      ("args", jsonListAsDict [("info", json qi.toConstantVal)])
    ]

-- The JSON representation of a Lean InductiveVal
-- It has arguments: the constant info, whether the inductive type is recursive, the number of parameters of the inductive type, the number of indices of the inductive type, the list of all inductive names, and the list of the corresponding constructor names
instance : JSONable InductiveVal where
  json ii :=
    jsonListAsDict [
      ("tag", json Tag.Inductive),
      ("args", jsonListAsDict [("info", json ii.toConstantVal), ("is_recursive", json ii.isRec), ("num_params", json ii.numParams), ("num_indices", json ii.numIndices), ("inductive_names", jsonListAsList (ii.all.map json)), ("constructor_names", jsonListAsList ii.ctors)])
    ]

-- The JSON representation of a Lean ConstructorVal
-- It has arguments: the constant info, the inductive name, the constructor index in the inductive type
instance : JSONable ConstructorVal where
  json ci :=
   jsonListAsDict [("tag", json Tag.Constructor),
    ("args", jsonListAsDict [("info", json ci.toConstantVal), ("inductive_name", json ci.induct), ("c_index", json ci.cidx), ("num_params", json ci.numParams), ("num_fields", json ci.numFields)])
  ]

-- The JSON representation of a Lean RecursorRule
-- It has arguments: the constructor name, the number of fields of the constructor, and the right-hand side of the rule
instance : JSONable RecursorRule where
  json rr :=
    jsonListAsDict [
      ("tag", json Tag.RecursorRule),
      ("args", jsonListAsDict [("constructor", json rr.ctor), ("num_fields", json rr.nfields), ("value", json rr.rhs)]),
    ]

-- The JSON representation of a Lean RecursorVal
-- It has arguments: the constant info, the number of parameters of the recursor, the number of indices of the recursor, the number of motives of the recursor, the number of minors of the recursor, the list of recursor rules, and whether the recursor is a K-recursor (if it supports axiom K)
instance : JSONable RecursorVal where
  json ri :=
    -- what about ri.all?
    jsonListAsDict [
      ("tag", json Tag.Recursor),
      ("args", jsonListAsDict [("info", json ri.toConstantVal), ("num_params", json ri.numParams), ("num_indices", json ri.numIndices), ("num_motives", json ri.numMotives), ("num_minors", json ri.numMinors), ("recursor_rules", jsonListAsList ri.rules), ("isK", json ri.k)])
    ]

-- The JSON representation of a Lean ConstantInfo
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
