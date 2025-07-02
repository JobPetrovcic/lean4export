import Lean
import Init.Data.List.Basic
open Lean

-- get all the constants used in an expression
def getDepsExpr (e : Expr) : List Name :=
  let depsArray := e.getUsedConstants
  depsArray.toList

-- a function that takes a ConstantInfo and returns a list of the names of the constants it depends on
def getDeclarationDepsRaw : ConstantInfo → List Name
  | .axiomInfo val =>
    let typeDeps := getDepsExpr val.type
    typeDeps
  | .defnInfo val =>
    let typeDeps := getDepsExpr val.type
    let valueDeps := getDepsExpr val.value
    typeDeps ++ valueDeps
  | .thmInfo val =>
    let typeDeps := getDepsExpr val.type
    let valueDeps := getDepsExpr val.value
    typeDeps ++ valueDeps
  | .opaqueInfo val =>
    let typeDeps := getDepsExpr val.type
    let valueDeps := getDepsExpr val.value
    typeDeps ++ valueDeps
  | .quotInfo val =>
    let typeDeps := getDepsExpr val.type
    typeDeps
  | .inductInfo val =>
    let typeDeps := getDepsExpr val.type
    val.ctors ++ typeDeps
  | .ctorInfo val =>
    let typeDeps := getDepsExpr val.type
    typeDeps
  | .recInfo val =>
    let typeDeps := getDepsExpr val.type
    let ruleDeps := val.rules.map (fun rule => getDepsExpr rule.rhs)
    typeDeps ++ ruleDeps.join

-- same as getDeclarationDepsRaw but removes duplicates
def getDeclarationDeps (c : ConstantInfo) : List Name :=
  let deps := getDeclarationDepsRaw c
  deps.eraseDups
