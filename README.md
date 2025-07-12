# Lean 4 Declaration Exporter

This tool exports Lean 4 declarations and their dependencies to a structured JSON format. It was designed to be efficient enough to export the entire Mathlib 4 library.

## Quick Startup

This guide provides the minimal steps to use this tool within your own Lean project.

1.  **Prerequisites**: Ensure you have a working Lean 4 project.

2.  **Add as a dependency**: Add this package to your project's `lakefile.lean`.
    ```lean
    require lean4export from git "https://github.com/JobPetrovcic/lean4export.git" @ "json"
    ```

3.  **Build your project**: Update your dependencies and build your project.
    ```bash
    lake update
    lake build
    ```

4.  **Run the exporter**: Execute the main program to export declarations. The basic command structure is:
    ```bash
    lake exe lean4export <output_directory> <lean_module>
    ```
    For example, to export all declarations from `Mathlib.Data.Nat.Basic` into a directory named `data` (NOTE: the directory must exist), run:
    ```bash
    lake exe lean4export data Mathlib.Data.Nat.Basic
    ```
    This will populate the directory with JSON files, one for each declaration in `Mathlib.Data.Nat.Basic` and its dependencies.

## Using Arguments

The program's behavior can be customized using command-line arguments.

The general syntax is:
```bash
lake exe lean4export <outDir> [imports...] [-- constants...]
```

*   `<outDir>`: (Required) The path to the directory where the output JSON files will be stored.
*   `[imports...]`: (Required) A space-separated list of Lean modules to process. The tool will export declarations from these modules.
*   `--`: An optional separator. (NOTE: after the double dash a space is required)
*   `[constants...]`: An optional list of specific constant names to export. If this list is provided, only these constants and their dependencies will be exported. If omitted, all non-internal declarations from the specified `imports` will be exported.

### Example

To export only the `Nat.add` and `Nat.mul` declarations from `Mathlib.Data.Nat.Basic` into a directory named `data`, use the following command:

```bash
lake exe lean4export data Mathlib.Data.Nat.Basic -- Nat.add Nat.mul
```

## JSON Output Format

The tool generates one JSON file per declaration. The filename is a "file-friendly" version of the declaration's name (e.g., `/` is replaced by a space, since spaces cannot appear in names coming from Lean).

Each JSON file contains a top-level object with two properties:

*   `dependencies`: A list of strings representing the names of other declarations that the current declaration depends on. These names are also made file-friendly.
*   `content`: An object containing the detailed information about the declaration.

## Lean Export JSON Format

This document describes the JSON format for serializing Lean 4 declarations. The format uses a consistent structure of tagged unions, where each object has a `tag` field indicating its type and an `args` field containing its data.

### Top-Level Declaration Format

Every exported declaration is a JSON object with a `tag` and an `args` field. Most declarations share common information (name, level parameters, and type), which is encapsulated within a nested `DeclarationInfo` object.

#### Common Object: `DeclarationInfo`

This object contains the base information for a constant.

*   **`tag`**: `DeclarationInfo`
*   **`args`**:
    *   `ciname`: The JSON representation of the declaration's `Name`.
    *   `lvl_params`: A list of `Level` objects representing the universe level parameters.
    *   `type`: The JSON representation of the declaration's type (an `Expr`).

---

The following are the possible top-level declaration tags:

*   **`Axiom`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the axiom.

*   **`Definition`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the definition.
        *   `value`: The JSON representation of the definition's value (`Expr`).
        *   `hint`: A `ReducibilityHint` JSON object.

*   **`Theorem`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the theorem.
        *   `value`: The JSON representation of the theorem's proof (`Expr`).

*   **`Opaque`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the opaque constant.
        *   `value`: The JSON representation of the value (`Expr`).

*   **`Quot`**: Represents a quotient type declaration.
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the quotient type.

*   **`Inductive`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the inductive type.
        *   `is_recursive`: A boolean indicating if it is a recursive inductive type.
        *   `num_params`: The number of parameters.
        *   `num_indices`: The number of indices.
        *   `inductive_names`: A list of all inductive type `Name` objects in the same mutual block.
        *   `constructor_names`: A list of constructor `Name` objects for this inductive type.

*   **`Constructor`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` object for the constructor.
        *   `inductive_name`: The `Name` of the inductive type this constructor belongs to.
        *   `c_index`: The index of this constructor within the inductive type.
        *   `num_params`: The number of parameters for the constructor.
        *   `num_fields`: The number of fields for the constructor.

*   **`Recursor`**:
    *   `args`:
        *   `info`: A `DeclarationInfo` JSON object for the recursor.
        *   `num_params`: The number of parameters.
        *   `num_indices`: The number of indices.
        *   `num_motives`: The number of motives.
        *   `num_minors`: The number of minor premises.
        *   `recursor_rules`: A list of `RecursorRule` objects.
        *   `isK`: A boolean indicating if it is a K-recursor.
    For more information about recursors and inductive types in Lean, see (https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html).
    

### Core Data Structures

#### Name (`Name`) Format

Names are represented as a recursive structure.

*   **`Anonymous`**: The anonymous root name.
    *   `args`: An empty object `{}`.
*   **`SubName`**: A name component (string or number) extending a prefix name.
    *   `args`:
        *   `str`: The string representation of this part of the name.
        *   `anc`: The `Name` object of the prefix/ancestor.

#### Expression (`Expr`) Format

Lean expressions (`Expr`) are represented as nested JSON objects. To reduce redundancy, every unique expression is assigned a numerical index (`ei`). Then, ExprRef refers to a duplicate expression that was already exported by this index.

**General Expr Structure:**

*   **First Occurrence:** When an expression is first seen, it is fully serialized:
    *   `tag`: The kind of expression (e.g., `Const`, `App`).
    *   `ei`: A unique integer index assigned to this expression.
    *   `args`: An object containing data specific to this expression tag.

*   **Reference:** Any subsequent time the same expression is needed, it is represented by a reference:
    *   `tag`: `ExprRef`
    *   `ei`: The index of the expression being referenced.

**Expression Tags and their `args`:**

*   **`BVar`** (Bound Variable):
    *   `db_index`: The de Bruijn index of the variable.

*   **`Sort`**:
    *   `level`: The `Level` object for the sort.

*   **`Const`**:
    *   `cname`: The `Name` of the constant.
    *   `lvl_params`: A list of `Level` objects for the universe parameters.

*   **`NatLit`**:
    *   `val`: The integer value of the natural number literal.

*   **`StrLit`**:
    *   `val`: The string value of the literal.

*   **`App`**:
    *   `fn`: The function `Expr`.
    *   `arg`: The argument `Expr`.

*   **`Lambda`**:
    *   `bname`: The `Name` of the binder.
    *   `domain`: The domain (type) `Expr` of the binder.
    *   `body`: The body `Expr` of the lambda.

*   **`Pi`** (Dependent Function Type):
    *   `bname`: The `Name` of the binder.
    *   `domain`: The domain `Expr` of the binder.
    *   `codomain`: The body `Expr` of the pi-type.

*   **`Let`**:
    *   `bname`: The `Name` of the binder.
    *   `domain`: The type `Expr` of the let-binding.
    *   `val`: The value `Expr` of the let-binding.
    *   `body`: The body `Expr` of the let-expression.

*   **`Proj`** (Projection):
    *   `sname`: The `Name` of the instance's structure.
    *   `index`: The index of the field to project.
    *   `expr`: The `Expr` of the structure instance.

#### Level (`Level`) Format

*   **`LevelZero`**: The ground universe `Level`.
    *   `args`: An empty object `{}`.
*   **`LevelSucc`**: The successor of a level.
    *   `args`:
        *   `anc`: The predecessor `Level` object.
*   **`LevelMax`**: The maximum of two levels.
    *   `args`:
        *   `lhs`: The first `Level` object.
        *   `rhs`: The second `Level` object.
*   **`LevelIMax`**: The "impredicative" maximum of two levels.
    *   `args`:
        *   `lhs`: The first `Level` object.
        *   `rhs`: The second `Level` object.
*   **`LevelParam`**: A universe parameter.
    *   `args`:
        *   `pname`: The `Name` of the level parameter.

#### Other Structures

*   **`ReducibilityHint`**: a hint for the kernel whether or how much to unfold a definition
    *   **`OpaqueHint`**: `{"tag": "OpaqueHint", "args": {}}`
    *   **`Abbrev`**: `{"tag": "Abbrev", "args": {}}`
    *   **`Regular`**: `{"tag": "Regular", "args": {"depth": <number>}}`

*   **`RecursorRule`**: Describes a rule for a recursor.
    *   `tag`: `RecursorRule`
    *   `args`:
        *   `constructor`: The `Name` of the constructor this rule applies to.
        *   `num_fields`: The number of fields for the constructor.
        *   `value`: The right-hand-side `Expr` of the rule.

### Example
The definition `exported_example`
```lean
def export_example: Sort 1 := Sort 0
```

is exported as

```json
{"dependencies": [], "content": {"tag": "Definition", "args": {"info": {"tag": "DeclarationInfo", "args": {"ciname": {"tag": "SubName", "args": {"str": "export_example", "anc": {"tag": "Anonymous", "args": {}}}}, "lvl_params": [], "type": {"tag": "Sort", "ei": 0, "args": {"level": {"tag": "LevelSucc", "args": {"anc": {"tag": "LevelZero", "args": {}}}}}}}}, "value": {"tag": "Sort", "ei": 0, "args": {"level": {"tag": "LevelZero", "args": {}}}}, "hint": {"tag": "Regular", "args": {"depth": 1}}}}}
```
