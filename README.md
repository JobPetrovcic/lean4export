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

### The `content` Object

The `content` object's structure depends on the type of declaration. It always includes a `tag` field indicating the declaration type. Here are the possible tags and their associated fields:

*   **`Axiom`**:
    *   `name`: The name of the axiom.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the axiom's type (an `Expr`).

*   **`Definition`**:
    *   `name`: The name of the definition.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the definition's type (`Expr`).
    *   `value`: The JSON representation of the definition's value (`Expr`).
    *   `hints`: The reducibility hint (`abbrev`, `regular`, or `opaque`).

*   **`Theorem`**:
    *   `name`: The name of the theorem.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the theorem's type (`Expr`).
    *   `value`: The JSON representation of the theorem's proof (`Expr`).

*   **`Opaque`**:
    *   `name`: The name of the opaque constant.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the type (`Expr`).
    *   `value`: The JSON representation of the value (`Expr`).

*   **`Inductive`**:
    *   `name`: The name of the inductive type.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the type (`Expr`).
    *   `numParams`: The number of parameters.
    *   `numIndices`: The number of indices.
    *   `all`: A list of all inductive type names in the same mutual block.
    *   `ctors`: A list of constructor names for this inductive type.
    *   `isRec`: A boolean indicating if it is a recursive inductive type.

*   **`Constructor`**:
    *   `name`: The name of the constructor.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the constructor's type (`Expr`).
    *   `induct`: The name of the inductive type this constructor belongs to.
    *   `cidx`: The index of this constructor within the inductive type.
    *   `numParams`: The number of parameters for the constructor.
    *   `numFields`: The number of fields for the constructor.

*   **`Recursor`**:
    *   `name`: The name of the recursor.
    *   `levelParams`: A list of level parameter names.
    *   `type`: The JSON representation of the recursor's type (`Expr`).
    *   `all`: A list of all inductive types in the mutual block.
    *   `numParams`: The number of parameters.
    *   `numIndices`: The number of indices.
    *   `numMotives`: The number of motives.
    *   `numMinors`: The number of minor premises.
    *   `rules`: A list of recursor rules.
    *   `k`: A boolean indicating if it is a K-recursor.

### Expression (`Expr`) Format

Lean expressions (`Expr`) are represented as nested JSON objects. To handle cycles and reduce redundancy, expressions that appear multiple times are referenced by an index `ei`.

Each expression object has a `tag` and other properties depending on the tag. For example:
*   `{"tag": "Const", "name": "Nat", "levels": []}`
*   `{"tag": "App", "fn": {...}, "arg": {...}}`

If an expression has been seen before, it is represented as:
*   `{"tag": "ExprRef", "ei": <index>}`
