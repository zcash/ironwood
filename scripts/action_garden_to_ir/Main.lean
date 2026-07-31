import Lean

open Lean

namespace ActionGardenToIR

private def sourceInfoJson : SourceInfo → Json
  | .original _ start _ stop =>
      Json.mkObj [
        ("start", toJson start.byteIdx),
        ("stop", toJson stop.byteIdx)
      ]
  | .synthetic start stop canonical =>
      Json.mkObj [
        ("start", toJson start.byteIdx),
        ("stop", toJson stop.byteIdx),
        ("synthetic", toJson true),
        ("canonical", toJson canonical)
      ]
  | .none => Json.null

private partial def syntaxJson : Syntax → Json
  | .missing => Json.mkObj [("tag", "missing")]
  | .atom info value =>
      Json.mkObj [
        ("tag", "atom"),
        ("value", value),
        ("span", sourceInfoJson info)
      ]
  | .ident info raw value _ =>
      Json.mkObj [
        ("tag", "ident"),
        ("raw", raw.toString),
        ("value", value.toString),
        ("span", sourceInfoJson info)
      ]
  | .node info kind args =>
      Json.mkObj [
        ("tag", "node"),
        ("kind", kind.toString),
        ("span", sourceInfoJson info),
        ("args", Json.arr (args.map syntaxJson))
      ]

private partial def forbiddenBeforeElaboration? : Syntax → Option Name
  | .node _ kind args =>
      if kind.toString == "Lean.Parser.Term.byTactic" ||
          kind.toString == "Lean.Parser.Term.attributes" then
        some kind
      else
        args.findSome? forbiddenBeforeElaboration?
  | _ => none

private partial def identifierTexts : Syntax → List String
  | .ident _ raw _ _ => [raw.toString]
  | .node _ _ args =>
      args.toList.flatMap identifierTexts
  | _ => []

private partial def importedModules : Syntax → List String
  | .node _ kind args =>
      if kind.toString == "Lean.Parser.Module.import" then
        identifierTexts (.node SourceInfo.none kind args)
      else
        args.toList.flatMap importedModules
  | _ => []

private def validateBeforeElaboration (stx : Syntax) : Except String Unit := do
  if stx.getKind.toString != "Lean.Parser.Module.module" then
    throw "expected a parsed Lean module"
  let args := stx.getArgs
  if args.size != 2 then
    throw "unexpected Lean module shape"
  let imports := importedModules args[0]!
  if imports != ["Init.Prelude"] then
    throw s!"standalone source must import exactly Init.Prelude; found {imports}"
  let allowed : List String := [
    "Lean.Parser.Command.moduleDoc",
    "Lean.Parser.Command.namespace",
    "Lean.Parser.Command.declaration",
    "Lean.Parser.Command.in",
    "Lean.Parser.Command.end",
    "Lean.Parser.Command.eoi"
  ]
  for command in args[1]!.getArgs do
    unless allowed.contains command.getKind.toString do
      throw s!"unsupported top-level command {command.getKind}"
    if let some kind := forbiddenBeforeElaboration? command then
      throw s!"unsupported pre-elaboration syntax {kind}"

unsafe def main (args : List String) : IO UInt32 := do
  let some input := args.head?
    | IO.eprintln "usage: actionGardenToIR INPUT.lean"
      return 2
  if args.length != 1 then
    IO.eprintln "usage: actionGardenToIR INPUT.lean"
    return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} 0
    (loadExts := true)
  enableInitializersExecution
  let contents ← IO.FS.readFile input
  -- Parse the immutable in-memory snapshot first. Elaboration below consumes
  -- these exact bytes, and the same syntax tree is what the emitter receives.
  let stx ← Parser.testParseModule env input contents
  match validateBeforeElaboration stx with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok () => pure ()
  let options := ({} : Options).setBool `autoImplicit false
  let some _ ← Elab.runFrontend
      contents options input `ActionGardenTranslation
    | IO.eprintln "ActionGarden source did not elaborate"
      return 1
  let output := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("source", toJson input),
    ("contents", toJson contents),
    ("syntax", syntaxJson stx)
  ]
  IO.println output.compress
  return 0

end ActionGardenToIR

unsafe def main := ActionGardenToIR.main
