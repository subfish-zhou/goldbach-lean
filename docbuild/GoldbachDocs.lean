import DocGen4

/-!
# Project-only API documentation

Use doc-gen4's analyzer, HTML renderer, and search-index writer without its
recursive Lake `:docs` facet. Imported declarations remain in the linking
context, but only explicitly selected project modules are rendered. The Python
build driver routes dependency links to upstream documentation afterwards.
-/

open Lean DocGen4 DocGen4.Output

private def readModules (path : System.FilePath) : IO (Array Name) := do
  return (← IO.FS.readFile path).splitOn "\n"
    |>.filter (· != "") |>.map String.toName |>.toArray

private def renderModule (buildDir : System.FilePath) (modules : Array Name)
    (mod : Name) (sourceRoot : String) : IO Unit := do
  let result ← load (.analyzeConcreteModules #[mod])
  let base ← getSimpleBaseContext buildDir (Hierarchy.fromArray modules)
  let config : SiteContext := {
    result
    sourceLinker := fun name =>
      SourceLinker.mkGithubSourceLinker
        (sourceRoot ++ "/" ++ "/".intercalate (name.components.map toString) ++ ".lean")
    refsMap := {}
  }
  let some info := result.moduleInfo[mod]?
    | throw (IO.userError s!"No documentation information for {mod}")
  let modConfig := { base with
    depthToRoot := mod.components.dropLast.length
    currentName := some mod }
  let (html, state) := moduleToHtml info |>.run {} config modConfig
  unless state.errors.isEmpty do
    throw (IO.userError s!"Documentation errors for {mod}: {state.errors}")
  let file := basePath buildDir / moduleNameToFile mod
  if let some parent := file.parent then IO.FS.createDirAll parent
  IO.FS.writeFile file html.toString
  IO.FS.createDirAll (declarationsBasePath buildDir)
  IO.FS.writeFile (declarationsBasePath buildDir / s!"backrefs-{mod}.json")
    (toJson state.backrefs).compress
  let (json, _) := moduleToJsonModule info |>.run {} config base
  IO.FS.writeFile (declarationsBasePath buildDir / s!"declaration-data-{mod}.bmp")
    (toJson json).compress

private def renderIndex (buildDir : System.FilePath) (modules : Array Name) : IO Unit := do
  let base ← getSimpleBaseContext buildDir (Hierarchy.fromArray modules)
  -- The upstream index writer merges the per-module data produced above.
  htmlOutputIndex base #[] #[]
  headerDataOutput buildDir

def main (args : List String) : IO UInt32 := do
  match args with
  | ["module", build, manifest, mod, sourceRoot] =>
    renderModule build (← readModules manifest) mod.toName sourceRoot
    return 0
  | ["index", build, manifest] =>
    renderIndex build (← readModules manifest)
    return 0
  | _ =>
    IO.eprintln "Usage: goldbach-docs module BUILD MANIFEST MODULE SOURCE_ROOT | index BUILD MANIFEST"
    return 1
