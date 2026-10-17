module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find PowerOfFew Basic -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all Basic.Analysis.GridNet
import all Basic.Analysis.SpecialFunctions.CubeRoot
import all Basic.Analysis.SpecialFunctions.ExpLog
import all Basic.Combinatorics.Choose
import all Basic.Probability.BernoulliFamily
import all Basic.Probability.Chernoff
import all Basic.Probability.Concentration
import all Basic.Probability.WeightedBernoulli
import all PowerOfFew.Defs
import all PowerOfFew.Dense.Appendix
import all PowerOfFew.Dense.BinomialDifference
import all PowerOfFew.Dense.DayOne
import all PowerOfFew.Dense.Main
import all PowerOfFew.Dense.Shrinking
import all PowerOfFew.External.FeigeOfek.Defs
import all PowerOfFew.External.FeigeOfek.FeigeOfek
import all PowerOfFew.External.FeigeOfek.Heavy
import all PowerOfFew.External.FeigeOfek.Light
import all PowerOfFew.External.FeigeOfek.Properties
import all PowerOfFew.External.FeigeOfek.SixCases
import all PowerOfFew.External.GolesOlivos.GolesOlivos
import all PowerOfFew.External.RandomMatrix.RandomMatrix
import all PowerOfFew.Model.BerryEsseen
import all PowerOfFew.Model.EdgeConditioning
import all PowerOfFew.Model.Gnp
import all PowerOfFew.Model.Lazy
import all PowerOfFew.Model.Majority
import all PowerOfFew.Model.Normal
import all PowerOfFew.Sparse.Activation
import all PowerOfFew.Sparse.ActivationCounterexample
import all PowerOfFew.Sparse.ActivationDayOne
import all PowerOfFew.Sparse.ActivationLastDays
import all PowerOfFew.Sparse.ActivationShrinking
import all PowerOfFew.Sparse.BerryEsseen
import all PowerOfFew.Sparse.Chernoff
import all PowerOfFew.Sparse.ColoringAux
import all PowerOfFew.Sparse.DayOne
import all PowerOfFew.Sparse.DayThree
import all PowerOfFew.Sparse.DayTwo
import all PowerOfFew.Sparse.Degrees
import all PowerOfFew.Sparse.Main
import all PowerOfFew.Sparse.MatrixNorm
import all PowerOfFew.Sparse.RandomColoring
import all PowerOfFew.Sparse.Subconnectivity
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`PowerOfFew/External/`, `Basic/`) that it uses, whether proved there or, in a conditional
formalization, assumed as hypotheses of its statement. It then checks every declaration
of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `route_check.py` (in the skill's `scripts/`) compares these routes with the
results that the paper's proofs cite.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the libraries' root
names in `isLibraryModule`: the paper's library and `Basic`, the library of general mathematics.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `PowerOfFew/External/`
or, when general, in `Basic/`, and, in a conditional formalization, the propositions assumed as
hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Berry–Esseen, Shevtsova 2010 (assumed)", ``PowerOfFew.ShevtsovaBerryEsseen),
   ("Feige–Ofek 2005", ``PowerOfFew.FeigeOfek.feigeOfek),
   ("Benaych-Georges–Bordenave–Knowles Thm 3.2 (not assumed)", ``PowerOfFew.BBKTheorem3_2),
   ("Boucheron–Lugosi–Massart Thm 6.10 (not assumed)", ``PowerOfFew.BLMTheorem6_10),
   ("Hoeffding (upper tail)", ``ProbabilityTheory.measureReal_sum_ge_add_le_exp),
   ("Hoeffding (lower tail)", ``ProbabilityTheory.measureReal_sum_le_sub_le_exp),
   ("Chernoff (relative entropy)", ``ProbabilityTheory.IsBernoulliFamily.measureReal_sum_le_le_exp_klBern),
   ("Chernoff (upper tail)", ``ProbabilityTheory.IsBernoulliFamily.measureReal_sum_ge_le_exp),
   ("Chernoff (lower tail)", ``ProbabilityTheory.IsBernoulliFamily.measureReal_sum_le_le_exp),
   ("Matoušek–Nešetřil Prop 2.6.2", ``Nat.centralBinom_lt_four_pow_div_sqrt),
   ("C(n, k) ≤ exp(n H(k/n)) (Stirling)", ``Nat.choose_le_exp_mul_binEntropy),
   ("Goles–Olivos, Poljak–Sůra", ``PowerOfFew.blueAfter_eventually_period_two)]

/-- The numbered results of the paper, in the order of the paper. -/
meta def paperResults : List (String × Name) :=
  [("D Thm 1.2", ``PowerOfFew.Dense.theorem1_2),
   ("D Thm 1.3", ``PowerOfFew.Dense.theorem1_3),
   ("D Thm 1.5", ``PowerOfFew.Dense.theorem1_5),
   ("D Thm 1.6", ``PowerOfFew.Dense.theorem1_6),
   ("D Lemma 2.1", ``PowerOfFew.Dense.lemma2_1),
   ("D Thm 2.2 (Berry–Esseen)", ``PowerOfFew.ShevtsovaBerryEsseen),
   ("D Lemma 2.3", ``PowerOfFew.Dense.lemma2_3),
   ("D Lemma 2.4", ``PowerOfFew.Dense.lemma2_4),
   ("D Claim 2.5", ``PowerOfFew.Dense.claim2_5),
   ("D Claim 2.6", ``PowerOfFew.Dense.claim2_6),
   ("D Thm 3.1 (Hoeffding)", ``ProbabilityTheory.measureReal_sum_ge_add_le_exp),
   ("D Lemma 3.2", ``PowerOfFew.Dense.lemma3_2),
   ("D Lemma 3.3", ``PowerOfFew.Dense.lemma3_3),
   ("D Lemma 3.4", ``PowerOfFew.Dense.lemma3_4),
   ("D Lemma 3.5", ``PowerOfFew.Dense.lemma3_5),
   ("D Lemma 3.6", ``PowerOfFew.Dense.lemma3_6),
   ("D App. A", ``PowerOfFew.Dense.appendixA),
   ("S Thm 1.2", ``PowerOfFew.Sparse.theorem1_2),
   ("S Thm 1.4", ``PowerOfFew.Sparse.theorem1_4),
   ("S Thm 1.5", ``PowerOfFew.Sparse.theorem1_5),
   ("S Thm 1.7", ``PowerOfFew.Sparse.theorem1_7),
   ("S Lemma 2.1", ``PowerOfFew.Sparse.lemma2_1),
   ("S Prop 2.2", ``PowerOfFew.Sparse.proposition2_2),
   ("S Lemma 2.3", ``PowerOfFew.Sparse.lemma2_3),
   ("S Lemma 2.4", ``PowerOfFew.Sparse.lemma2_4),
   ("S Lemma 2.5", ``PowerOfFew.Sparse.lemma2_5),
   ("S Lemma 2.6", ``PowerOfFew.Sparse.lemma2_6),
   ("S Thm 3.1", ``PowerOfFew.Sparse.theorem3_1),
   ("S Thm 4.1", ``PowerOfFew.Sparse.theorem4_1),
   ("S Prop 4.2", ``PowerOfFew.Sparse.proposition4_2),
   ("S Prop 4.3", ``PowerOfFew.Sparse.proposition4_3),
   ("S Prop 4.4", ``PowerOfFew.Sparse.proposition4_4),
   ("S Thm A.1 (Berry–Esseen)", ``PowerOfFew.ShevtsovaBerryEsseen),
   ("S Cor A.2", ``PowerOfFew.Sparse.corollaryA_2),
   ("S Lemma A.3", ``PowerOfFew.Sparse.lemmaA_3),
   ("S Lemma A.4", ``PowerOfFew.Sparse.lemmaA_4),
   ("S Lemma A.5", ``PowerOfFew.Sparse.lemmaA_5),
   ("S Lemma A.6", ``PowerOfFew.Sparse.lemmaA_6),
   ("S Lemma A.7", ``PowerOfFew.Sparse.lemmaA_7)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``Challenge.dense_theorem1_6,
   ``Challenge.dense_theorem1_2,
   ``Challenge.dense_theorem1_3,
   ``Challenge.sparse_theorem1_2,
   ``Challenge.sparse_theorem1_4,
   ``Challenge.sparse_theorem1_5,
   ``Challenge.sparse_theorem1_5_printed_false,
   ``Challenge.sparse_theorem3_1,
   ``Challenge.sparse_theorem1_7,
   ``Challenge.sparse_theorem4_1,
   ``Challenge.sparse_theorem1_7_printed_false_seq,
   ``Challenge.sparse_theorem4_1_printed_false_seq,
   ``Challenge.Φ_eq_cdf_gaussianReal]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: the paper's, or `Basic`. -/
meta def isLibraryModule (m : Name) : Bool := (`PowerOfFew).isPrefixOf m || (`Basic).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
