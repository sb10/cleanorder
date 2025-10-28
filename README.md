# cleanorder
Reorder go source code files in clean coding order (caller-before-callee).

Use -dry to print the new version to STDOUT. Without -dry, it edits files
in place.


Ordering rules implemented

This tool reorders declarations in a single Go source file to follow a
caller-before-callee, readability-driven layout while making minimal
textual movement and preserving original grouping/spacing where possible.
Below is a succinct summary of the rules and classifications the program
applies when producing output.

High-level emission order

- Package header, imports and file-level comments are preserved at the top.
- All `const`/`var` declaration blocks are emitted next, in original order,
  separated by blank lines.
- "Independent" free functions (non-methods that have no calls to or from
  other functions in the file and are not constructors named `New*`) are
  emitted next in their original order.
- For each named type declared in the file (in source order):
  - Emit the `type` declaration (once).
  - Emit constructor functions for that type (free functions named `NewX`
    that return `X` or `*X`). Constructors keep their original order.
  - Emit the type's methods and their helper functions as a clustered group.
	Within that cluster, helpers are placed directly after the first method
	that calls them (callee-after-first-caller). If a helper is called by
	multiple methods, it is still anchored under the chosen first caller; the
	later callers do not force the helper to move further down.
	Note: A free function that is used as a method helper is not treated as a
	generic "user" of any types it happens to reference. This prevents helpers
	(e.g., readBody/handleError used by ServeHTTP) from being emitted before
	their first caller in another type’s user section.
  - Emit functions and methods that "use" the type (any function or method
    that references the type in a signature/body or calls the type's
    constructors/methods). If the type has no constructors or methods, its
    users are still emitted immediately after the type declaration.

- Any remaining `type` blocks that weren't emitted in the typed loop are
  written next.
- Remaining free functions are emitted by connected components of the
  call graph. Each component is ordered so callers appear before callees
  and local call order is preserved; components and intra-component items
  otherwise retain original ordering as a tie-breaker.

Classification rules used by the emitter

- Constructors: free functions named `New...` that have results mentioning
  a declared type in this file (allows pointer returns `*T`).
- Methods: functions with a receiver whose base type matches a declared
  type in this file.
- Helpers: free functions that are called by methods of a given type. These
  are grouped with the type's methods so related helpers appear near the
  methods that reference them.
- Users: functions and methods that reference a type (in
  params/results/struct fields or body) or that call the type's
  constructors/methods. Users are emitted after the type's
  methods/constructors cluster, or directly after the type when there are no
  methods/constructors.
  - Incidental types: when a type has no constructors or methods and its only
    users are methods whose receiver types are not declared in the same file,
    the type declaration is considered incidental and is emitted immediately
    before the first such user instead of anchoring its own section. This
    prevents incidental return/parameter types from disrupting grouping and the
    callee-after-first-caller ordering within the receiver's method cluster.
- Independent free functions: non-methods that are not constructors and have
  no incoming or outgoing call edges within the file.

Ordering constraints and algorithms

- Callee-after-first-caller (within clusters): for helpers grouped under a
  type's methods, each helper is anchored immediately beneath a single
  designated first caller. When a helper has multiple callers among the
  methods, the first caller is chosen as the method that calls the most
  helpers (ties broken by earliest appearance). Other callers do not impose
  additional predecessor constraints on that helper inside the cluster.
  Outside of clusters (e.g., among free functions), callers still precede
  their callees as before.
  - Precedence: the callee-after-first-caller rule for a type's method cluster
    takes precedence over incidental standalone type declarations that happen
    to be referenced or returned by those methods. Such incidental types are
    inlined immediately above the first using method and do not form their own
    user section.
- Call sequencing: if a function calls A then B in that order, the tool
  records that sequence and prefers to keep A before B when both are in the
  reordering subset.
- Minimal movement: reorders try to move as little as possible from the
  original layout (stable sort by original offsets is used as a base).
- Packing: within clusters, helpers are packed contiguously under their first
  caller in the order the caller first uses them. Among remaining reordering
  regions, packing behaves as before while respecting constraints.

Tie-breakers

- When ordering is otherwise unconstrained, exported (public) functions and
  methods are preferred over unexported (private). Within each group, original
  file order is preserved. This applies across independent functions, call-graph
  components, and type users.

Limitations (brief)

- Analysis is file-local: it recognizes calls by identifier/selector name but
  does not fully resolve cross-package symbols or handle shadowing across
  multiple files in a package. Selector-based calls use only the selector
  name (package qualification is ignored).
- The tool is conservative about detection of constructors and "uses" of a
  type (it looks in signatures and the function body for identifier matches).

These rules are intentionally conservative to avoid breaking code while
improving readability by grouping related declarations and ensuring callers
come before the functions they call.

Comment handling

- Doc comments (// or /* */) that are attached to a declaration are emitted
  with that declaration. The tool ensures the file header (package/imports) is
  split from the first declaration at the declaration's doc start to avoid
  duplicating the doc text when reordering.
- Inline trailing comments that appear on the same line as a declaration or a
  function's closing brace (for example, //nolint) are preserved on that same
  line in the output.