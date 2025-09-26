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
    Within that cluster the tool tries to place callers before callees and
    pack callees immediately below their callers when possible.
  - Emit free functions that "use" the type (functions that reference the
    type in a signature/body or call the type's constructors/methods).

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
- Users: free functions that reference a type (in params/results/struct
  fields or body) or that call the type's constructors/methods. Users are
  emitted after the type's methods/constructors cluster.
- Independent free functions: non-methods that are not constructors and have
  no incoming or outgoing call edges within the file.

Ordering constraints and algorithms

- Caller-before-callee: the ordering algorithms add predecessor edges so
  that every caller precedes its callee. The output guarantees this where
  possible.
- Call sequencing: if a function calls A then B in that order, the tool
  records that sequence and prefers to keep A before B when both are in the
  reordering subset.
- Minimal movement: reorders try to move as little as possible from the
  original layout (stable sort by original offsets is used as a base).
- Packing: within clusters (methods/helpers or call-graph components) the
  emitter will "pack" callees directly beneath their callers when it can
  while still respecting predecessor and call-sequence constraints.

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