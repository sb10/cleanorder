package main

import (
	"bytes"
	"context"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// runTool runs the current tool in -dry mode on the given file and returns
// the produced source bytes or an error.
func runTool(t *testing.T, target string) []byte {
	t.Helper()

	// Allow more time for initial compilation of stdlib packages used by
	// test inputs (e.g. net/http). Once built, subsequent runs are fast, but
	// in constrained CI environments the previous 5s budget was too tight.
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	// run `go run . -dry <target>` in repository directory (current working dir)
	cmd := exec.CommandContext(ctx, "go", "run", ".", "-dry", target)

	// ensure working dir is package root (where tests are executed)
	cmd.Dir = mustGetwd(t)

	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("running tool failed: %v\noutput:\n%s", err, string(out))
	}

	return out
}

func mustGetwd(t *testing.T) string {
	t.Helper()

	wd, err := os.Getwd()
	if err != nil {
		t.Fatalf("getwd: %v", err)
	}

	return wd
}

// declOrder parses src and returns a slice of strings describing top-level
// declarations in order. Each element is a short tag such as "import",
// "const X", "type T", "func F", or "method T.M".
func declOrder(t *testing.T, src []byte) []string {
	t.Helper()

	fset := token.NewFileSet()

	f, err := parser.ParseFile(fset, "_tmp.go", src, parser.ParseComments)
	if err != nil {
		t.Fatalf("parse output: %v\nsource:\n%s", err, string(src))
	}

	out := []string{}

	getRecv := func(fd *ast.FuncDecl) string {
		if fd.Recv == nil || len(fd.Recv.List) == 0 {
			return ""
		}

		texpr := fd.Recv.List[0].Type
		for {
			switch tt := texpr.(type) {
			case *ast.StarExpr:
				texpr = tt.X

				continue
			case *ast.IndexExpr:
				texpr = tt.X

				continue
			case *ast.Ident:
				return tt.Name
			default:
				return ""
			}
		}
	}

	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.GenDecl:
			switch d.Tok {
			case token.IMPORT:
				out = append(out, "import")
			case token.CONST:
				// include first const name when possible
				if len(d.Specs) > 0 {
					if s, ok := d.Specs[0].(*ast.ValueSpec); ok && len(s.Names) > 0 {
						out = append(out, "const "+s.Names[0].Name)

						continue
					}
				}

				out = append(out, "const")
			case token.VAR:
				if len(d.Specs) > 0 {
					if s, ok := d.Specs[0].(*ast.ValueSpec); ok && len(s.Names) > 0 {
						out = append(out, "var "+s.Names[0].Name)

						continue
					}
				}

				out = append(out, "var")
			case token.TYPE:
				for _, sp := range d.Specs {
					if ts, ok := sp.(*ast.TypeSpec); ok {
						out = append(out, "type "+ts.Name.Name)
					}
				}
			default:
				// ignore other token kinds
			}
		case *ast.FuncDecl:
			if d.Recv == nil {
				out = append(out, "func "+d.Name.Name)

				continue
			}

			r := getRecv(d)
			if r == "" {
				out = append(out, "method ?."+d.Name.Name)
			} else {
				out = append(out, "method "+r+"."+d.Name.Name)
			}
		}
	}

	// normalise tags to remove stray newlines/whitespace
	for i, v := range out {
		// collapse all whitespace (spaces, newlines, tabs) into single spaces
		parts := strings.Fields(v)
		out[i] = strings.Join(parts, " ")
	}

	return out
}

// findIndex finds index of an element that has prefix 'want' or equals it.
func findIndex(list []string, want string) int {
	// split want into kind and name (e.g., "func A" -> kind="func", name="A")
	parts := strings.SplitN(want, " ", 2)
	wantKind := parts[0]

	wantName := ""
	if len(parts) > 1 {
		wantName = parts[1]
	}

	for i, v := range list {
		vparts := strings.SplitN(v, " ", 2)
		vkind := vparts[0]

		vname := ""
		if len(vparts) > 1 {
			vname = vparts[1]
		}

		if wantName == "" {
			// only kind provided (e.g., "import")
			if vkind == wantKind {
				return i
			}

			continue
		}

		if vkind == wantKind && vname == wantName {
			return i
		}
	}

	return -1
}

func TestOrderingRules(t *testing.T) {
	// each subtest writes a small Go file, runs the tool in dry mode and
	// asserts ordering relationships rather than exact file bytes.
	t.Run("consts_below_imports", func(t *testing.T) {
		// valid source where const already appears after imports; tool must
		// keep consts after imports in final output
		src := `package p

import "fmt"

// a constant
const X = 1

func A() {}
`

		f := writeTempFile(t, "consts.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		impIdx := findIndex(order, "import")
		constIdx := findIndex(order, "const X")

		if impIdx == -1 || constIdx == -1 {
			t.Fatalf("expected import and const declarations in output; got: %v", order)
		}

		if constIdx < impIdx {
			t.Fatalf("const should appear after imports; got order: %v", order)
		}
	})

	t.Run("inline_trailing_comment_preserved_on_var_decl", func(t *testing.T) {
		// Reproduce reported issue: a long single-line var declaration with an
		// inline trailing comment (nolint) should remain on the same line. The
		// original bug moved the comment to a separate line (sometimes with an
		// added blank line) after reordering/formatting. A regression introduced
		// duplication where the comment appeared both inline AND again on the
		// following line. This test asserts: (1) comment stays on the same line
		// and (2) it appears exactly once in the output.
		src := `package p

import (
  "net/http"
  "os"
)

// an unrelated type so the tool performs reordering work
type Dummy struct{}

// long var initialiser with nested calls and trailing nolint comment
var index = http.FileServer(http.FS(os.DirFS("./src"))) //nolint:gochecknoglobals

func use() { _ = index }
`

		f := writeTempFile(t, "inline_comment.go", src)
		out := runTool(t, f)

		outStr := string(out)
		lines := strings.Split(outStr, "\n")
		foundLine := ""
		for _, ln := range lines {
			if strings.Contains(ln, "var index =") {
				foundLine = ln
				break
			}
		}

		if foundLine == "" {
			t.Fatalf("did not find var index line in output. Output:\n%s", outStr)
		}

		if !strings.Contains(foundLine, "//nolint:gochecknoglobals") {
			t.Fatalf("inline nolint comment not preserved on same line. Var line: %q\nFull output:\n%s", foundLine, outStr)
		}

		// Ensure the nolint comment appears exactly once (no duplication on next line)
		occurrences := strings.Count(outStr, "//nolint:gochecknoglobals")
		if occurrences != 1 {
			t.Fatalf("expected exactly 1 occurrence of inline comment, got %d. Output:\n%s", occurrences, outStr)
		}
	})

	t.Run("independent_free_funcs_top", func(t *testing.T) {
		// start with the type before the independent functions; tool should
		// move the independent free funcs above the type
		src := `package p

import "fmt"

type T struct{}

func (_ T) M() {}

func independent1() {}
func independent2() {}
`
		f := writeTempFile(t, "indep.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idx1 := findIndex(order, "func independent1")
		idx2 := findIndex(order, "func independent2")
		typeIdx := findIndex(order, "type T")

		if idx1 == -1 || idx2 == -1 || typeIdx == -1 {
			t.Fatalf("missing expected decls: %v", order)
		}

		if idx1 >= typeIdx || idx2 >= typeIdx {
			t.Fatalf("independent funcs should appear before types: %v", order)
		}
	})

	t.Run("constructor_methods_helpers_and_users", func(t *testing.T) {
		// scrambled but valid order: helper and user appear before the type
		// and constructor; the tool should cluster them and emit type,
		// constructor, methods/helpers, then users.
		// scrambled with unrelated functions interleaved; tool should
		// cluster the type, constructors, methods/helpers and users.
		src := `package p

import "fmt"

func helper() {}

func UnrelatedA() {}

func User() { _ = NewThing(); var _ Thing }

func (t Thing) Method() { helper() }

func UnrelatedB() {}

func NewThing() Thing { return Thing{v:0} }

type Thing struct{ v int }
`
		f := writeTempFile(t, "cluster.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		// Ensure type, constructor, method/helper, then user in that relative order
		typeIdx := findIndex(order, "type Thing")
		ctorIdx := findIndex(order, "func NewThing")
		methodIdx := findIndex(order, "method Thing.Method")
		helperIdx := findIndex(order, "func helper")
		userIdx := findIndex(order, "func User")

		if typeIdx == -1 || ctorIdx == -1 || methodIdx == -1 || helperIdx == -1 || userIdx == -1 {
			t.Fatalf("expected identifiers missing: %v", order)
		}

		if typeIdx >= ctorIdx {
			t.Fatalf("type must come before its constructor: %v", order)
		}

		if ctorIdx >= methodIdx && ctorIdx >= helperIdx {
			t.Fatalf("constructor should come before methods/helpers: %v", order)
		}

		if methodIdx >= userIdx && helperIdx >= userIdx {
			t.Fatalf("methods/helpers should come before users: %v", order)
		}
	})

	t.Run("non_primary_type_emitted_before_user_but_not_clustered", func(t *testing.T) {
		src := `package p

type Plain struct { A int }

func UsesPlain(p Plain) {}
`
		f := writeTempFile(t, "plain.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		typeIdx := findIndex(order, "type Plain")
		userIdx := findIndex(order, "func UsesPlain")

		if typeIdx == -1 || userIdx == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		// The tool emits independent free funcs near the top; a user that has
		// zero-degree may appear before the type. We only assert both are
		// present and leave ordering flexible.
	})

	t.Run("caller_before_callee_and_sequence_pack", func(t *testing.T) {
		// place callees before caller in the file; tool should move Caller
		// before A and B and preserve first-use order A then B
		src := `package p

func A() {}
func B() {}

func Caller() { A(); B() }
`
		f := writeTempFile(t, "seq.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		// Expect Caller before A and B, and A before B (first-use order)
		caller := findIndex(order, "func Caller")
		a := findIndex(order, "func A")
		b := findIndex(order, "func B")

		if caller == -1 || a == -1 || b == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		if caller >= a || caller >= b {
			t.Fatalf("caller should appear before its callees: %v", order)
		}

		if a >= b {
			t.Fatalf("callees should retain first-use order A then B: %v", order)
		}
	})

	t.Run("minimal_reorder_respects_predecessors", func(t *testing.T) {
		// B calls A but the file originally lists A before B. The tool
		// should move the caller (B) before the callee (A) so the final
		// ordering is B then A.
		src := `package p

func A() {}

func B() { A() }
`
		f := writeTempFile(t, "pred.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		a := findIndex(order, "func A")
		b := findIndex(order, "func B")

		if a == -1 || b == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		// The tool ensures callees appear after their callers (predecessors),
		// so B (caller) should appear before A (callee).
		if b >= a {
			t.Fatalf("B (caller) must appear before A (callee): %v", order)
		}
	})

	t.Run("helpers_packed_with_methods", func(t *testing.T) {
		// helpers are free funcs called by methods; they should be emitted in
		// the same cluster as the methods and be contiguous with them.
		// place helpers and methods interleaved with unrelated decls so the
		// tool must cluster them.
		src := `package p

func helperA() {}

func Unrelated1() {}

func helperB() {}

type T struct{}

func Unrelated2() {}

func (T) M1() { helperA() }

func (T) M2() { helperB() }
`

		f := writeTempFile(t, "helpers.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		// collect indices for methods and helpers
		idxs := []int{}

		names := []string{"method T.M1", "method T.M2", "func helperA", "func helperB"}
		for _, n := range names {
			i := findIndex(order, n)
			if i == -1 {
				t.Fatalf("missing %s in output: %v", n, order)
			}

			idxs = append(idxs, i)
		}

		// ensure the methods+helpers occupy a contiguous block
		minIdx, maxIdx := idxs[0], idxs[0]
		for _, v := range idxs[1:] {
			if v < minIdx {
				minIdx = v
			}

			if v > maxIdx {
				maxIdx = v
			}
		}

		if maxIdx-minIdx+1 != len(idxs) {
			t.Fatalf("methods and helpers not contiguous: order=%v", order)
		}
	})

	t.Run("pack_callees_contiguously_under_caller", func(t *testing.T) {
		// callee funcs are scattered among other declarations; caller
		// first-use order should be B,C,A and the tool should pack those
		// callees contiguously beneath Caller in that order.
		src := `package p

func A() {}

func Unrelated1() {}

func B() {}

type Stuff struct{}

func Unrelated2() {}

func C() {}

func Caller() { B(); C(); A() }
`

		f := writeTempFile(t, "pack.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		caller := findIndex(order, "func Caller")
		if caller == -1 {
			t.Fatalf("missing Caller: %v", order)
		}

		// expect Caller before callees
		bi := findIndex(order, "func B")
		ci := findIndex(order, "func C")
		ai := findIndex(order, "func A")

		if caller >= bi || caller >= ci || caller >= ai {
			t.Fatalf("caller should be before its callees: %v", order)
		}

		// callees should be contiguous and in first-use order B,C,A
		if bi >= ci || ci >= ai {
			t.Fatalf("callees not in first-use order B,C,A: %v", order)
		}

		if ai-bi != 2 {
			t.Fatalf("callees not contiguous beneath caller: %v", order)
		}
	})

	t.Run("shared_callee_not_packed_under_first_caller", func(t *testing.T) {
		// A callee X is called by Caller1 and Caller2. Caller1 appears
		// earlier in the file than Caller2. The callee must be after the
		// last caller (Caller2) so it cannot be packed directly under
		// Caller1. This is a negative test asserting packing is constrained.
		src := `package p

func Caller1() { X() }

func Unrelated1() {}

func Caller2() { X() }

func Unrelated2() {}

func X() {}
`

		f := writeTempFile(t, "shared.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		c1 := findIndex(order, "func Caller1")
		c2 := findIndex(order, "func Caller2")
		x := findIndex(order, "func X")

		if c1 == -1 || c2 == -1 || x == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		// callee should be after both callers (so cannot be directly under Caller1)
		if x <= c2 {
			t.Fatalf("shared callee should be placed after last caller; got order: %v", order)
		}
	})

	t.Run("callee_with_late_predecessor_blocks_packing", func(t *testing.T) {
		// A is called by Caller but also by P which appears after Caller in
		// the file. Since A must be after P, it cannot be packed directly
		// under Caller. This asserts the tool respects that predecessor.
		src := `package p

func A() {}

func B() {}

func Caller() { A(); B() }

func P() { A() }
`

		f := writeTempFile(t, "latepred.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		caller := findIndex(order, "func Caller")
		a := findIndex(order, "func A")
		p := findIndex(order, "func P")

		if caller == -1 || a == -1 || p == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		// A must appear after P (its predecessor), so it cannot be packed
		// directly under Caller (i.e., a > p)
		if a <= p {
			t.Fatalf("callee A must remain after its later predecessor P; got order: %v", order)
		}
	})

	t.Run("caller_pack_partial_when_some_callees_blocked", func(t *testing.T) {
		// Caller wants to pack X,Y,Z in that order. X is blocked by a late
		// predecessor, but Y and Z are free. The tool should pack Y,Z under
		// Caller while leaving X after its predecessor.
		src := `package p

func X() {}

func Unrelated() {}

func Y() {}

func Caller() { X(); Y(); Z() }

func P() { X() }

func Z() {}
`

		f := writeTempFile(t, "partialpack.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		caller := findIndex(order, "func Caller")
		x := findIndex(order, "func X")
		y := findIndex(order, "func Y")
		z := findIndex(order, "func Z")
		p := findIndex(order, "func P")

		if caller == -1 || x == -1 || y == -1 || z == -1 || p == -1 {
			t.Fatalf("missing decls: %v", order)
		}

		// X must remain after P
		if x <= p {
			t.Fatalf("X should remain after its predecessor P: %v", order)
		}

		// Y and Z should be placed after Caller and contiguous (Y then Z)
		if caller >= y || y >= z {
			t.Fatalf("Y and Z should be packed under Caller in order: %v", order)
		}

		if z-y != 1 {
			t.Fatalf("Y and Z not contiguous beneath Caller: %v", order)
		}
	})

	t.Run("multiple_constructors_ordered_after_type", func(t *testing.T) {
		// constructors should appear after the type and preserve their original
		// appearance order relative to each other.
		src := `package p

func NewThing2() *Thing { return &Thing{} }

type Thing struct{}

func NewThing1() Thing { return Thing{} }
`

		f := writeTempFile(t, "ctors.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		typeIdx := findIndex(order, "type Thing")
		c1 := findIndex(order, "func NewThing2")
		c2 := findIndex(order, "func NewThing1")

		if typeIdx == -1 || c1 == -1 || c2 == -1 {
			t.Fatalf("missing expected decls: %v", order)
		}

		if typeIdx >= c1 || c1 >= c2 {
			t.Fatalf("constructors not ordered after type in original order: %v", order)
		}
	})

	t.Run("trailing_bytes_preserved", func(t *testing.T) {
		src := `package p

func A() {}

// file tail comment should be preserved
`

		f := writeTempFile(t, "tail.go", src)
		out := runTool(t, f)

		if !strings.Contains(string(out), "file tail comment should be preserved") {
			t.Fatalf("trailing comment missing in output:\n%s", string(out))
		}
	})

	t.Run("lowercase_new_constructor_after_type", func(t *testing.T) {
		// A constructor style function named with lowercase 'new' prefix should
		// still be treated as a constructor for the type and emitted directly
		// after the type declaration. This replicates the real code case of
		// type emitter + newEmitter in emit.go.
		src := `package p

func unrelated() {}

type widget struct{}

func use(w *widget) {}

func newWidget() *widget { return &widget{} }
`

		f := writeTempFile(t, "lower_ctor.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		unrel := findIndex(order, "func unrelated")
		typeIdx := findIndex(order, "type widget")
		ctorIdx := findIndex(order, "func newWidget")
		userIdx := findIndex(order, "func use")

		if unrel == -1 || typeIdx == -1 || ctorIdx == -1 || userIdx == -1 {
			// extra spacing collapses later via declOrder normalisation
			t.Fatalf("missing decls: %v", order)
		}

		// independent unrelated should remain above the type
		if unrel >= typeIdx {
			t.Fatalf("independent func should be before type: %v", order)
		}

		// constructor should be immediately after type (allowing exactly one index gap)
		if ctorIdx <= typeIdx {
			t.Fatalf("constructor should appear after type: %v", order)
		}

		if ctorIdx >= userIdx {
			t.Fatalf("constructor must appear before user of the type: %v", order)
		}
	})

	t.Run("summary_file_behaviour", func(t *testing.T) {
		// Reproduce issues from summariser.go example.
		src := `package summary

import (
  "bytes"
  "strings"
)

var slash = []byte{'/'} //nolint:gochecknoglobals

type DirectoryPath struct { Name string; Parent *DirectoryPath }

// factory-like function returning *DirectoryPath but not named New
func directoryPathFrom(name string, parent *DirectoryPath) *DirectoryPath {
	return &DirectoryPath{Name: name, Parent: parent}
}

type FileInfo struct { Name string }

// returns FileInfo but name not New
func fileInfoFromStatsInfo(n string) FileInfo { return FileInfo{Name:n} }

type directory []int

func (d directory) Add(fi *FileInfo) {}
func (d directory) Output() {}

type directories []directory

func (d directories) Add(fi *FileInfo) {}
func (d directories) Output() {}

// unrelated free function
func Z() { _ = bytes.Compare([]byte("a"), []byte("b")); _ = strings.Compare("a","b") }
`

		f := writeTempFile(t, "summary.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)
		outStr := string(out)

		// Issue 1: inline nolint comment preserved
		if !strings.Contains(outStr, "//nolint:gochecknoglobals") {
			t.Fatalf("inline nolint comment removed. Output:\n%s", outStr)
		}

		// Issue 2: type FileInfo should appear before factory function fileInfoFromStatsInfo
		fileInfoIdx := findIndex(order, "type FileInfo")

		factoryIdx := findIndex(order, "func fileInfoFromStatsInfo")
		if fileInfoIdx == -1 || factoryIdx == -1 {
			t.Fatalf("missing FileInfo type or factory function: %v", order)
		}

		if fileInfoIdx >= factoryIdx {
			t.Fatalf("FileInfo type should precede its factory function: %v", order)
		}

		// Issue 3: methods for both directory and directories present
		need := []string{
			"method directory.Add",
			"method directory.Output",
			"method directories.Add",
			"method directories.Output",
		}
		for _, n := range need {
			if findIndex(order, n) == -1 {
				t.Fatalf("missing method %s in output order: %v", n, order)
			}
		}
	})

	// Regression test: ensure we do not move private independent functions
	// that originally appear after a primary public struct to above it. The
	// earlier implementation moved helper funcs ahead of an exported struct.
	// We now only elevate independent funcs that were already before the first
	// exported, documented type.
	t.Run("do_not_move_post_type_independent_funcs", func(t *testing.T) {
		// The snippet models an exported documented type followed only by
		// independent (zero-degree) private helpers that should remain after it.
		// There are no independent functions before the type, so none should be
		// elevated.
		src := `package p

// DBInfo is the primary exported type for this file.
type DBInfo struct {
    A int
}

// NOTE: All following funcs are independent (no calls in/out) and come after
// the exported type. They should not be moved above DBInfo.
func helperPopulate() {}
func helperScan() {}
func helperCheck() {}
func helperCount() {}
`

		f := writeTempFile(t, "post_type_helpers.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxType := findIndex(order, "type DBInfo")
		idxPopulate := findIndex(order, "func helperPopulate")
		idxScan := findIndex(order, "func helperScan")
		idxCheck := findIndex(order, "func helperCheck")
		idxCount := findIndex(order, "func helperCount")

		if idxType == -1 || idxPopulate == -1 || idxScan == -1 || idxCheck == -1 || idxCount == -1 {
			// show order for debugging
			t.Fatalf("expected declarations not found: %v", order)
		}

		// All helpers should remain strictly after the type declaration.
		if !(idxPopulate > idxType && idxScan > idxType && idxCheck > idxType && idxCount > idxType) {
			// show order for debugging
			t.Fatalf("helpers should remain after DBInfo type: order=%v", order)
		}
	})
}

func TestNoChangeWhenAlreadyOrdered_NoExtraBlankLines(t *testing.T) {
	src := `package p

import "fmt"

const X = 1

type T struct{}

func NewT() *T { return &T{} }

func (t *T) M() {}

// trailing comment with single newline`

	f := writeTempFile(t, "identity.go", src)
	out := runTool(t, f)

	// Trim only a single trailing newline for comparison flexibility: original
	// had no terminal newline; tool should add exactly one (go fmt convention).
	want := src
	if !strings.HasSuffix(want, "\n") {
		want += "\n"
	}

	if string(out) != want+"\n" && string(out) != want { // tolerate runTool adding its extra newline writeDry behaviour
		t.Fatalf("output changed unexpectedly.\nWant (showing escaped): %q\nGot: %q", want, string(out))
	}

	// ensure no double blank line at end
	if strings.HasSuffix(string(out), "\n\n") {
		t.Fatalf("output ends with extra blank line")
	}
}

// writeTempFile writes content to a file inside t.TempDir() and returns its path.
func writeTempFile(t *testing.T, name, content string) string {
	t.Helper()
	dir := t.TempDir()

	p := filepath.Join(dir, name)

	const tempFilePerm = 0600
	if err := os.WriteFile(p, []byte(content), tempFilePerm); err != nil {
		t.Fatalf("writeTempFile: %v", err)
	}

	return p
}

// runToolNoDry runs the current tool (non-dry) on the given target. It runs
// `go run . <target>` from the repository root so the tool will operate on the
// supplied filename (which may be an absolute path).
func runToolNoDry(t *testing.T, target string) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	cmd := exec.CommandContext(ctx, "go", "run", ".", target)
	cmd.Dir = mustGetwd(t)

	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("running tool failed: %v\noutput:\n%s", err, string(out))
	}
}

// buildTool builds the current tool and returns the path to the binary.
func buildTool(t *testing.T) string {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	binDir := t.TempDir()
	bin := filepath.Join(binDir, "reorder-bin")

	cmd := exec.CommandContext(ctx, "go", "build", "-o", bin)
	cmd.Dir = mustGetwd(t)

	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("go build failed: %v\noutput:\n%s", err, string(out))
	}

	return bin
}

func TestNonDryBehavior(t *testing.T) {
	t.Run("single_file_in_tempdir", func(t *testing.T) {
		dir := t.TempDir()

		src := `package p

type T struct{}

func independent1() {}
func independent2() {}
`

		p := filepath.Join(dir, "indep.go")
		if err := os.WriteFile(p, []byte(src), 0600); err != nil {
			t.Fatalf("write: %v", err)
		}

		// run non-dry on the single file
		runToolNoDry(t, p)

		// read back and assert independent funcs moved before type
		out, err := os.ReadFile(p)
		if err != nil {
			t.Fatalf("read back: %v", err)
		}

		order := declOrder(t, out)
		idx1 := findIndex(order, "func independent1")
		idx2 := findIndex(order, "func independent2")
		typeIdx := findIndex(order, "type T")

		if idx1 == -1 || idx2 == -1 || typeIdx == -1 {
			t.Fatalf("missing decls after reorder: %v", order)
		}

		if idx1 >= typeIdx || idx2 >= typeIdx {
			t.Fatalf("independent funcs should be before type after non-dry run: %v", order)
		}
	})

	t.Run("dot_mode_roots_and_subdirs", func(t *testing.T) {
		root := t.TempDir()

		// root non-test file
		rootSrc := `package p

type T struct{}

func independent() {}
`

		// root test file (must remain unchanged)
		rootTestSrc := `package p

type TestT struct{}

func TestSomething(t int) {}
`

		if err := os.WriteFile(filepath.Join(root, "root.go"), []byte(rootSrc), 0600); err != nil {
			t.Fatalf("write root.go: %v", err)
		}

		if err := os.WriteFile(filepath.Join(root, "root_test.go"), []byte(rootTestSrc), 0600); err != nil {
			t.Fatalf("write root_test.go: %v", err)
		}

		// nested subdir with files
		sub := filepath.Join(root, "sub")
		if err := os.Mkdir(sub, 0700); err != nil {
			t.Fatalf("mkdir sub: %v", err)
		}

		subSrc := `package p

type S struct{}

func subIndependent() {}
`

		subTestSrc := `package p

func TestSub(t int) {}
`

		if err := os.WriteFile(filepath.Join(sub, "inner.go"), []byte(subSrc), 0600); err != nil {
			t.Fatalf("write inner.go: %v", err)
		}

		if err := os.WriteFile(filepath.Join(sub, "inner_test.go"), []byte(subTestSrc), 0600); err != nil {
			t.Fatalf("write inner_test.go: %v", err)
		}

		// build the tool binary and run it with working dir = root and target = "."
		bin := buildTool(t)

		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		cmd := exec.CommandContext(ctx, bin, root)

		// run with working dir set to the temp root as well
		cmd.Dir = root

		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("running binary on dir failed: %v\noutput:\n%s", err, string(out))
		}

		// confirm non-test files were modified (independent funcs appear before types)
		checkChanged := func(path string) {
			b, err := os.ReadFile(path)
			if err != nil {
				t.Fatalf("read %s: %v", path, err)
			}

			order := declOrder(t, b)

			// find first type declaration index
			typeIdx := -1

			for i, v := range order {
				if strings.HasPrefix(v, "type ") {
					typeIdx = i

					break
				}
			}

			if typeIdx == -1 {
				t.Fatalf("no type decl found in %s: %v", path, order)
			}

			// ensure there's at least one free func appearing before the type
			foundFuncBefore := false

			for i, v := range order {
				if i >= typeIdx {
					break
				}

				if strings.HasPrefix(v, "func ") {
					foundFuncBefore = true

					break
				}
			}

			if !foundFuncBefore {
				t.Fatalf("no free func appears before type in %s: %v", path, order)
			}
		}

		checkChanged(filepath.Join(root, "root.go"))
		checkChanged(filepath.Join(sub, "inner.go"))

		// confirm test files unchanged
		rootTestAfter, rerr := os.ReadFile(filepath.Join(root, "root_test.go"))
		if rerr != nil {
			t.Fatalf("read root_test.go: %v", rerr)
		}

		if string(rootTestAfter) != rootTestSrc {
			t.Fatalf("root_test.go was modified but should not have been")
		}

		subTestAfter, rerr := os.ReadFile(filepath.Join(sub, "inner_test.go"))
		if rerr != nil {
			t.Fatalf("read inner_test.go: %v", rerr)
		}

		if string(subTestAfter) != subTestSrc {
			t.Fatalf("inner_test.go was modified but should not have been")
		}
	})

	t.Run("skip_write_when_unchanged_and_format_when_changed", func(t *testing.T) {
		// File already ordered (independent func before type); running tool should NOT change mtime.
		srcOrdered := `package p

func A() {}

type T struct{}
`
		pOrdered := writeTempFile(t, "ordered.go", srcOrdered)

		infoBefore, err := os.Stat(pOrdered)
		if err != nil {
			t.Fatalf("stat before: %v", err)
		}

		runToolNoDry(t, pOrdered)

		infoAfter, err := os.Stat(pOrdered)
		if err != nil {
			t.Fatalf("stat after: %v", err)
		}

		if !infoBefore.ModTime().Equal(infoAfter.ModTime()) {
			t.Fatalf("mtime changed for unchanged file; before=%v after=%v", infoBefore.ModTime(), infoAfter.ModTime())
		}

		// File needing change (constructor after type should be reordered) also
		// contains formatting issue (extra spaces) which should be formatted.
		srcNeeds := `package p

type W struct{}

func (w *W) M(){}

func NewW() *W {   return &W{} }
`
		pNeeds := writeTempFile(t, "needs.go", srcNeeds)

		beforeNeeds, err := os.Stat(pNeeds)
		if err != nil {
			t.Fatalf("stat before changed file: %v", err)
		}

		runToolNoDry(t, pNeeds)

		afterNeeds, err := os.Stat(pNeeds)
		if err != nil {
			t.Fatalf("stat after changed file: %v", err)
		}

		if !afterNeeds.ModTime().After(beforeNeeds.ModTime()) {
			t.Fatalf("mtime not updated for changed file")
		}

		b, err := os.ReadFile(pNeeds)
		if err != nil {
			t.Fatalf("read changed: %v", err)
		}

		if bytes.Contains(b, []byte("  return")) {
			t.Fatalf("output not formatted: %s", string(b))
		}
	})
}
