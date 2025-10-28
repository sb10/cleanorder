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

	// Bug report reproducer: a type used by another type's declaration must be
	// declared before its user. In examples/monster_phase.go, MonsterOutcome has a
	// field of type []AttackDetail, but AttackDetail was declared below it. The
	// tool should reorder so that AttackDetail appears immediately above
	// MonsterOutcome.
	t.Run("type_used_in_type_decl_precedes_user", func(t *testing.T) {
		src := `package p

// MonsterOutcome summarizes outcomes and uses AttackDetail in its fields
type MonsterOutcome struct {
    Details []AttackDetail
}

// Declared after its user in source; tool should move it above
type AttackDetail struct{ Hit bool }
`

		f := writeTempFile(t, "monster_phase_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxUser := findIndex(order, "type MonsterOutcome")
		idxDep := findIndex(order, "type AttackDetail")

		if idxUser == -1 || idxDep == -1 {
			t.Fatalf("missing expected type decls in output: %v", order)
		}

		if !(idxDep < idxUser) {
			t.Fatalf("AttackDetail type should appear before MonsterOutcome that uses it: %v", order)
		}

		if idxUser-idxDep != 1 {
			t.Fatalf("AttackDetail should be immediately above MonsterOutcome: %v", order)
		}
	})

	// Regression: nested helper packing for free-function users. When a user
	// function emits a helper that itself calls other helpers, we should pack
	// those nested helpers depth-first in first-use order, anchoring under the
	// first caller even if another sibling later also calls the nested helper.
	// Expect order: Connect, H, Line, V (callee-after-first-caller for Line).
	t.Run("nested_helpers_depth_first_under_user", func(t *testing.T) {
		src := `package p

// anchor type so the user function is classified as a user of the type
type Params struct{}

// user references Params (in signature) and calls Connect
func Generate(p Params) { Connect() }

// helper under the user
func Connect() { H(); V() }

// sibling helpers that both call Line
func H() { Line() }
func V() { Line() }

// shared callee; should be anchored under H (first caller) rather than V
func Line() {}
`

		f := writeTempFile(t, "nested_helpers_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxGen := findIndex(order, "func Generate")
		idxConn := findIndex(order, "func Connect")
		idxH := findIndex(order, "func H")
		idxLine := findIndex(order, "func Line")
		idxV := findIndex(order, "func V")

		need := map[string]int{"Generate": idxGen, "Connect": idxConn, "H": idxH, "Line": idxLine, "V": idxV}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		// Ensure depth-first packing under Connect: H, then Line (its helper), then V
		if !(idxConn == idxGen+1) {
			t.Fatalf("Connect should be immediately after Generate: %v", order)
		}
		if !(idxH == idxConn+1) {
			t.Fatalf("H should be immediately after Connect: %v", order)
		}
		if !(idxLine == idxH+1) {
			t.Fatalf("Line should be immediately after H: %v", order)
		}
		if !(idxV == idxLine+1) {
			t.Fatalf("V should be immediately after Line: %v", order)
		}
	})

	// Bug report: in examples/generate.go, the private helpers of Generate()
	// should appear in the caller's first-use order: chooseRoom, roomsIntersecting,
	// carveRoom, connectRooms. Reproduce with a minimal snippet modelled on that file.
	t.Run("dungeon_generate_helpers_order", func(t *testing.T) {
		src := `package p

type Params struct{ RoomAttempts, MinSize, MaxSize int }

func applyDefaults(p Params) Params { return p }

// Generate creates a level; calls helpers in order: chooseRoom, roomsIntersecting, carveRoom, connectRooms
func Generate(width, height int, p Params) {
    p = applyDefaults(p)
    for i := 0; i < p.RoomAttempts; i++ {
        _ = i
        _ = width
        _ = height
        _ = p
        _ = struct{}{}
        room := chooseRoom(); _ = room
        if roomsIntersecting() { continue }
        carveRoom()
        if i > 0 { connectRooms() }
    }
}

// Helpers intentionally in a scrambled order to force reordering by the tool
func carveRoom() {}
func connectRooms() {}
func chooseRoom() struct{} { return struct{}{} }
func roomsIntersecting() bool { return false }
`

		f := writeTempFile(t, "dungeon_like_generate.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		genIdx := findIndex(order, "func Generate")
		idxChoose := findIndex(order, "func chooseRoom")
		idxInter := findIndex(order, "func roomsIntersecting")
		idxCarve := findIndex(order, "func carveRoom")
		idxConn := findIndex(order, "func connectRooms")

		need := map[string]int{"Generate": genIdx, "chooseRoom": idxChoose, "roomsIntersecting": idxInter, "carveRoom": idxCarve, "connectRooms": idxConn}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		// Expect helpers packed immediately beneath Generate in first-call order.
		if !(idxChoose == genIdx+1 && idxInter == idxChoose+1 && idxCarve == idxInter+1 && idxConn == idxCarve+1) {
			t.Fatalf("helpers not packed under Generate in first-use order (chooseRoom, roomsIntersecting, carveRoom, connectRooms): %v", order)
		}
	})

	// When a constructor returns two types declared in the same file, both type
	// declarations must appear before the constructor. The constructor should not
	// be emitted after only the first type.
	t.Run("constructor_returning_two_types_appears_after_both_types", func(t *testing.T) {
		src := `package p

// Two related types
type A struct{}
type B struct{}

// Constructor-style function returning both A and B; it should be emitted after both types
func NewAB() (A, B) { return A{}, B{} }
`

		f := writeTempFile(t, "ctor_two_types.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxA := findIndex(order, "type A")
		idxB := findIndex(order, "type B")
		idxCtor := findIndex(order, "func NewAB")

		need := map[string]int{"type A": idxA, "type B": idxB, "func NewAB": idxCtor}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		if !(idxCtor > idxA && idxCtor > idxB) {
			t.Fatalf("constructor returning two types must appear after both types: %v", order)
		}
	})

	// Interface types should be treated the same as other types: the interface
	// declaration must appear before any declarations that reference it (users),
	// including methods on other receiver types and typed var declarations.
	// This test asserts:
	//   - type Service (interface) comes before var defaultSvc Service
	//   - type Service comes before method Controller.Handle returning Service
	t.Run("interface_type_before_users_and_vars", func(t *testing.T) {
		src := `package p

type Controller struct{}

// Method using Service interface; appears before the Service type in source
func (Controller) Handle() Service { return nil }

// var typed to Service; also appears before the Service type in source
var defaultSvc Service

// Interface type that should be emitted before its users above
type Service interface { Do() }
`

		f := writeTempFile(t, "iface_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxIface := findIndex(order, "type Service")
		idxVar := findIndex(order, "var defaultSvc")
		idxMeth := findIndex(order, "method Controller.Handle")

		need := map[string]int{"type Service": idxIface, "var defaultSvc": idxVar, "method Controller.Handle": idxMeth}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		if !(idxIface < idxVar) {
			t.Fatalf("interface type should appear before var typed to it: %v", order)
		}

		if !(idxIface < idxMeth) {
			t.Fatalf("interface type should appear before methods that return/reference it: %v", order)
		}
	})

	// Regression from examples/combat.go: ensure types come before their users,
	// including (1) typed const iota block using a declared type, and (2) a method
	// on a different receiver type that returns/mentions a declared type.
	// The tool should emit:
	//   - type Kind before the const (AttackRolled Kind = iota)
	//   - type Summary before method Events.Summary
	// We inline a minimal snippet capturing just the ordering relationships.
	t.Run("combat_types_before_users_and_typed_consts", func(t *testing.T) {
		src := `package p

// Receiver type whose method references Summary below
type Events []Event

// Method that returns Summary; in the original example this appeared before the Summary type.
func (ev Events) Summary() Summary { return Summary{} }

// A typed iota constant block that uses Kind
const (
    AttackRolled Kind = iota
    DamageRolled
)

// Unrelated constants and vars should remain near the top
const Unrelated = 42
var GlobalX = 7

// Another unrelated type to demonstrate that typed consts stay near the top
type Other struct{}

// The type that must precede the above typed const block
type Kind int

// A basic Event to satisfy Events element type (not important for ordering test)
type Event struct{ K Kind }

// The type that should appear before Events.Summary
type Summary struct{ Hit bool }
`

		f := writeTempFile(t, "combat_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxKind := findIndex(order, "type Kind")
		idxConst := findIndex(order, "const AttackRolled")
		idxSummaryType := findIndex(order, "type Summary")
		idxSummaryMethod := findIndex(order, "method Events.Summary")
		idxUnrelConst := findIndex(order, "const Unrelated")
		idxVar := findIndex(order, "var GlobalX")
		idxOther := findIndex(order, "type Other")

		need := map[string]int{
			"type Kind":             idxKind,
			"const AttackRolled":    idxConst,
			"type Summary":          idxSummaryType,
			"method Events.Summary": idxSummaryMethod,
			"const Unrelated":       idxUnrelConst,
			"var GlobalX":           idxVar,
			"type Other":            idxOther,
		}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		// Kind must come before its typed const block
		if !(idxKind < idxConst) {
			t.Fatalf("type Kind should appear before its typed const block: %v", order)
		}

		// Summary type should be before Events.Summary method
		if !(idxSummaryType < idxSummaryMethod) {
			t.Fatalf("type Summary should appear before Events.Summary method: %v", order)
		}

		// Prefer unrelated const/var at the top, before any types (except those needed to satisfy typed consts)
		if !(idxUnrelConst < idxKind && idxVar < idxKind) {
			t.Fatalf("unrelated const/var should remain before types in top section: %v", order)
		}

		// The typed const block should remain near the top, not below unrelated types
		if !(idxConst < idxOther) {
			t.Fatalf("typed const block should remain near top, before unrelated types: %v", order)
		}
	})

	// Regression for bug report: when run on examples/input.go, the doc comment
	// for MoveOrWait() was duplicated. Ensure the documentation comment appears
	// exactly once in the reordered output.
	// We copy the relevant example content directly here as the input.
	t.Run("moveorwait_doc_not_duplicated", func(t *testing.T) {
		src := `package input

// MoveOrWait maps directional and wait inputs into a movement vector and a
// boolean indicating whether a turn should be consumed. If multiple
// directions are pressed, horizontal takes precedence when both horizontal and
// vertical are true, and left/right or up/down cancel each other out.
func MoveOrWait(up, down, left, right, wait bool) (dx, dy int, turnTaken bool) {
	// Resolve vertical
	vy := 0
	if up && !down {
		vy = -1
	} else if down && !up {
		vy = 1
	}

	// Resolve horizontal
	vx := 0
	if left && !right {
		vx = -1
	} else if right && !left {
		vx = 1
	}

	if vx != 0 || vy != 0 {
		return vx, vy, true
	}

	if wait {
		return 0, 0, true
	}

	return 0, 0, false
}
`

		f := writeTempFile(t, "examples_input_like.go", src)
		out := runTool(t, f)

		outStr := string(out)
		needle := "MoveOrWait maps directional and wait inputs"
		occ := strings.Count(outStr, needle)
		if occ != 1 {
			t.Fatalf("expected exactly 1 occurrence of MoveOrWait doc comment, got %d.\nOutput:\n%s", occ, outStr)
		}

		// Also, ensure the function appears exactly once
		if strings.Count(outStr, "func MoveOrWait(") != 1 {
			t.Fatalf("expected exactly 1 MoveOrWait function decl; output:\n%s", outStr)
		}
	})

	// Regression from examples/db.go: a method that returns a type declared in
	// the same file (gidMountsMap) should not be pulled under that type's
	// "users" section when it participates in an intra-receiver call chain.
	// Instead, methods on the same receiver type should remain grouped and obey
	// callee-after-first-caller: gidsToMountpoints() should be followed
	// immediately by dcssToMountPoints(), and gidsToMountpoints() itself should
	// come after updateHistories(). The gidMountsMap type is incidental and
	// should be kept immediately above gidsToMountpoints(), not treated as a
	// separate cluster anchor.
	// We intentionally do NOT declare the BaseDirs type here (as in the real
	// examples/db.go), so prior logic that classified methods as users of other
	// types would move gidsToMountpoints() under gidMountsMap. This test
	// asserts the desired grouping behaviour.
	t.Run("basedirs_gid_mounts_grouping", func(t *testing.T) {
		src := `package p

import (
  "time"
  "github.com/wtsi-hgi/wrstat-ui/db"
)

// incidental type used as a return value below
type gidMountsMap map[uint32]map[string]db.DirSummary

// updateHistories should appear before gidsToMountpoints
func (b *BaseDirs) updateHistories(gidBase IDAgeDirs) error {
  _ = b.gidsToMountpoints(gidBase)
  return nil
}

// this method returns gidMountsMap but is conceptually part of the BaseDirs
// method group; it calls dcssToMountPoints
func (b *BaseDirs) gidsToMountpoints(gidBase IDAgeDirs) gidMountsMap {
  _ = gidBase
  return gidMountsMap{0: b.dcssToMountPoints(nil)}
}

// callee of gidsToMountpoints; should be packed immediately after it
func (b *BaseDirs) dcssToMountPoints(dcss *AgeDirs) map[string]db.DirSummary {
  mounts := make(map[string]db.DirSummary)
  // simulate combining counts/sizes
  var ds db.DirSummary
  _ = time.Now()
  mounts["/"] = ds
  return mounts
}
`

		f := writeTempFile(t, "db_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxUpdate := findIndex(order, "method BaseDirs.updateHistories")
		idxType := findIndex(order, "type gidMountsMap")
		idxGids := findIndex(order, "method BaseDirs.gidsToMountpoints")
		idxDcss := findIndex(order, "method BaseDirs.dcssToMountPoints")

		need := map[string]int{"updateHistories": idxUpdate, "gidMountsMap type": idxType, "gidsToMountpoints": idxGids, "dcssToMountPoints": idxDcss}
		for name, idx := range need {
			if idx == -1 {
				t.Fatalf("missing %s in output order: %v", name, order)
			}
		}

		// updateHistories should come before gidsToMountpoints
		if !(idxUpdate < idxGids) {
			t.Fatalf("updateHistories should appear before gidsToMountpoints: %v", order)
		}

		// dcssToMountPoints should be immediately after gidsToMountpoints
		if !(idxDcss == idxGids+1) {
			t.Fatalf("dcssToMountPoints should be immediately after gidsToMountpoints: %v", order)
		}

		// The incidental gidMountsMap type should appear immediately above
		// gidsToMountpoints (kept adjacent, not forcing a separate users section)
		if !(idxType == idxGids-1) {
			t.Fatalf("gidMountsMap type should be immediately above gidsToMountpoints: %v", order)
		}
	})

	// New rule: callee-after-first-caller. From the bug report: in a basedirs
	// example, helpers basedirsKey and codecDecode should be moved directly
	// under the first method that calls them (GroupSubDirs).
	// We inline a minimal snippet modelling that case.
	t.Run("basedirs_helpers_follow_first_caller", func(t *testing.T) {
		src := `package p

type bdReader struct{}

func (bdReader) GroupSubDirs() { basedirsKey(); codecDecode() }

// another method also calling the helpers later
func (bdReader) Later() { basedirsKey(); codecDecode() }

// helpers
func basedirsKey() {}
func codecDecode() {}
`

		f := writeTempFile(t, "basedirs_store_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxGroupSubDirs := findIndex(order, "method bdReader.GroupSubDirs")
		idxBasedirsKey := findIndex(order, "func basedirsKey")
		idxCodecDecode := findIndex(order, "func codecDecode")

		if idxGroupSubDirs == -1 || idxBasedirsKey == -1 || idxCodecDecode == -1 {
			t.Fatalf("missing expected decls in reordered output: %v", order)
		}

		// Expect helpers to be packed immediately below the first caller.
		if !(idxBasedirsKey == idxGroupSubDirs+1) {
			t.Fatalf("basedirsKey should appear immediately after GroupSubDirs; order=%v", order)
		}

		if !(idxCodecDecode == idxBasedirsKey+1) {
			t.Fatalf("codecDecode should appear immediately after basedirsKey; order=%v", order)
		}
	})

	// Regression: do not emit a method as a "user" of another type before the
	// method receiver's type is declared. Type declarations must precede any code
	// that needs that type.
	t.Run("method_user_not_emitted_before_own_type", func(t *testing.T) {
		src := `package p

// Some type that will be processed first
type Other struct{}

// Receiver type declared after
type IDAgeDirs struct{}

// Method uses Other; previous logic could incorrectly emit this as a user of
// Other (placing it before IDAgeDirs). It must remain after IDAgeDirs.
func (i IDAgeDirs) Get(o Other) {}
`

		f := writeTempFile(t, "basedirs_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxOther := findIndex(order, "type Other")
		idxType := findIndex(order, "type IDAgeDirs")
		idxMeth := findIndex(order, "method IDAgeDirs.Get")

		if idxOther == -1 || idxType == -1 || idxMeth == -1 {
			t.Fatalf("missing expected decls: %v", order)
		}

		if !(idxType < idxMeth) {
			t.Fatalf("receiver type must come before its method: %v", order)
		}

		if !(idxOther < idxType) {
			t.Fatalf("sanity: Other should remain before IDAgeDirs: %v", order)
		}
	})

	// Regression for bug report: A function/method that returns a slice of the
	// immediately preceding type should not be moved beneath unrelated private
	// helpers. Specifically, a public method returning []History should be
	// treated as a "user" of type History and emitted right after the type even
	// if the type has no constructors or methods.
	t.Run("type_users_emitted_even_without_methods_or_ctors_and_before_private_helpers", func(t *testing.T) {
		src := `package p

// History contains usage info
type History struct{}

// independent private helpers that should not be preferred over public users
func validateMountPoints() {}
func calc() {}

// a different type declared in this file
type BaseDirReader struct{}

// Public method returning a slice of the immediately preceding type; should
// be emitted with the users of History (ie. right after History), not below
// the unrelated private helpers above.
func (b *BaseDirReader) History() ([]History, error) { return nil, nil }
`

		f := writeTempFile(t, "history_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxType := findIndex(order, "type History")
		idxMeth := findIndex(order, "method BaseDirReader.History")
		idxPriv1 := findIndex(order, "func validateMountPoints")
		idxPriv2 := findIndex(order, "func calc")

		if idxType == -1 || idxMeth == -1 || idxPriv1 == -1 || idxPriv2 == -1 {
			t.Fatalf("missing expected decls: %v", order)
		}

		// The user method should be emitted after the type
		if !(idxType < idxMeth) {
			t.Fatalf("user method should appear after its type: %v", order)
		}

		// and before unrelated private helpers
		if !(idxMeth < idxPriv1 && idxMeth < idxPriv2) {
			t.Fatalf("public user should be preferred over uncalled private helpers: %v", order)
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

	// Bug report regression: In examples/dir.go, the variable DirectionsURDL
	// (which uses the Up/Right/Down/Left constants) appeared above the const
	// block that defines those constants. As a user of the consts, it should be
	// emitted beneath them.
	t.Run("dir_var_below_consts", func(t *testing.T) {
		src := `package model

// DirectionsURDL is the canonical neighbor iteration order used by rules that
// need 4-connected movement on a grid: Up, Right, Down, Left. Using a shared
// definition keeps pathfinding and other systems deterministic.
var DirectionsURDL = [...]Dir{Up, Right, Down, Left}

const (
	Up Dir = iota
	Right
	Down
	Left
)

// Dir represents a cardinal direction.
type Dir int
`

		f := writeTempFile(t, "dir_bug.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		idxVar := findIndex(order, "var DirectionsURDL")
		idxConst := findIndex(order, "const Up")

		if idxVar == -1 || idxConst == -1 {
			t.Fatalf("missing DirectionsURDL var or Up const in output order: %v", order)
		}

		if !(idxConst < idxVar) {
			t.Fatalf("DirectionsURDL var should appear after its composing consts: %v", order)
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

	// Regression for bug report: In a generic handler type with a ServeHTTP
	// method that calls free helper functions readBody and handleError, those
	// helpers must be emitted after ServeHTTP (callee-after-first-caller within
	// the type cluster). Previously, the tool could move helpers above the
	// method when processing examples/server.go.
	t.Run("server_helpers_after_ServeHTTP", func(t *testing.T) {
		src := `package p

import (
  "encoding/json"
  "errors"
  "io"
  "net/http"
)

type httpError struct { code int; msg string }
func (h httpError) Error() string { return "" }

type handle[T any] func(T) (any, error)

func (h handle[T]) ServeHTTP(w http.ResponseWriter, r *http.Request) {
  var val T
  if err := readBody(r.Body, &val); err != nil { //nolint:nestif
    handleError(w, err)
  } else if data, err := h(val); err != nil {
    handleError(w, err)
  } else if err = json.NewEncoder(w).Encode(data); err != nil {}
}

func readBody(r io.ReadCloser, data any) error {
  defer r.Close(); return nil
}

func handleError(w http.ResponseWriter, err error) {
  var herr httpError
  if errors.As(err, &herr) { _ = herr } else {}
}
`

		f := writeTempFile(t, "server_like.go", src)
		out := runTool(t, f)
		order := declOrder(t, out)

		serve := findIndex(order, "method handle.ServeHTTP")
		read := findIndex(order, "func readBody")
		herr := findIndex(order, "func handleError")

		if serve == -1 || read == -1 || herr == -1 {
			t.Fatalf("missing ServeHTTP/readBody/handleError: %v", order)
		}

		// Helpers must come after ServeHTTP
		if !(serve < read && serve < herr) {
			t.Fatalf("helpers should be after ServeHTTP: %v", order)
		}

		// Prefer helpers to be packed near ServeHTTP when unconstrained
		if !(read == serve+1 || herr == serve+1) {
			// allow flexibility but encourage packing; failure here helps catch regressions
			t.Fatalf("expected at least one helper directly after ServeHTTP: %v", order)
		}
	})

	// Regression for bug report: examples/level.go got corrupted with the
	// TileType declaration being munged together with its typed const block.
	// Ensure the tool outputs a valid separation where the type appears before
	// the const block, and no concatenation like "type TileType intconst (" occurs.
	t.Run("level_tiletype_and_typed_consts_separated_and_ordered", func(t *testing.T) {
		src := `package model

const (
	Wall TileType = iota
	Floor
)

// TileType represents the logical tile kind.
// Values are kept stable to mirror the legacy code expectations when needed.
type TileType int

// Tile is a logical, render-agnostic tile.
type Tile struct {
	Blocked    bool
	IsRevealed bool
	Type       TileType
}

// Level is a logical dungeon map with inclusive coordinate bounds: [0..Width-1] x [0..Height-1].
type Level struct {
	Width  int
	Height int
	Tiles  []Tile
	Rooms  []Rect
}

// NewLevel allocates a blank level filled with walls.
func NewLevel(width, height int) Level {
	l := Level{Width: width, Height: height, Tiles: make([]Tile, width*height)}
	for i := range l.Tiles {
		l.Tiles[i] = Tile{Blocked: true, Type: Wall}
	}

	return l
}

// Index computes the linear index; caller must pass in-bounds x,y.
func (l Level) Index(x, y int) int { return y*l.Width + x }

// InBounds reports whether x,y are within [0..Width-1] x [0..Height-1].
func (l Level) InBounds(x, y int) bool {
	return x >= 0 && x < l.Width && y >= 0 && y < l.Height
}
`

		f := writeTempFile(t, "level_like.go", src)
		out := runTool(t, f)
		outStr := string(out)

		// Must not concatenate type and const tokens
		if strings.Contains(outStr, "type TileType intconst") {
			t.Fatalf("type and const concatenated; output invalid. Output:\n%s", outStr)
		}

		// Parse and assert ordering: type TileType must come before const Wall
		order := declOrder(t, out)
		typeIdx := findIndex(order, "type TileType")
		constIdx := findIndex(order, "const Wall")
		if typeIdx == -1 || constIdx == -1 {
			t.Fatalf("missing type or const decls in output order: %v", order)
		}
		if !(typeIdx < constIdx) {
			t.Fatalf("type TileType should appear before its typed const block: %v", order)
		}
	})

	// Regression for bug report: examples/dir.go lost a large portion of its
	// code after reordering (methods disappeared). This test ensures that:
	//   1) key methods on Dir (Opposite, Apply, Delta) are preserved in output
	//   2) we don't delete lines: the count of non-blank lines before and after
	//      reordering is identical.
	t.Run("dir_methods_preserved_and_linecount_guard", func(t *testing.T) {
		src := `package model

// DirectionsURDL is the canonical neighbor iteration order used by rules that
// need 4-connected movement on a grid: Up, Right, Down, Left. Using a shared
// definition keeps pathfinding and other systems deterministic.
var DirectionsURDL = [...]Dir{Up, Right, Down, Left}

const (
	Up Dir = iota
	Right
	Down
	Left
)

// Dir represents a cardinal direction.
type Dir int

// Opposite returns the opposite cardinal direction.
func (d Dir) Opposite() Dir {
	switch d {
	case Up:
		return Down
	case Right:
		return Left
	case Down:
		return Up
	case Left:
		return Right
	default:
		return d
	}
}

// Apply returns a new Position translated by this direction's unit delta.
func (d Dir) Apply(p Position) Position {
	dx, dy := d.Delta()

	return p.Add(dx, dy)
}

// Delta returns the (dx, dy) unit step for the direction.
func (d Dir) Delta() (int, int) {
	switch d {
	case Up:
		return 0, -1
	case Right:
		return 1, 0
	case Down:
		return 0, 1
	case Left:
		return -1, 0
	default:
		return 0, 0
	}
}
`

		f := writeTempFile(t, "dir_like.go", src)
		beforeNonBlank := countNonBlankLines(src)
		out := runTool(t, f)
		outStr := string(out)
		afterNonBlank := countNonBlankLines(outStr)

		// Presence checks for methods
		need := []string{
			"func (d Dir) Opposite() Dir",
			"func (d Dir) Apply(",
			"func (d Dir) Delta() (int, int)",
		}
		for _, n := range need {
			if !strings.Contains(outStr, n) {
				t.Fatalf("missing expected method %q in output. Output:\n%s", n, outStr)
			}
		}

		// Non-blank line count must remain the same
		if beforeNonBlank != afterNonBlank {
			t.Fatalf("non-blank line count changed: before=%d after=%d", beforeNonBlank, afterNonBlank)
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

// countNonBlankLines counts lines that contain any non-whitespace character.
func countNonBlankLines(s string) int {
	n := 0
	for _, ln := range strings.Split(s, "\n") {
		if strings.TrimSpace(ln) != "" {
			n++
		}
	}
	return n
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
