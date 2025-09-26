package main

import "go/ast"

// getRecvType returns the base identifier name of the first receiver type.
func getRecvType(fd *ast.FuncDecl) string {
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

// usesType checks whether a free function references a type by name in its
// signature or body.
func usesType(fd *ast.FuncDecl, typeName string) bool {
	if fieldListContains(fd.Type.Params, typeName) || fieldListContains(fd.Type.Results, typeName) {
		return true
	}

	return bodyContainsIdent(fd.Body, typeName)
}

// helper: check whether a field list contains the given type
func fieldListContains(fl *ast.FieldList, typeName string) bool {
	if fl == nil {
		return false
	}

	for _, f := range fl.List {
		if typeContains(f.Type, typeName) {
			return true
		}
	}

	return false
}

// helper: inspect function body for identifier occurrences
func bodyContainsIdent(body *ast.BlockStmt, typeName string) bool {
	if body == nil {
		return false
	}

	found := false

	ast.Inspect(body, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && id.Name == typeName {
			found = true

			return false
		}

		return true
	})

	return found
}

// typeContains recursively checks whether the ast.Expr contains a given
// identifier name.
//
//nolint:gocyclo // recursive walker with many AST cases; keeping as-is is clearer
func typeContains(t ast.Expr, typeName string) bool {
	if t == nil {
		return false
	}

	switch tt := t.(type) {
	case *ast.Ident:
		return tt.Name == typeName
	case *ast.FuncType:
		return funcTypeContains(tt, typeName)
	case *ast.SelectorExpr:
		return tt.Sel != nil && tt.Sel.Name == typeName
	case *ast.StructType:
		return structTypeContains(tt, typeName)
	case *ast.InterfaceType:
		return interfaceTypeContains(tt, typeName)
	default:
		return compositeTypeContains(t, typeName)
	}
}

func funcTypeContains(ft *ast.FuncType, typeName string) bool {
	return fieldListContains(ft.Params, typeName) || fieldListContains(ft.Results, typeName)
}

func structTypeContains(st *ast.StructType, typeName string) bool {
	if st.Fields == nil {
		return false
	}

	for _, f := range st.Fields.List {
		if typeContains(f.Type, typeName) {
			return true
		}
	}

	return false
}

func interfaceTypeContains(it *ast.InterfaceType, typeName string) bool {
	if it.Methods == nil {
		return false
	}

	for _, f := range it.Methods.List {
		if typeContains(f.Type, typeName) {
			return true
		}
	}

	return false
}

// compositeTypeContains handles a subset of expression types that are
// composites and recurse into their child expressions.
func compositeTypeContains(t ast.Expr, typeName string) bool {
	switch tt := t.(type) {
	case *ast.StarExpr:
		return typeContains(tt.X, typeName)
	case *ast.ArrayType:
		return typeContains(tt.Elt, typeName)
	case *ast.MapType:
		return typeContains(tt.Key, typeName) || typeContains(tt.Value, typeName)
	case *ast.IndexExpr:
		return typeContains(tt.X, typeName) || typeContains(tt.Index, typeName)
	default:
		return false
	}
}
