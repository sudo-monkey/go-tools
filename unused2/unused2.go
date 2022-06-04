package unused2

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"reflect"
	"strings"

	"golang.org/x/exp/typeparams"
	"golang.org/x/tools/go/analysis"
	"honnef.co/go/tools/analysis/facts/directives"
	"honnef.co/go/tools/analysis/facts/generated"
	"honnef.co/go/tools/analysis/lint"
	"honnef.co/go/tools/go/ast/astutil"
	"honnef.co/go/tools/go/types/typeutil"
	"honnef.co/go/tools/unused"
)

// XXX vet all code for proper use of core types

// XXX handle cgo and go:linkname

// XXX handle implementing interfaces

// XXX aliases/function vars are temporary and will vanish once we replace unused with unused2

type Result = unused.Result
type SerializedResult = unused.SerializedResult
type SerializedObject = unused.SerializedObject

var Serialize = unused.Serialize

func debugf(f string, v ...interface{}) {
	// XXX respect -debug.unused-graph flag for destination
	fmt.Fprintf(os.Stdout, f, v...)
}

// XXX all of these are only exported so we can refer to them in unused2, unexport them when we replace unused with
// unused2

//go:generate go run golang.org/x/tools/cmd/stringer@master -type edgeKind
type edgeKind unused.EdgeKind

func (e edgeKind) is(o edgeKind) bool {
	return e&o != 0
}

const (
	edgeAlias edgeKind = 1 << iota
	edgeBlankField
	edgeAnonymousStruct
	edgeCgoExported
	edgeConstGroup
	edgeElementType
	edgeEmbeddedInterface
	edgeExportedConstant
	edgeExportedField
	edgeExportedFunction
	edgeExportedMethod
	edgeExportedType
	edgeExportedVariable
	edgeExtendsExportedFields
	edgeExtendsExportedMethodSet
	edgeFieldAccess
	edgeFunctionArgument
	edgeFunctionResult
	edgeFunctionSignature
	edgeImplements
	edgeInstructionOperand
	edgeInterfaceCall
	edgeInterfaceMethod
	edgeKeyType
	edgeLinkname
	edgeMainFunction
	edgeInitFunction
	edgeNamedType
	edgeNoCopySentinel
	edgeProvidesMethod
	edgeReceiver
	edgeRuntimeFunction
	edgeSignature
	edgeStructConversion
	edgeTestSink
	edgeTupleElement
	edgeType
	edgeTypeName
	edgeUnderlyingType
	edgePointerType
	edgeUnsafeConversion
	edgeUsedConstant
	edgeVarDecl
	edgeIgnored
	edgeSamePointer
	edgeTypeParam
	edgeTypeArg
	edgeUnionTerm
	edgeRead
	edgeBlankName
)

var typString = unused.TypString
var isIrrelevant = unused.IsIrrelevant
var isNoCopyType = unused.IsNoCopyType
var runtimeFuncs = unused.RuntimeFuncs

var Analyzer = &lint.Analyzer{
	Doc: &lint.Documentation{
		Title: "Unused code",
	},
	Analyzer: &analysis.Analyzer{
		Name:       "U21000", // XXX change Name to U1000
		Doc:        "Unused code",
		Run:        run,
		Requires:   []*analysis.Analyzer{generated.Analyzer, directives.Analyzer},
		ResultType: reflect.TypeOf(Result{}),
	},
}

type graph struct {
	Root        *node
	Nodes       map[types.Object]*node
	pass        *analysis.Pass
	nodeCounter uint64
}

func (g *graph) newNode(obj types.Object) *node {
	g.nodeCounter++
	return &node{
		obj: obj,
		id:  g.nodeCounter,
	}
}

func (g *graph) node(obj types.Object) *node {
	if obj == nil {
		return g.Root
	}
	if n, ok := g.Nodes[obj]; ok {
		return n
	}
	n := g.newNode(obj)
	g.Nodes[obj] = n
	return n
}

type edge struct {
	node *node
	kind edgeKind
}

type node struct {
	// OPT(dh): we could trivially turn this from AoS into SoA. Benchmark if that has any benefits.

	obj interface{}
	id  uint64

	// OPT(dh): evaluate using a map instead of a slice to avoid
	// duplicate edges.
	used []edge

	// set during final graph walk if node is reachable
	seen  bool
	quiet bool
}

func (g *graph) see(obj types.Object) {
	// XXX don't track objects in other packages
	// XXX use isIrrelevant

	g.node(obj)
}

func (g *graph) use(used, by types.Object, kind edgeKind) {
	if used.Pkg() != g.pass.Pkg {
		return
	}
	// XXX use isIrrelevant

	nUsed := g.node(used)
	nBy := g.node(by)
	nBy.used = append(nBy.used, edge{node: nUsed, kind: kind})
}

func (g *graph) color(root *node) {
	if root.seen {
		return
	}
	root.seen = true
	for _, e := range root.used {
		g.color(e.node)
	}
}

func (g *graph) entry(pass *analysis.Pass) {
	for _, f := range pass.Files {
		for _, cg := range f.Comments {
			for _, c := range cg.List {
				if strings.HasPrefix(c.Text, "//go:linkname ") {
					// FIXME(dh): we're looking at all comments. The
					// compiler only looks at comments in the
					// left-most column. The intention probably is to
					// only look at top-level comments.

					// (1.8) packages use symbols linked via go:linkname
					fields := strings.Fields(c.Text)
					if len(fields) == 3 {
						obj := pass.Pkg.Scope().Lookup(fields[1])
						if obj == nil {
							continue
						}
						g.use(obj, nil, edgeLinkname)
					}
				}
			}
		}
	}
	for _, f := range pass.Files {
		for _, decl := range f.Decls {
			g.decl(decl, nil)
		}
	}
}

func (g *graph) read(node ast.Node, by types.Object) {
	if node == nil {
		return
	}

	switch node := node.(type) {
	case *ast.Ident:
		// XXX this branch, in the end, handles all uses of objects
		// (7.2) field accesses use fields

		obj := g.pass.TypesInfo.ObjectOf(node)
		g.use(obj, by, edgeRead)

	case *ast.BasicLit:
		// Nothing to do

	case *ast.SliceExpr:
		g.read(node.X, by)
		g.read(node.Low, by)
		g.read(node.High, by)
		g.read(node.Max, by)

	case *ast.UnaryExpr:
		g.read(node.X, by)

	case *ast.ParenExpr:
		g.read(node.X, by)

	case *ast.ArrayType:
		g.read(node.Len, by)
		g.read(node.Elt, by)

	case *ast.SelectorExpr:
		g.read(node.X, by)
		g.read(node.Sel, by)

	case *ast.IndexExpr:
		g.read(node.X, by)
		g.read(node.Index, by)

	case *ast.BinaryExpr:
		g.read(node.X, by)
		g.read(node.Y, by)

	case *ast.CompositeLit:
		g.read(node.Type, by)
		// We get the type of the node itself, not of node.Type, to handle nested composite literals of the kind
		// T{{...}}
		_, isStruct := typeutil.CoreType(g.pass.TypesInfo.TypeOf(node)).(*types.Struct)

		// Reading a struct composite literal T{...} is the same as writing values to the fields of the struct

		for i, elt := range node.Elts {
			if kv, ok := elt.(*ast.KeyValueExpr); ok {
				_ = i
				_ = kv
				if isStruct {
					g.write(kv.Key, by)
					g.read(kv.Value, by)
				} else {
					g.read(kv.Key, by)
					g.read(kv.Value, by)
				}
			} else {
				if isStruct {
					// Untagged struct literal, deduce the field from the index
					// XXX implement
				} else {
					g.read(elt, by)
				}
			}
		}

	case *ast.StarExpr:
		g.read(node.X, by)

	case *ast.MapType:
		g.read(node.Key, by)
		g.read(node.Value, by)

	case *ast.FuncLit:
		g.read(node.Type, by)
		g.block(node.Body, by)

	case *ast.FuncType:
		g.read(node.TypeParams, by)
		g.read(node.Params, by)
		g.read(node.Results, by)

	case *ast.FieldList:
		if node == nil {
			return
		}

		for _, field := range node.List {
			for _, name := range field.Names {
				g.read(name, by)
				g.read(field.Type, g.pass.TypesInfo.ObjectOf(name))
			}
		}

	case *ast.ChanType:
		g.read(node.Value, by)

	case *ast.StructType:
		for _, field := range node.Fields.List {
			for _, name := range field.Names {
				g.read(name, by)
				g.read(field.Type, g.pass.TypesInfo.ObjectOf(name))
			}
		}

	case *ast.TypeAssertExpr:
		g.read(node.X, by)
		g.read(node.Type, by)

	case *ast.InterfaceType:
		// XXX implement

	case *ast.Ellipsis:
		g.read(node.Elt, by)

	case *ast.CallExpr:
		g.read(node.Fun, by)
		for _, arg := range node.Args {
			g.read(arg, by)
		}

		// Handle conversiosn
		conv := node
		if len(conv.Args) != 1 || conv.Ellipsis.IsValid() {
			return
		}

		dst := g.pass.TypesInfo.TypeOf(conv.Fun)
		src := g.pass.TypesInfo.TypeOf(conv.Args[0])

		// TODO should this use DereferenceR instead?
		s1, ok1 := typeutil.CoreType(typeutil.Dereference(dst)).(*types.Struct)
		s2, ok2 := typeutil.CoreType(typeutil.Dereference(src)).(*types.Struct)
		if ok1 && ok2 {
			// Converting between two structs. The fields are
			// relevant for the conversion, but only if the
			// fields are also used outside of the conversion.
			// Mark fields as used by each other.

			assert(s1.NumFields() == s2.NumFields())
			for i := 0; i < s1.NumFields(); i++ {
				// (5.1) when converting between two equivalent structs, the fields in
				// either struct use each other. the fields are relevant for the
				// conversion, but only if the fields are also accessed outside the
				// conversion.
				g.use(s1.Field(i), s2.Field(i), edgeStructConversion)
				g.use(s2.Field(i), s1.Field(i), edgeStructConversion)
			}
		}

		// XXX check if dst or src are unsafe.Pointer and mark all fields as used

	default:
		lint.ExhaustiveTypeSwitch(node)
	}
}

func (g *graph) write(node ast.Node, by types.Object) {
	if node == nil {
		return
	}

	switch node := node.(type) {
	case *ast.Ident:
		obj := g.pass.TypesInfo.ObjectOf(node)
		if obj == nil {
			// This can happen for `switch x := v.(type)`, where that x doesn't have an object
			return
		}
		g.see(obj)

		// (4.9) functions use package-level variables they assign to iff in tests (sinks for benchmarks)
		// (9.7) variable _reads_ use variables, writes do not, except in tests
		path := g.pass.Fset.File(obj.Pos()).Name()
		if strings.HasSuffix(path, "_test.go") {
			if isGlobal(obj) {
				g.use(obj, by, edgeTestSink)
			}
		}

	case *ast.IndexExpr:
		g.read(node.X, by)

	case *ast.SelectorExpr:
		g.read(node.X, by)
		g.write(node.Sel, by)

	case *ast.StarExpr:
		g.read(node.X, by)

	default:
		lint.ExhaustiveTypeSwitch(node)
	}
}

func (g *graph) block(block *ast.BlockStmt, by types.Object) {
	if block == nil {
		return
	}

	for _, stmt := range block.List {
		g.stmt(stmt, by)
	}
}

func isGlobal(obj types.Object) bool {
	return obj.Parent() == obj.Pkg().Scope()
}

func (g *graph) decl(decl ast.Decl, parent types.Object) {
	switch decl := decl.(type) {
	case *ast.GenDecl:
		switch decl.Tok {
		case token.IMPORT:
			// Nothing to do

		case token.CONST:
			for _, spec := range decl.Specs {
				vspec := spec.(*ast.ValueSpec)
				assert(len(vspec.Values) == 0 || len(vspec.Values) == len(vspec.Names))
				for i, name := range vspec.Names {
					obj := g.pass.TypesInfo.ObjectOf(name)
					g.see(obj)
					g.read(vspec.Type, obj)

					if len(vspec.Values) != 0 {
						g.read(vspec.Values[i], obj)
					}

					if name.Name == "_" {
						g.use(obj, parent, edgeBlankName)
					} else if token.IsExported(name.Name) && isGlobal(obj) {
						g.use(obj, nil, edgeExportedConstant)
					}
				}
			}

			// (10.1) if one constant out of a block of constants is used, mark all of them used
			groups := astutil.GroupSpecs(g.pass.Fset, decl.Specs)
			for _, group := range groups {
				if len(group) > 1 {
					for i, spec := range group[:len(group)-1] {
						names := spec.(*ast.ValueSpec).Names
						for j := range names[:len(names)-1] {
							// names[j] uses names[j+1]
							left := g.pass.TypesInfo.ObjectOf(names[j+1])
							right := g.pass.TypesInfo.ObjectOf(names[j])
							g.use(left, right, edgeConstGroup)
							g.use(right, left, edgeConstGroup)
						}
						left := g.pass.TypesInfo.ObjectOf(group[i+1].(*ast.ValueSpec).Names[0])
						right := g.pass.TypesInfo.ObjectOf(names[len(names)-1])
						g.use(left, right, edgeConstGroup)
						g.use(right, left, edgeConstGroup)
					}
				}
			}

		case token.TYPE:
			// XXX handle aliases

			for _, spec := range decl.Specs {
				tspec := spec.(*ast.TypeSpec)
				obj := g.pass.TypesInfo.ObjectOf(tspec.Name).(*types.TypeName)
				g.see(obj)
				if token.IsExported(tspec.Name.Name) && isGlobal(obj) {
					// (1.1) packages use exported named types
					g.use(g.pass.TypesInfo.ObjectOf(tspec.Name), nil, edgeExportedType)
				}

				// (2.5) named types use all their type parameters
				g.read(tspec.TypeParams, obj)

				g.namedType(obj, tspec.Type)

				if tspec.Name.Name == "_" {
					g.use(obj, parent, edgeBlankName)
				}
			}

		case token.VAR:
			for _, spec := range decl.Specs {
				vspec := spec.(*ast.ValueSpec)
				for i, name := range vspec.Names {
					obj := g.pass.TypesInfo.ObjectOf(name)
					g.see(obj)
					// variables and constants use their types
					g.read(vspec.Type, obj)

					if len(vspec.Names) == len(vspec.Values) {
						// One value per variable
						g.read(vspec.Values[i], obj)
					} else if len(vspec.Values) != 0 {
						// Multiple variables initialized with a single rhs
						// assert(len(vspec.Values) == 1)
						if len(vspec.Values) != 1 {
							panic(g.pass.Fset.PositionFor(vspec.Pos(), false))
						}
						g.read(vspec.Values[0], obj)
					}

					if token.IsExported(name.Name) && isGlobal(obj) {
						// (1.3) packages use exported variables
						g.use(obj, nil, edgeExportedVariable)
					}

					if name.Name == "_" {
						g.use(obj, parent, edgeBlankName)
					}
				}
			}

		default:
			panic(fmt.Sprintf("unexpected token %s", decl.Tok))
		}

	case *ast.FuncDecl:
		obj := typeparams.OriginMethod(g.pass.TypesInfo.ObjectOf(decl.Name).(*types.Func))
		g.see(obj)

		if token.IsExported(decl.Name.Name) {
			if decl.Recv == nil {
				// (1.2) packages use exported functions
				g.use(obj, nil, edgeExportedFunction)
			} else {
				// (2.1) named types use exported methods
				tname := typeutil.Dereference(g.pass.TypesInfo.TypeOf(decl.Recv.List[0].Type)).(*types.Named).Obj()
				g.use(obj, tname, edgeExportedMethod)
			}
		} else if decl.Name.Name == "init" {
			// (1.5) packages use init functions
			g.use(obj, nil, edgeInitFunction)
		} else if decl.Name.Name == "main" && g.pass.Pkg.Name() == "main" {
			// (1.7) packages use the main function iff in the main package
			g.use(obj, nil, edgeMainFunction)
		}

		// (4.1) functions use all their arguments, return parameters and receivers
		// (4.10) all their type parameters
		g.read(decl.Type, obj)
		g.block(decl.Body, obj)

		if decl.Name.Name == "_" {
			g.use(obj, nil, edgeBlankName)
		}

		if decl.Doc != nil {
			for _, cmt := range decl.Doc.List {
				if strings.HasPrefix(cmt.Text, "//go:cgo_export_") {
					// (1.6) packages use functions exported to cgo
					g.use(obj, nil, edgeCgoExported)
				}
			}
		}

	default:
		// We do not cover BadDecl, but we shouldn't ever see one of those
		lint.ExhaustiveTypeSwitch(decl)
	}
}

func (g *graph) stmt(stmt ast.Stmt, by types.Object) {
	if stmt == nil {
		return
	}

	for {
		// We don't care about labels, so unwrap LabeledStmts. Note that a label can itself be labeled.
		if labeled, ok := stmt.(*ast.LabeledStmt); ok {
			stmt = labeled.Stmt
		} else {
			break
		}
	}

	switch stmt := stmt.(type) {
	case *ast.AssignStmt:
		for _, lhs := range stmt.Lhs {
			g.write(lhs, by)
		}
		for _, rhs := range stmt.Rhs {
			g.read(rhs, by)
		}

	case *ast.BlockStmt:
		g.block(stmt, by)

	case *ast.BranchStmt:
		// Nothing to do

	case *ast.DeclStmt:
		g.decl(stmt.Decl, by)

	case *ast.DeferStmt:
		g.read(stmt.Call, by)

	case *ast.ExprStmt:
		g.read(stmt.X, by)

	case *ast.ForStmt:
		g.stmt(stmt.Init, by)
		g.read(stmt.Cond, by)
		g.stmt(stmt.Post, by)
		g.block(stmt.Body, by)

	case *ast.GoStmt:
		g.read(stmt.Call, by)

	case *ast.IfStmt:
		g.stmt(stmt.Init, by)
		g.read(stmt.Cond, by)
		g.block(stmt.Body, by)
		g.stmt(stmt.Else, by)

	case *ast.IncDecStmt:
		// Increment/decrement have no effect on the usedness of an object.

	case *ast.RangeStmt:
		g.write(stmt.Key, by)
		g.write(stmt.Value, by)
		g.read(stmt.X, by)
		g.block(stmt.Body, by)

	case *ast.ReturnStmt:
		for _, ret := range stmt.Results {
			g.read(ret, by)
		}

	case *ast.SelectStmt:
		for _, clause_ := range stmt.Body.List {
			clause := clause_.(*ast.CommClause)
			switch comm := clause.Comm.(type) {
			case *ast.SendStmt:
				g.read(comm.Chan, by)
				g.read(comm.Value, by)
			case *ast.ExprStmt:
				g.read(comm.X.(*ast.UnaryExpr).X, by)
			case *ast.AssignStmt:
				for _, lhs := range comm.Lhs {
					g.write(lhs, by)
				}
				for _, rhs := range comm.Rhs {
					g.read(rhs, by)
				}
			case nil:
			default:
				lint.ExhaustiveTypeSwitch(comm)
			}
			for _, body := range clause.Body {
				g.stmt(body, by)
			}
		}

	case *ast.SendStmt:
		g.read(stmt.Chan, by)
		g.read(stmt.Value, by)

	case *ast.SwitchStmt:
		g.stmt(stmt.Init, by)
		g.read(stmt.Tag, by)
		for _, clause_ := range stmt.Body.List {
			clause := clause_.(*ast.CaseClause)
			for _, expr := range clause.List {
				g.read(expr, by)
			}
			for _, body := range clause.Body {
				g.stmt(body, by)
			}
		}

	case *ast.TypeSwitchStmt:
		g.stmt(stmt.Init, by)
		g.stmt(stmt.Assign, by)
		for _, clause_ := range stmt.Body.List {
			clause := clause_.(*ast.CaseClause)
			for _, expr := range clause.List {
				g.read(expr, by)
			}
			for _, body := range clause.Body {
				g.stmt(body, by)
			}
		}

	case *ast.EmptyStmt:
		// Nothing to do

	default:
		lint.ExhaustiveTypeSwitch(stmt)
	}
}

func (g *graph) namedType(typ *types.TypeName, spec ast.Expr) {
	// (2.2) named types use the type they're based on

	if st, ok := spec.(*ast.StructType); ok {
		// Named structs are special in that its unexported fields are only used if they're being written to. That is,
		// the fields are not used by the named type itself, nor are the types of the fields.
		for _, field := range st.Fields.List {
			for _, name := range field.Names {
				obj := g.pass.TypesInfo.ObjectOf(name)
				g.see(obj)
				// (7.2) fields use their types
				g.read(field.Type, obj)
				if name.Name == "_" {
					g.use(obj, typ, edgeBlankField)
				} else if token.IsExported(name.Name) {
					// (6.2) structs use exported fields
					g.use(obj, typ, edgeExportedField)
				}

				if isNoCopyType(obj.Type()) {
					// (6.1) structs use fields of type NoCopy sentinel
					g.use(obj, typ, edgeNoCopySentinel)
				}
			}
		}
	} else {
		g.read(spec, typ)
	}
}

func (g *graph) results() (used, unused []types.Object) {
	g.color(g.Root)

	// OPT(dh): can we find meaningful initial capacities for the used and unused slices?

	for _, n := range g.Nodes {
		if obj, ok := n.obj.(types.Object); ok {
			switch obj := obj.(type) {
			case *types.Var:
				// don't report unnamed variables (interface embedding)
				if obj.Name() == "" && obj.IsField() {
					continue
				}
			case types.Object:
				// XXX do we still need this?
				if obj.Name() == "_" {
					continue
				}
			}

			if obj.Pkg() != nil {
				if n.seen {
					used = append(used, obj)
				} else if !n.quiet {
					if obj.Pkg() != g.pass.Pkg {
						continue
					}
					unused = append(unused, obj)
				}
			}
		}
	}

	return used, unused
}

func run(pass *analysis.Pass) (interface{}, error) {
	g := &graph{
		pass:  pass,
		Nodes: map[types.Object]*node{},
	}
	g.Root = g.newNode(nil)
	g.entry(pass)
	used, unused := g.results()

	// XXX don't flag fields in unused structs
	// XXX don't flag methods in unused interfaces
	// XXX don't flag local variables

	if false {
		// XXX make debug printing conditional
		debugNode := func(n *node) {
			if n.obj == nil {
				debugf("n%d [label=\"Root\"];\n", n.id)
			} else {
				color := "red"
				if n.seen {
					color = "green"
				}
				debugf("n%d [label=%q, color=%q];\n", n.id, fmt.Sprintf("(%T) %s", n.obj, n.obj), color)
			}
			for _, e := range n.used {
				for i := edgeKind(1); i < 64; i++ {
					if e.kind.is(1 << i) {
						debugf("n%d -> n%d [label=%q];\n", n.id, e.node.id, edgeKind(1<<i))
					}
				}
			}
		}

		debugf("digraph{\n")
		debugNode(g.Root)
		for _, v := range g.Nodes {
			debugNode(v)
		}

		debugf("}\n")
	}

	return Result{Used: used, Unused: unused}, nil
}

func assert(b bool) {
	if !b {
		panic("failed assertion")
	}
}
