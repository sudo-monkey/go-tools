package unused2

import (
	"reflect"

	"golang.org/x/tools/go/analysis"
	"honnef.co/go/tools/analysis/facts/directives"
	"honnef.co/go/tools/analysis/facts/generated"
	"honnef.co/go/tools/analysis/lint"
	"honnef.co/go/tools/unused"
)

// XXX aliases/function vars are temporary and will vanish once we replace unused with unused2

type Result = unused.Result
type SerializedResult = unused.SerializedResult
type SerializedObject = unused.SerializedObject

var Serialize = unused.Serialize

// XXX all of these are only exported so we can refer to them in unused2, unexport them when we replace unused with
// unused2

var typString = unused.TypString
var isIrrelevant = unused.IsIrrelevant
var isNoCopyType = unused.IsNoCopyType

var Analyzer = &lint.Analyzer{
	Doc: &lint.Documentation{
		Title: "Unused code",
	},
	Analyzer: &analysis.Analyzer{
		Name:       "U1000",
		Doc:        "Unused code",
		Run:        run,
		Requires:   []*analysis.Analyzer{generated.Analyzer, directives.Analyzer},
		ResultType: reflect.TypeOf(Result{}),
	},
}

func run(pass *analysis.Pass) (interface{}, error) {
	return nil, nil
}
