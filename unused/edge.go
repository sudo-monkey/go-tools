package unused

//go:generate go run golang.org/x/tools/cmd/stringer@master -type EdgeKind
type EdgeKind uint64

func (e EdgeKind) is(o EdgeKind) bool {
	return e&o != 0
}

const (
	edgeAlias EdgeKind = 1 << iota
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
)
