"use strict";

const EXPECTED_COMPILER_VERSION = "5.9.3";

function refuse(code, message, node, sourceFile) {
  let line = null;
  let column = null;
  if (node && sourceFile) {
    const position = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
    line = position.line + 1;
    column = position.character + 1;
  }
  process.stdout.write(JSON.stringify({ status: "refused", code, message, line, column }));
  process.exit(0);
}

if (process.argv.length !== 6) {
  refuse("frontend.typescript.invocation", "expected compiler, source, requested-symbol, and language arguments");
}

const compilerPath = process.argv[2];
const sourcePath = process.argv[3];
const requestedSymbols = JSON.parse(process.argv[4]);
const sourceLanguage = process.argv[5];
if (!["javascript", "typescript"].includes(sourceLanguage)) {
  refuse("frontend.typescript.invocation", `unsupported source language ${sourceLanguage}`);
}
const isJavaScript = sourceLanguage === "javascript";
const diagnosticPrefix = `frontend.${sourceLanguage}`;
const ts = require(compilerPath);
if (ts.version !== EXPECTED_COMPILER_VERSION) {
  refuse(
    `${diagnosticPrefix}.compiler-version`,
    `expected TypeScript ${EXPECTED_COMPILER_VERSION}, found ${ts.version}`,
  );
}

const options = {
  strict: true,
  noEmit: true,
  target: ts.ScriptTarget.ES2022,
  module: ts.ModuleKind.ESNext,
  moduleResolution: ts.ModuleResolutionKind.Bundler,
  exactOptionalPropertyTypes: true,
  noUncheckedIndexedAccess: true,
  useUnknownInCatchVariables: true,
  noImplicitOverride: true,
  noFallthroughCasesInSwitch: true,
  noImplicitReturns: true,
  allowUnreachableCode: false,
  skipLibCheck: false,
  allowJs: isJavaScript,
  checkJs: isJavaScript,
};
const program = ts.createProgram([sourcePath], options);
const sourceFile = program.getSourceFile(sourcePath);
if (!sourceFile) {
  refuse(`${diagnosticPrefix}.source-missing`, `compiler did not load ${sourcePath}`);
}
const diagnostics = ts.getPreEmitDiagnostics(program);
if (diagnostics.length > 0) {
  const diagnostic = diagnostics[0];
  let line = null;
  let column = null;
  if (diagnostic.file && diagnostic.start !== undefined) {
    const position = diagnostic.file.getLineAndCharacterOfPosition(diagnostic.start);
    line = position.line + 1;
    column = position.character + 1;
  }
  const message = diagnostics.map(item => {
    const text = ts.flattenDiagnosticMessageText(item.messageText, "\n");
    if (!item.file || item.start === undefined) {
      return `TS${item.code}: ${text}`;
    }
    const position = item.file.getLineAndCharacterOfPosition(item.start);
    return `${item.file.fileName}:${position.line + 1}:${position.character + 1}: ` +
      `TS${item.code}: ${text}`;
  }).join("\n");
  process.stdout.write(JSON.stringify({
    status: "refused",
    code: `${diagnosticPrefix}.strict-typecheck`,
    message,
    line,
    column,
  }));
  process.exit(0);
}

const checker = program.getTypeChecker();
const functions = [];
const functionNames = new Set();
const functionDeclarations = [];
const functionSymbols = new Map();
const callEdges = new Map();
const functionSignatures = new Map();
const declaredRecordTypes = new Map();
const classes = [];
const classDeclarations = [];
const classSymbols = new Map();
const classByName = new Map();
const classMemberDeclarations = [];
const classMembers = new Map();
const classFields = new Map();

function canonicalFields(fields) {
  return Array.from(fields, field => ({ name: field.name, type_name: field.type_name }))
    .sort((left, right) => left.name < right.name ? -1 : left.name > right.name ? 1 : 0);
}

function fieldsEqual(left, right) {
  const canonicalLeft = canonicalFields(left);
  const canonicalRight = canonicalFields(right);
  return canonicalLeft.length === canonicalRight.length && canonicalLeft.every(
    (field, index) => field.name === canonicalRight[index].name &&
      field.type_name === canonicalRight[index].type_name,
  );
}

function validRecordFieldName(name) {
  if (name === "__proto__" || name.length === 0) {
    return false;
  }
  const first = name.charCodeAt(0);
  const validFirst = first === 36 || first === 95 ||
    (first >= 65 && first <= 90) || (first >= 97 && first <= 122);
  if (!validFirst) {
    return false;
  }
  for (let index = 1; index < name.length; index += 1) {
    const code = name.charCodeAt(index);
    if (
      code !== 36 && code !== 95 &&
      (code < 48 || code > 57) &&
      (code < 65 || code > 90) &&
      (code < 97 || code > 122)
    ) {
      return false;
    }
  }
  return true;
}

function fallthroughGraph() {
  return { kind: "fallthrough" };
}

function sequenceGraph(items) {
  return { kind: "sequence", items };
}

function branchGraph(branches) {
  return { kind: "branch", branches };
}

function sourceLocation(node) {
  const position = sourceFile.getLineAndCharacterOfPosition(node.getStart(sourceFile));
  return { line: position.line + 1, column: position.character + 1 };
}

function graphContainsCall(graph) {
  if (
    graph.kind === "call" ||
    graph.kind === "await-call" ||
    graph.kind === "promise-adopt" ||
    graph.kind === "callback-invoke"
  ) {
    return true;
  }
  if (graph.kind === "sequence") {
    return graph.items.some(graphContainsCall);
  }
  if (graph.kind === "branch") {
    return graph.branches.some(graphContainsCall);
  }
  if (graph.kind === "try-catch") {
    return graphContainsCall(graph.try_body) || graphContainsCall(graph.catch_body);
  }
  if (graph.kind === "terminal-switch") {
    return graphContainsCall(graph.discriminant) ||
      graph.cases.some(item => graphContainsCall(item.body)) ||
      graphContainsCall(graph.default_body);
  }
  return false;
}

function primitiveType(annotation, role) {
  if (!annotation) {
    refuse(
      `${diagnosticPrefix}.explicit-type-required`,
      `${role} requires an explicit type annotation`,
      annotation || sourceFile,
      sourceFile,
    );
  }
  const type = checker.getTypeFromTypeNode(annotation);
  const rendered = checker.typeToString(type);
  if (!["number", "boolean", "string", "void"].includes(rendered)) {
    refuse(
      `${diagnosticPrefix}.type-unsupported`,
      `${role} has unsupported compiler-resolved type ${rendered}`,
      annotation,
      sourceFile,
    );
  }
  return rendered;
}

function asyncResultType(annotation, role) {
  if (
    !annotation ||
    !ts.isTypeReferenceNode(annotation) ||
    !ts.isIdentifier(annotation.typeName) ||
    annotation.typeName.text !== "Promise" ||
    !annotation.typeArguments ||
    annotation.typeArguments.length !== 1
  ) {
    refuse(
      `${diagnosticPrefix}.async-return-type`,
      `${role} must be explicitly annotated as Promise<number>, Promise<boolean>, Promise<string>, or Promise<void>`,
      annotation || sourceFile,
      sourceFile,
    );
  }
  const promiseType = checker.getTypeFromTypeNode(annotation);
  const symbol = promiseType.aliasSymbol || promiseType.symbol ||
    (promiseType.target ? promiseType.target.symbol : undefined);
  if (!symbol || symbol.name !== "Promise") {
    refuse(
      `${diagnosticPrefix}.async-return-type`,
      `${role} must resolve to the standard Promise type`,
      annotation,
      sourceFile,
    );
  }
  return primitiveType(annotation.typeArguments[0], `${role} fulfillment`);
}

function primitiveName(type) {
  const widened = checker.getBaseTypeOfLiteralType(checker.getWidenedType(type));
  if ((widened.flags & ts.TypeFlags.Number) !== 0) {
    return "number";
  }
  if ((widened.flags & ts.TypeFlags.Boolean) !== 0) {
    return "boolean";
  }
  if ((widened.flags & ts.TypeFlags.String) !== 0) {
    return "string";
  }
  return null;
}

function recordFieldsFromMembers(members, role, requireReadonly = true) {
  if (members.length === 0) {
    refuse(
      `${diagnosticPrefix}.record-type-unsupported`,
      `${role} record type must declare at least one field`,
      sourceFile,
      sourceFile,
    );
  }
  const fields = [];
  const names = new Set();
  for (const member of members) {
    if (
      !ts.isPropertySignature(member) ||
      !ts.isIdentifier(member.name) ||
      member.questionToken ||
      !member.type ||
      (member.modifiers && Array.from(member.modifiers).some(
        modifier => modifier.kind !== ts.SyntaxKind.ReadonlyKeyword,
      )) ||
      (requireReadonly && (
        !member.modifiers ||
        !Array.from(member.modifiers).some(modifier => modifier.kind === ts.SyntaxKind.ReadonlyKeyword)
      ))
    ) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `${role} requires required readonly primitive property signatures only`,
        member,
        sourceFile,
      );
    }
    const name = member.name.text;
    if (!validRecordFieldName(name) || names.has(name)) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `${role} has a duplicate or reserved record field ${name}`,
        member.name,
        sourceFile,
      );
    }
    const typeName = primitiveName(checker.getTypeFromTypeNode(member.type));
    if (!typeName) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `${role} field ${name} must be exactly number, boolean, or string`,
        member.type,
        sourceFile,
      );
    }
    names.add(name);
    fields.push({ name, type_name: typeName });
  }
  return canonicalFields(fields);
}

function compilerRecordFields(annotation, role) {
  const type = checker.getTypeFromTypeNode(annotation);
  const rendered = checker.typeToString(type);
  if (
    (type.flags & (
      ts.TypeFlags.Any |
      ts.TypeFlags.Unknown |
      ts.TypeFlags.Union |
      ts.TypeFlags.Intersection
    )) !== 0 ||
    (type.flags & ts.TypeFlags.Object) === 0 ||
    checker.isTupleType(type) ||
    checker.getIndexInfosOfType(type).length !== 0 ||
    checker.getSignaturesOfType(type, ts.SignatureKind.Call).length !== 0 ||
    checker.getSignaturesOfType(type, ts.SignatureKind.Construct).length !== 0
  ) {
    refuse(
      `${diagnosticPrefix}.record-type-unsupported`,
      `${role} has unsupported record type ${rendered}`,
      annotation,
      sourceFile,
    );
  }
  const properties = checker.getPropertiesOfType(type);
  if (properties.length === 0) {
    refuse(
      `${diagnosticPrefix}.record-type-unsupported`,
      `${role} record type must declare at least one field`,
      annotation,
      sourceFile,
    );
  }
  const fields = [];
  const names = new Set();
  for (const property of properties) {
    const typeName = primitiveName(checker.getTypeOfSymbolAtLocation(property, annotation));
    if (
      !validRecordFieldName(property.name) ||
      names.has(property.name) ||
      (property.flags & ts.SymbolFlags.Optional) !== 0 ||
      !typeName
    ) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `${role} field ${property.name} must be one required primitive field`,
        annotation,
        sourceFile,
      );
    }
    names.add(property.name);
    fields.push({ name: property.name, type_name: typeName });
  }
  return canonicalFields(fields);
}

function recordType(annotation, role) {
  if (!annotation) {
    return null;
  }
  if (isJavaScript) {
    const type = checker.getTypeFromTypeNode(annotation);
    if (
      (type.flags & ts.TypeFlags.Object) === 0 ||
      checker.isTupleType(type) ||
      checker.getSignaturesOfType(type, ts.SignatureKind.Call).length !== 0 ||
      checker.getSignaturesOfType(type, ts.SignatureKind.Construct).length !== 0 ||
      checker.getPropertiesOfType(type).length === 0
    ) {
      return null;
    }
    return { kind: "record", fields: compilerRecordFields(annotation, role), provenance: "parameter" };
  }
  if (ts.isTypeLiteralNode(annotation)) {
    return {
      kind: "record",
      fields: recordFieldsFromMembers(annotation.members, role),
      provenance: "parameter",
    };
  }
  if (
    ts.isTypeReferenceNode(annotation) &&
    ts.isIdentifier(annotation.typeName) &&
    !annotation.typeArguments
  ) {
    const fields = declaredRecordTypes.get(annotation.typeName.text);
    if (fields) {
      return { kind: "record", fields, provenance: "parameter" };
    }
  }
  if (
    ts.isTypeReferenceNode(annotation) &&
    ts.isIdentifier(annotation.typeName) &&
    annotation.typeName.text === "Readonly" &&
    annotation.typeArguments &&
    annotation.typeArguments.length === 1
  ) {
    const inner = annotation.typeArguments[0];
    if (ts.isTypeLiteralNode(inner)) {
      return {
        kind: "record",
        fields: recordFieldsFromMembers(inner.members, role, false),
        provenance: "parameter",
      };
    }
    if (ts.isTypeReferenceNode(inner) && ts.isIdentifier(inner.typeName) && !inner.typeArguments) {
      const fields = declaredRecordTypes.get(inner.typeName.text);
      if (fields) {
        return { kind: "record", fields, provenance: "parameter" };
      }
    }
  }
  return null;
}

function readonlyCollectionType(annotation, role) {
  const type = checker.getTypeFromTypeNode(annotation);
  const rendered = checker.typeToString(type);
  if ((type.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.Union)) !== 0) {
    refuse(
      `${diagnosticPrefix}.collection-type-unsupported`,
      `${role} has unsupported collection type ${rendered}`,
      annotation,
      sourceFile,
    );
  }
  if (checker.isTupleType(type)) {
    const target = type.target || type;
    const elements = checker.getTypeArguments(type);
    if (
      target.readonly !== true ||
      target.hasRestElement === true ||
      (typeof target.fixedLength === "number" && target.fixedLength !== elements.length) ||
      (typeof target.minLength === "number" && target.minLength !== elements.length)
    ) {
      refuse(
        `${diagnosticPrefix}.collection-type-unsupported`,
        `${role} requires a fixed readonly tuple`,
        annotation,
        sourceFile,
      );
    }
    const primitiveElements = elements.map(primitiveName);
    if (primitiveElements.some(element => element === null)) {
      refuse(
        `${diagnosticPrefix}.collection-element-type-unsupported`,
        `${role} tuple elements must each have one primitive number, boolean, or string type`,
        annotation,
        sourceFile,
      );
    }
    return { kind: "collection", collection: "tuple", elements: primitiveElements };
  }
  const targetName = type.target && type.target.symbol ? type.target.symbol.name : null;
  const symbolName = type.symbol ? type.symbol.name : null;
  if (targetName === "ReadonlyArray" || symbolName === "ReadonlyArray") {
    const elements = checker.getTypeArguments(type);
    const element = elements.length === 1 ? primitiveName(elements[0]) : null;
    if (!element) {
      refuse(
        `${diagnosticPrefix}.collection-element-type-unsupported`,
        `${role} ReadonlyArray element must have one primitive number, boolean, or string type`,
        annotation,
        sourceFile,
      );
    }
    return { kind: "collection", collection: "array", elements: [element] };
  }
  return null;
}

function parameterType(annotation, role) {
  if (!annotation) {
    refuse(
      `${diagnosticPrefix}.explicit-type-required`,
      `${role} requires an explicit type annotation`,
      sourceFile,
      sourceFile,
    );
  }
  const type = checker.getTypeFromTypeNode(annotation);
  const rendered = checker.typeToString(type);
  if (["number", "boolean", "string"].includes(rendered)) {
    return { kind: "primitive", primitive: rendered };
  }
  if (ts.isFunctionTypeNode(annotation)) {
    if (annotation.typeParameters) {
      refuse(
        `${diagnosticPrefix}.callback-signature-unsupported`,
        `${role} callback must be nongeneric`,
        annotation,
        sourceFile,
      );
    }
    const parameterTypes = [];
    for (const callbackParameter of annotation.parameters) {
      if (
        !ts.isIdentifier(callbackParameter.name) ||
        callbackParameter.dotDotDotToken ||
        callbackParameter.questionToken ||
        callbackParameter.initializer ||
        !callbackParameter.type
      ) {
        refuse(
          `${diagnosticPrefix}.callback-signature-unsupported`,
          `${role} callback parameters must be required, named, explicitly typed primitives`,
          callbackParameter,
          sourceFile,
        );
      }
      const callbackParameterType = primitiveType(
        callbackParameter.type,
        `${role} callback parameter ${callbackParameter.name.text}`,
      );
      if (callbackParameterType === "void") {
        refuse(
          `${diagnosticPrefix}.callback-signature-unsupported`,
          `${role} callback parameters cannot have void type`,
          callbackParameter,
          sourceFile,
        );
      }
      parameterTypes.push(callbackParameterType);
    }
    return {
      kind: "callback",
      parameter_types: parameterTypes,
      return_type: primitiveType(annotation.type, `${role} callback return`),
    };
  }
  const collection = readonlyCollectionType(annotation, role);
  if (collection) {
    return collection;
  }
  const record = recordType(annotation, role);
  if (record) {
    return record;
  }
  return { kind: "primitive", primitive: primitiveType(annotation, role) };
}

function formalDescriptor(descriptor) {
  if (descriptor.kind === "primitive") {
    return { kind: "primitive", type_name: descriptor.primitive };
  }
  if (descriptor.kind === "record") {
    return { kind: "record", fields: canonicalFields(descriptor.fields) };
  }
  if (descriptor.kind === "callback") {
    return {
      kind: "callback",
      parameter_types: descriptor.parameter_types,
      return_type: descriptor.return_type,
    };
  }
  if (descriptor.collection === "array") {
    return { kind: "readonly-array", element_type: descriptor.elements[0] };
  }
  return { kind: "readonly-tuple", element_types: descriptor.elements };
}

function actualDescriptor(descriptor) {
  if (descriptor.kind === "source-callback") {
    return {
      kind: "source-callback",
      function: descriptor.function,
      parameter_types: descriptor.parameter_types,
      return_type: descriptor.return_type,
    };
  }
  if (descriptor.kind === "record") {
    return { kind: "source-record", fields: canonicalFields(descriptor.fields) };
  }
  return formalDescriptor(descriptor);
}

function descriptorsCompatible(formal, actual) {
  if (formal.kind === "callback") {
    return actual.kind === "source-callback" &&
      formal.return_type === actual.return_type &&
      formal.parameter_types.length === actual.parameter_types.length &&
      formal.parameter_types.every((item, index) => item === actual.parameter_types[index]);
  }
  if (formal.kind !== actual.kind) {
    return false;
  }
  if (formal.kind === "primitive") {
    return formal.primitive === actual.primitive;
  }
  if (formal.kind === "record") {
    return actual.provenance === "source-literal" && fieldsEqual(formal.fields, actual.fields);
  }
  if (formal.collection === "tuple") {
    return actual.collection === "tuple" &&
      formal.elements.length === actual.elements.length &&
      formal.elements.every((item, index) => item === actual.elements[index]);
  }
  return actual.collection === "array" && formal.elements[0] === actual.elements[0];
}

function collectionBinding(expression, bindings, role) {
  if (!ts.isIdentifier(expression)) {
    refuse(
      `${diagnosticPrefix}.collection-base-unsupported`,
      `${role} requires a direct local collection identifier`,
      expression,
      sourceFile,
    );
  }
  const binding = bindings.get(expression.text);
  if (!binding || binding.kind !== "collection") {
    refuse(
      `${diagnosticPrefix}.collection-base-unsupported`,
      `${role} requires a readonly primitive array or fixed readonly tuple`,
      expression,
      sourceFile,
    );
  }
  return binding;
}

function nullishElementType(expression) {
  const type = checker.getTypeAtLocation(expression);
  if (!type.isUnion()) {
    return null;
  }
  let sawUndefined = false;
  let primitive = null;
  for (const member of type.types) {
    if ((member.flags & ts.TypeFlags.Undefined) !== 0) {
      sawUndefined = true;
      continue;
    }
    const memberPrimitive = primitiveName(member);
    if (!memberPrimitive || (primitive && primitive !== memberPrimitive)) {
      return null;
    }
    primitive = memberPrimitive;
  }
  return sawUndefined ? primitive : null;
}

function verifyCollectionElementAccess(expression, bindings, currentFunction, undefinedHandled) {
  if (expression.questionDotToken || !expression.argumentExpression) {
    refuse(
      `${diagnosticPrefix}.collection-index-unsupported`,
      "collection indexing must be direct and non-optional",
      expression,
      sourceFile,
    );
  }
  const binding = collectionBinding(expression.expression, bindings, "collection indexing");
  const indexGraph = verifyExpression(expression.argumentExpression, bindings, currentFunction);
  if (primitiveResolvedType(expression.argumentExpression, "collection index") !== "number") {
    refuse(
      `${diagnosticPrefix}.collection-index-type`,
      "collection index must have compiler-resolved number type",
      expression.argumentExpression,
      sourceFile,
    );
  }
  if (binding.collection === "tuple" && ts.isNumericLiteral(expression.argumentExpression)) {
    const index = Number(expression.argumentExpression.text);
    if (Number.isSafeInteger(index) && index >= 0 && index < binding.elements.length) {
      return indexGraph;
    }
  }
  if (!undefinedHandled || !nullishElementType(expression)) {
    refuse(
      `${diagnosticPrefix}.collection-index-undefined`,
      "non-fixed collection indexing requires compiler-visible undefined handling with ??",
      expression,
      sourceFile,
    );
  }
  return indexGraph;
}

function receiverClass(expression, bindings, currentFunction) {
  if (ts.isIdentifier(expression)) {
    const binding = bindings.get(expression.text);
    return binding && binding.kind === "instance" ? binding.class_name : null;
  }
  if (expression.kind === ts.SyntaxKind.ThisKeyword) {
    const member = classMembers.get(currentFunction);
    return member ? member.class_name : null;
  }
  return null;
}

function verifyCallExpression(expression, bindings, currentFunction, callKind) {
  if (
    (!ts.isIdentifier(expression.expression) && !ts.isPropertyAccessExpression(expression.expression)) ||
    expression.questionDotToken ||
    expression.typeArguments
  ) {
    refuse(
      `${diagnosticPrefix}.${callKind === "await" ? "await" : "call"}-target-unsupported`,
      "closed calls require one direct, non-optional source-function identifier or one compiler-resolved source instance method",
      expression,
      sourceFile,
    );
  }
  const currentSignature = functionSignatures.get(currentFunction);
  if (
    (callKind === "await" || callKind === "promise-adopt") &&
    (!currentSignature || currentSignature.execution !== "asynchronous")
  ) {
    refuse(
      `${diagnosticPrefix}.async-context-required`,
      `${callKind} is permitted only inside a source-owned async function`,
      expression,
      sourceFile,
    );
  }
  const callbackBinding = ts.isIdentifier(expression.expression)
    ? bindings.get(expression.expression.text)
    : undefined;
  if (callbackBinding && callbackBinding.kind === "callback") {
    if (callKind !== "call") {
      refuse(
        `${diagnosticPrefix}.async-callback-unsupported`,
        "callbacks cannot be awaited or adopted as promises in this fragment",
        expression,
        sourceFile,
      );
    }
    if (expression.arguments.length !== callbackBinding.parameter_types.length) {
      refuse(
        `${diagnosticPrefix}.callback-arity`,
        `callback ${expression.expression.text} must receive exactly ${callbackBinding.parameter_types.length} arguments`,
        expression,
        sourceFile,
      );
    }
    const argumentGraphs = [];
    const argumentDescriptors = [];
    for (let index = 0; index < expression.arguments.length; index += 1) {
      const argument = expression.arguments[index];
      if (ts.isSpreadElement(argument)) {
        refuse(
          `${diagnosticPrefix}.callback-spread-unsupported`,
          "callback invocations do not permit spread arguments",
          argument,
          sourceFile,
        );
      }
      const verified = verifyCallArgument(
        argument,
        { kind: "primitive", primitive: callbackBinding.parameter_types[index] },
        bindings,
        currentFunction,
      );
      argumentGraphs.push(verified.graph);
      argumentDescriptors.push(actualDescriptor(verified.descriptor));
    }
    return sequenceGraph([
      ...argumentGraphs,
      {
        kind: "callback-invoke",
        parameter: expression.expression.text,
        arguments: argumentDescriptors,
        ...sourceLocation(expression),
      },
    ]);
  }
  let symbolNode = expression.expression;
  let requiredClass = null;
  if (ts.isPropertyAccessExpression(expression.expression)) {
    if (expression.expression.questionDotToken) {
      refuse(
        `${diagnosticPrefix}.method-target-unsupported`,
        "source instance methods must be called directly and non-optionally",
        expression.expression,
        sourceFile,
      );
    }
    requiredClass = receiverClass(expression.expression.expression, bindings, currentFunction);
    if (!requiredClass) {
      refuse(
        `${diagnosticPrefix}.${callKind === "await" ? "await" : "call"}-target-unsupported`,
        "closed calls require one direct source function or one direct method on a closed source instance",
        expression.expression.expression,
        sourceFile,
      );
    }
    symbolNode = expression.expression.name;
  }
  const symbol = checker.getSymbolAtLocation(symbolNode);
  const callee = symbol ? functionSymbols.get(symbol) : undefined;
  const member = callee ? classMembers.get(callee) : undefined;
  if (requiredClass && (!member || member.kind !== "method" || member.class_name !== requiredClass)) {
    refuse(
      `${diagnosticPrefix}.method-dispatch-unsupported`,
      "method call did not resolve to one final method owned by the receiver's closed source class",
      expression.expression,
      sourceFile,
    );
  }
  if (!callee) {
    refuse(
      `${diagnosticPrefix}.${callKind === "await" ? "await" : "call"}-external-unsupported`,
      "call target is not one compiler-resolved source-owned verified function or final method",
      expression.expression,
      sourceFile,
    );
  }
  const signature = functionSignatures.get(callee);
  if (!signature || expression.arguments.length !== signature.parameters.length) {
    refuse(
      `${diagnosticPrefix}.call-arity`,
      `call to ${callee} must supply exactly ${signature ? signature.parameters.length : 0} arguments`,
      expression,
      sourceFile,
    );
  }
  if (callKind === "call" && signature.execution === "asynchronous") {
    refuse(
      `${diagnosticPrefix}.promise-use-unsupported`,
      `async source call ${callee} must be directly awaited or directly returned for promise adoption`,
      expression,
      sourceFile,
    );
  }
  if (callKind === "promise-adopt" && signature.execution !== "asynchronous") {
    refuse(
      `${diagnosticPrefix}.promise-adoption-invalid`,
      `promise adoption requires an async source callee, found synchronous ${callee}`,
      expression,
      sourceFile,
    );
  }
  const argumentGraphs = [];
  const argumentDescriptors = [];
  for (let index = 0; index < expression.arguments.length; index += 1) {
    const argument = expression.arguments[index];
    if (ts.isSpreadElement(argument)) {
      refuse(
        `${diagnosticPrefix}.call-spread-unsupported`,
        "closed calls do not permit spread arguments",
        argument,
        sourceFile,
      );
    }
    const verified = verifyCallArgument(
      argument,
      signature.parameters[index].descriptor,
      bindings,
      currentFunction,
    );
    argumentGraphs.push(verified.graph);
    argumentDescriptors.push(actualDescriptor(verified.descriptor));
  }
  callEdges.get(currentFunction).push({ callee, node: expression });
  const graphKind = callKind === "await"
    ? "await-call"
    : callKind === "promise-adopt"
      ? "promise-adopt"
      : "call";
  return sequenceGraph([
    ...argumentGraphs,
    { kind: graphKind, callee, arguments: argumentDescriptors, ...sourceLocation(expression) },
  ]);
}

function unwrapParentheses(expression) {
  let current = expression;
  while (ts.isParenthesizedExpression(current)) {
    current = current.expression;
  }
  return current;
}

function verifyExpression(expression, bindings, currentFunction, context = "value") {
  if (
    ts.isNumericLiteral(expression) ||
    ts.isStringLiteral(expression) ||
    expression.kind === ts.SyntaxKind.TrueKeyword ||
    expression.kind === ts.SyntaxKind.FalseKeyword
  ) {
    return fallthroughGraph();
  }
  if (ts.isIdentifier(expression)) {
    const binding = bindings.get(expression.text);
    if (!binding) {
      refuse(
        `${diagnosticPrefix}.expression-identifier`,
        `expression reads non-local identifier ${expression.text}`,
        expression,
        sourceFile,
      );
    }
    if (binding.kind === "collection" && context !== "call-argument") {
      refuse(
        `${diagnosticPrefix}.collection-value-unsupported`,
        `collection ${expression.text} may only be read through canonical length/index access or passed to a verified source function`,
        expression,
        sourceFile,
      );
    }
    if (binding.kind === "record") {
      refuse(
        `${diagnosticPrefix}.record-value-unsupported`,
        `record ${expression.text} may only be read through direct own properties or passed by source-literal provenance to a verified private helper`,
        expression,
        sourceFile,
      );
    }
    if (binding.kind === "opaque-catch") {
      refuse(
        `${diagnosticPrefix}.catch-binding-use-unsupported`,
        `catch binding ${expression.text} is opaque and cannot be read or narrowed`,
        expression,
        sourceFile,
      );
    }
    if (binding.kind === "callback") {
      refuse(
        `${diagnosticPrefix}.callback-value-unsupported`,
        `callback ${expression.text} may only be invoked directly`,
        expression,
        sourceFile,
      );
    }
    if (binding.kind === "instance") {
      refuse(
        `${diagnosticPrefix}.class-instance-escape-unsupported`,
        `class instance ${expression.text} may only receive direct source-method calls or direct readonly field reads`,
        expression,
        sourceFile,
      );
    }
    return fallthroughGraph();
  }
  if (ts.isParenthesizedExpression(expression)) {
    return verifyExpression(expression.expression, bindings, currentFunction, context);
  }
  if (ts.isPrefixUnaryExpression(expression)) {
    if (![ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.ExclamationToken, ts.SyntaxKind.TildeToken].includes(expression.operator)) {
      refuse(`${diagnosticPrefix}.unary-operator`, "unsupported unary operator", expression, sourceFile);
    }
    return verifyExpression(expression.operand, bindings, currentFunction);
  }
  if (ts.isBinaryExpression(expression)) {
    const safeOperators = new Set([
      ts.SyntaxKind.PlusToken,
      ts.SyntaxKind.MinusToken,
      ts.SyntaxKind.AsteriskToken,
      ts.SyntaxKind.SlashToken,
      ts.SyntaxKind.PercentToken,
      ts.SyntaxKind.AsteriskAsteriskToken,
      ts.SyntaxKind.LessThanToken,
      ts.SyntaxKind.LessThanEqualsToken,
      ts.SyntaxKind.GreaterThanToken,
      ts.SyntaxKind.GreaterThanEqualsToken,
      ts.SyntaxKind.EqualsEqualsEqualsToken,
      ts.SyntaxKind.ExclamationEqualsEqualsToken,
      ts.SyntaxKind.AmpersandAmpersandToken,
      ts.SyntaxKind.BarBarToken,
      ts.SyntaxKind.QuestionQuestionToken,
      ts.SyntaxKind.AmpersandToken,
      ts.SyntaxKind.BarToken,
      ts.SyntaxKind.CaretToken,
      ts.SyntaxKind.LessThanLessThanToken,
      ts.SyntaxKind.GreaterThanGreaterThanToken,
      ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken,
    ]);
    if (!safeOperators.has(expression.operatorToken.kind)) {
      refuse(`${diagnosticPrefix}.binary-operator`, "unsupported binary operator", expression.operatorToken, sourceFile);
    }
    if (expression.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken) {
      if (ts.isElementAccessExpression(expression.left)) {
        const leftGraph = verifyCollectionElementAccess(expression.left, bindings, currentFunction, true);
        const rightGraph = verifyExpression(expression.right, bindings, currentFunction);
        return sequenceGraph([leftGraph, branchGraph([rightGraph, fallthroughGraph()])]);
      } else {
        const leftGraph = verifyExpression(expression.left, bindings, currentFunction);
        const rightGraph = verifyExpression(expression.right, bindings, currentFunction);
        return sequenceGraph([leftGraph, branchGraph([rightGraph, fallthroughGraph()])]);
      }
    }
    const leftGraph = verifyExpression(expression.left, bindings, currentFunction);
    const rightGraph = verifyExpression(expression.right, bindings, currentFunction);
    if (
      expression.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken ||
      expression.operatorToken.kind === ts.SyntaxKind.BarBarToken
    ) {
      return sequenceGraph([leftGraph, branchGraph([rightGraph, fallthroughGraph()])]);
    }
    return sequenceGraph([leftGraph, rightGraph]);
  }
  if (ts.isConditionalExpression(expression)) {
    const conditionGraph = verifyExpression(expression.condition, bindings, currentFunction);
    const trueGraph = verifyExpression(expression.whenTrue, bindings, currentFunction);
    const falseGraph = verifyExpression(expression.whenFalse, bindings, currentFunction);
    return sequenceGraph([conditionGraph, branchGraph([trueGraph, falseGraph])]);
  }
  if (ts.isAwaitExpression(expression)) {
    const awaited = unwrapParentheses(expression.expression);
    if (!ts.isCallExpression(awaited)) {
      refuse(
        `${diagnosticPrefix}.await-source-unsupported`,
        "await requires one direct call to a source-owned function; external and unknown thenables are not modeled",
        expression.expression,
        sourceFile,
      );
    }
    return verifyCallExpression(awaited, bindings, currentFunction, "await");
  }
  if (ts.isCallExpression(expression)) {
    return verifyCallExpression(expression, bindings, currentFunction, "call");
  }
  if (ts.isPropertyAccessExpression(expression)) {
    const owningClass = receiverClass(expression.expression, bindings, currentFunction);
    if (owningClass) {
      const symbol = checker.getSymbolAtLocation(expression.name);
      const field = symbol ? classFields.get(symbol) : undefined;
      if (
        expression.questionDotToken ||
        !field ||
        field.class_name !== owningClass ||
        primitiveResolvedType(expression, `field ${owningClass}.${expression.name.text}`) !==
          field.field.type_name
      ) {
        refuse(
          `${diagnosticPrefix}.class-property-unsupported`,
          "closed source instances expose only compiler-resolved direct readonly primitive fields",
          expression,
          sourceFile,
        );
      }
      return fallthroughGraph();
    }
    if (ts.isIdentifier(expression.expression)) {
      const binding = bindings.get(expression.expression.text);
      if (binding && binding.kind === "record") {
        const field = binding.fields.find(item => item.name === expression.name.text);
        if (expression.questionDotToken || !field) {
          refuse(
            `${diagnosticPrefix}.record-property-unsupported`,
            "sealed records expose only direct, non-optional own fields",
            expression,
            sourceFile,
          );
        }
        return fallthroughGraph();
      }
    }
    if (expression.questionDotToken || expression.name.text !== "length") {
      refuse(
        `${diagnosticPrefix}.collection-property-unsupported`,
        "readonly collections expose only direct, non-optional .length",
        expression,
        sourceFile,
      );
    }
    collectionBinding(expression.expression, bindings, "collection length");
    return fallthroughGraph();
  }
  if (ts.isElementAccessExpression(expression)) {
    if (
      ts.isIdentifier(expression.expression) &&
      bindings.get(expression.expression.text)?.kind === "record"
    ) {
      refuse(
        `${diagnosticPrefix}.record-dynamic-access-unsupported`,
        "sealed record fields must be read with direct property syntax",
        expression,
        sourceFile,
      );
    }
    return verifyCollectionElementAccess(expression, bindings, currentFunction, false);
  }
  refuse(
    `${diagnosticPrefix}.expression-unsupported`,
    `unsupported expression kind ${ts.SyntaxKind[expression.kind]}`,
    expression,
    sourceFile,
  );
}

function primitiveResolvedType(node, role) {
  const type = checker.getTypeAtLocation(node);
  const primitive = primitiveName(type);
  if (!primitive) {
    refuse(
      `${diagnosticPrefix}.local-type-unsupported`,
      `${role} has unsupported compiler-resolved type ${checker.typeToString(type)}`,
      node,
      sourceFile,
    );
  }
  return primitive;
}

function arrayLiteralInitializer(initializer) {
  if (ts.isArrayLiteralExpression(initializer)) {
    return { literal: initializer, assertedConst: false };
  }
  if (
    ts.isAsExpression(initializer) &&
    ts.isTypeReferenceNode(initializer.type) &&
    ts.isIdentifier(initializer.type.typeName) &&
    initializer.type.typeName.text === "const" &&
    ts.isArrayLiteralExpression(initializer.expression)
  ) {
    return { literal: initializer.expression, assertedConst: true };
  }
  return null;
}

function objectLiteralInitializer(initializer) {
  if (ts.isObjectLiteralExpression(initializer)) {
    return { literal: initializer, satisfies: null };
  }
  if (ts.isParenthesizedExpression(initializer)) {
    return objectLiteralInitializer(initializer.expression);
  }
  if (ts.isSatisfiesExpression(initializer)) {
    const inner = objectLiteralInitializer(initializer.expression);
    return inner ? { literal: inner.literal, satisfies: initializer.type } : null;
  }
  if (
    ts.isAsExpression(initializer) &&
    ts.isTypeReferenceNode(initializer.type) &&
    ts.isIdentifier(initializer.type.typeName) &&
    initializer.type.typeName.text === "const"
  ) {
    return objectLiteralInitializer(initializer.expression);
  }
  return null;
}

function verifyRecordLiteral(literal, expectedFields, bindings, currentFunction) {
  if (literal.properties.length === 0) {
    refuse(
      `${diagnosticPrefix}.record-literal-unsupported`,
      "sealed source records must contain at least one primitive field",
      literal,
      sourceFile,
    );
  }
  const fields = [];
  const graphs = [];
  const names = new Set();
  for (const property of literal.properties) {
    let name;
    let value;
    if (ts.isPropertyAssignment(property) && ts.isIdentifier(property.name)) {
      name = property.name.text;
      value = property.initializer;
    } else if (ts.isShorthandPropertyAssignment(property) && !property.objectAssignmentInitializer) {
      name = property.name.text;
      value = property.name;
    } else {
      refuse(
        `${diagnosticPrefix}.record-literal-shape-unsupported`,
        "sealed source records permit identifier property assignments and shorthand properties only",
        property,
        sourceFile,
      );
    }
    if (!validRecordFieldName(name) || names.has(name)) {
      refuse(
        `${diagnosticPrefix}.record-literal-shape-unsupported`,
        `sealed source record has duplicate or reserved field ${name}`,
        property,
        sourceFile,
      );
    }
    graphs.push(verifyExpression(value, bindings, currentFunction));
    fields.push({ name, type_name: primitiveResolvedType(value, `record field ${name}`) });
    names.add(name);
  }
  const canonical = canonicalFields(fields);
  if (expectedFields && !fieldsEqual(expectedFields, canonical)) {
    refuse(
      `${diagnosticPrefix}.record-shape-mismatch`,
      "source record literal does not exactly match its declared record shape",
      literal,
      sourceFile,
    );
  }
  return {
    descriptor: { kind: "record", fields: canonical, provenance: "source-literal" },
    graph: sequenceGraph(graphs),
  };
}

function verifyConstRecord(declaration, bindings, currentFunction) {
  const initializer = objectLiteralInitializer(declaration.initializer);
  if (!initializer) {
    return null;
  }
  let expected = null;
  if (declaration.type) {
    const descriptor = recordType(declaration.type, `local ${declaration.name.text}`);
    if (!descriptor) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `local ${declaration.name.text} object annotation is not an exact sealed record type`,
        declaration.type,
        sourceFile,
      );
    }
    expected = descriptor.fields;
  }
  if (initializer.satisfies) {
    const descriptor = recordType(initializer.satisfies, `local ${declaration.name.text} satisfies`);
    if (!descriptor || (expected && !fieldsEqual(expected, descriptor.fields))) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `local ${declaration.name.text} satisfies target must be the same exact sealed record type`,
        initializer.satisfies,
        sourceFile,
      );
    }
    expected = descriptor.fields;
  }
  return verifyRecordLiteral(initializer.literal, expected, bindings, currentFunction);
}

function verifyCallArgument(argument, formal, bindings, currentFunction) {
  if (formal.kind === "callback") {
    if (!ts.isIdentifier(argument)) {
      refuse(
        `${diagnosticPrefix}.callback-argument-provenance`,
        "callback arguments must name one compiler-resolved top-level function in this source module",
        argument,
        sourceFile,
      );
    }
    const symbol = checker.getSymbolAtLocation(argument);
    const callback = symbol ? functionSymbols.get(symbol) : undefined;
    const signature = callback ? functionSignatures.get(callback) : undefined;
    if (
      !callback ||
      !signature ||
      signature.execution !== "synchronous" ||
      signature.parameters.some(parameter => parameter.descriptor.kind !== "primitive")
    ) {
      refuse(
        `${diagnosticPrefix}.callback-argument-provenance`,
        "callback arguments must resolve to a non-higher-order top-level source function with a primitive signature",
        argument,
        sourceFile,
      );
    }
    const actual = {
      kind: "source-callback",
      function: callback,
      parameter_types: signature.parameters.map(parameter => parameter.descriptor.primitive),
      return_type: signature.returnType,
    };
    if (!descriptorsCompatible(formal, actual)) {
      refuse(
        `${diagnosticPrefix}.callback-argument-type`,
        "source callback signature does not exactly match the callback parameter",
        argument,
        sourceFile,
      );
    }
    callEdges.get(currentFunction).push({ callee: callback, node: argument });
    return { descriptor: actual, graph: fallthroughGraph() };
  }
  if (formal.kind === "record") {
    const initializer = objectLiteralInitializer(argument);
    if (initializer) {
      const verified = verifyRecordLiteral(
        initializer.literal,
        formal.fields,
        bindings,
        currentFunction,
      );
      return verified;
    }
    if (ts.isIdentifier(argument)) {
      const binding = bindings.get(argument.text);
      if (
        binding &&
        binding.kind === "record" &&
        binding.provenance === "source-literal" &&
        fieldsEqual(formal.fields, binding.fields)
      ) {
        return { descriptor: binding, graph: fallthroughGraph() };
      }
    }
    refuse(
      `${diagnosticPrefix}.record-argument-provenance`,
      "record parameters accept only exact source-owned object literals or const locals derived from them",
      argument,
      sourceFile,
    );
  }
  const graph = verifyExpression(argument, bindings, currentFunction, "call-argument");
  let actual;
  if (ts.isIdentifier(argument)) {
    actual = bindings.get(argument.text);
  }
  if (!actual || actual.kind !== formal.kind) {
    actual = { kind: "primitive", primitive: primitiveResolvedType(argument, "call argument") };
  }
  if (!descriptorsCompatible(formal, actual)) {
    refuse(
      `${diagnosticPrefix}.call-argument-type`,
      "call argument does not exactly match the verified source function parameter",
      argument,
      sourceFile,
    );
  }
  return { descriptor: actual, graph };
}

function verifyConstCollection(declaration, bindings, currentFunction) {
  const arrayInitializer = arrayLiteralInitializer(declaration.initializer);
  if (!arrayInitializer) {
    return null;
  }
  const { literal, assertedConst } = arrayInitializer;
  const annotatedDescriptor = declaration.type
    ? readonlyCollectionType(declaration.type, `local ${declaration.name.text}`)
    : null;
  if (declaration.type && !annotatedDescriptor) {
    refuse(
      `${diagnosticPrefix}.collection-type-unsupported`,
      `local ${declaration.name.text} collection annotation must be readonly`,
      declaration.type,
      sourceFile,
    );
  }
  if (literal.elements.length === 0) {
    if (annotatedDescriptor) {
      return { descriptor: annotatedDescriptor, graph: fallthroughGraph() };
    }
    if (assertedConst) {
      return {
        descriptor: { kind: "collection", collection: "tuple", elements: [] },
        graph: fallthroughGraph(),
      };
    }
    refuse(
      `${diagnosticPrefix}.collection-empty-unsupported`,
      "an unannotated empty collection literal has no primitive element type",
      literal,
      sourceFile,
    );
  }
  const elementTypes = [];
  const elementGraphs = [];
  for (const element of literal.elements) {
    if (ts.isSpreadElement(element) || ts.isOmittedExpression(element)) {
      refuse(
        `${diagnosticPrefix}.collection-literal-shape`,
        "collection literals do not permit spread elements or holes",
        element,
        sourceFile,
      );
    }
    elementGraphs.push(verifyExpression(element, bindings, currentFunction));
    elementTypes.push(primitiveResolvedType(element, "collection literal element"));
  }
  let descriptor;
  if (annotatedDescriptor) {
    descriptor = annotatedDescriptor;
  } else if (assertedConst) {
    descriptor = { kind: "collection", collection: "tuple", elements: elementTypes };
  } else {
    const first = elementTypes[0];
    if (elementTypes.some(element => element !== first)) {
      refuse(
        `${diagnosticPrefix}.collection-element-type-unsupported`,
        "an inferred collection literal must be homogeneous; use a fixed readonly tuple for heterogeneous primitives",
        literal,
        sourceFile,
      );
    }
    descriptor = { kind: "collection", collection: "array", elements: [first] };
  }
  return { descriptor, graph: sequenceGraph(elementGraphs) };
}

function terminalStatement(statement) {
  if (ts.isReturnStatement(statement) || ts.isThrowStatement(statement)) {
    return true;
  }
  if (ts.isBlock(statement)) {
    return terminalStatementList(statement.statements);
  }
  if (ts.isIfStatement(statement)) {
    return Boolean(statement.elseStatement) &&
      terminalStatement(statement.thenStatement) &&
      terminalStatement(statement.elseStatement);
  }
  if (ts.isTryStatement(statement)) {
    const protectedTerminal = terminalStatementList(statement.tryBlock.statements) &&
      (!statement.catchClause || terminalStatementList(statement.catchClause.block.statements));
    return protectedTerminal ||
      Boolean(statement.finallyBlock && terminalStatementList(statement.finallyBlock.statements));
  }
  if (ts.isSwitchStatement(statement)) {
    const clauses = Array.from(statement.caseBlock.clauses);
    return clauses.length >= 2 &&
      clauses[clauses.length - 1].kind === ts.SyntaxKind.DefaultClause &&
      clauses.filter(clause => clause.kind === ts.SyntaxKind.DefaultClause).length === 1 &&
      clauses.some(clause => clause.kind === ts.SyntaxKind.CaseClause) &&
      clauses.every(clause => terminalStatementList(clause.statements));
  }
  return false;
}

function terminalStatementList(statements) {
  return statements.length > 0 && terminalStatement(statements[statements.length - 1]);
}

function switchCaseLabel(expression) {
  if (ts.isStringLiteral(expression)) {
    return { type_name: "string", value: expression.text };
  }
  if (expression.kind === ts.SyntaxKind.TrueKeyword) {
    return { type_name: "boolean", value: true };
  }
  if (expression.kind === ts.SyntaxKind.FalseKeyword) {
    return { type_name: "boolean", value: false };
  }
  let numeric = null;
  if (ts.isNumericLiteral(expression)) {
    numeric = Number(expression.text);
  } else if (
    ts.isPrefixUnaryExpression(expression) &&
    [ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken].includes(expression.operator) &&
    ts.isNumericLiteral(expression.operand)
  ) {
    const magnitude = Number(expression.operand.text);
    numeric = expression.operator === ts.SyntaxKind.MinusToken ? -magnitude : magnitude;
  }
  if (numeric !== null && Number.isFinite(numeric)) {
    return { type_name: "number", value: Object.is(numeric, -0) ? 0 : numeric };
  }
  refuse(
    `${diagnosticPrefix}.switch-label-unsupported`,
    "switch case labels must be finite primitive literals",
    expression,
    sourceFile,
  );
}

function verifyTerminalSwitch(statement, bindings, returnType, currentFunction) {
  const discriminantType = primitiveResolvedType(statement.expression, "switch discriminant");
  const discriminantGraph = verifyExpression(statement.expression, bindings, currentFunction);
  const clauses = Array.from(statement.caseBlock.clauses);
  const defaults = clauses.filter(clause => ts.isDefaultClause(clause));
  const cases = clauses.filter(clause => ts.isCaseClause(clause));
  if (
    cases.length === 0 ||
    defaults.length !== 1 ||
    !ts.isDefaultClause(clauses[clauses.length - 1])
  ) {
    refuse(
      `${diagnosticPrefix}.switch-exhaustiveness-unsupported`,
      "terminal switch requires at least one case and exactly one final default",
      statement,
      sourceFile,
    );
  }
  const labels = new Set();
  const verifiedCases = [];
  let defaultBody = null;
  for (const clause of clauses) {
    if (!terminalStatementList(clause.statements)) {
      refuse(
        `${diagnosticPrefix}.switch-arm-nonterminal`,
        "every switch arm must terminate without fallthrough or break",
        clause,
        sourceFile,
      );
    }
    const body = verifyStatementList(
      clause.statements,
      new Map(bindings),
      returnType,
      currentFunction,
    );
    if (ts.isDefaultClause(clause)) {
      defaultBody = body;
      continue;
    }
    const label = switchCaseLabel(clause.expression);
    if (label.type_name !== discriminantType) {
      refuse(
        `${diagnosticPrefix}.switch-label-type`,
        `switch case ${JSON.stringify(label.value)} does not match ${discriminantType}`,
        clause.expression,
        sourceFile,
      );
    }
    const labelKey = `${label.type_name}:${JSON.stringify(label.value)}`;
    if (labels.has(labelKey)) {
      refuse(
        `${diagnosticPrefix}.switch-label-duplicate`,
        `switch repeats case label ${JSON.stringify(label.value)}`,
        clause.expression,
        sourceFile,
      );
    }
    labels.add(labelKey);
    verifiedCases.push({ label, body });
  }
  return {
    kind: "terminal-switch",
    discriminant: discriminantGraph,
    discriminant_type: discriminantType,
    cases: verifiedCases,
    default_body: defaultBody,
  };
}

function verifyStatement(statement, bindings, returnType, currentFunction) {
  if (ts.isEmptyStatement(statement)) {
    return fallthroughGraph();
  }
  if (ts.isBlock(statement)) {
    return verifyStatementList(statement.statements, new Map(bindings), returnType, currentFunction);
  }
  if (ts.isReturnStatement(statement)) {
    let expressionGraph = fallthroughGraph();
    if (statement.expression) {
      const directExpression = unwrapParentheses(statement.expression);
      if (ts.isCallExpression(directExpression)) {
        const calleeSymbol = ts.isIdentifier(directExpression.expression)
          ? checker.getSymbolAtLocation(directExpression.expression)
          : ts.isPropertyAccessExpression(directExpression.expression)
            ? checker.getSymbolAtLocation(directExpression.expression.name)
            : undefined;
        const callee = calleeSymbol ? functionSymbols.get(calleeSymbol) : undefined;
        const calleeSignature = callee ? functionSignatures.get(callee) : undefined;
        const currentSignature = functionSignatures.get(currentFunction);
        if (
          currentSignature &&
          currentSignature.execution === "asynchronous" &&
          calleeSignature &&
          calleeSignature.execution === "asynchronous"
        ) {
          if (calleeSignature.returnType !== returnType) {
            refuse(
              `${diagnosticPrefix}.promise-adoption-type`,
              `async return adopts ${calleeSignature.returnType}, expected ${returnType}`,
              statement.expression,
              sourceFile,
            );
          }
          return verifyCallExpression(
            directExpression,
            bindings,
            currentFunction,
            "promise-adopt",
          );
        }
      }
    }
    if (returnType === "void") {
      if (statement.expression) {
        refuse(
          `${diagnosticPrefix}.return-value-unexpected`,
          "void function returns a value",
          statement,
          sourceFile,
        );
      }
    } else {
      if (!statement.expression) {
        refuse(
          `${diagnosticPrefix}.return-value-missing`,
          `function returning ${returnType} has an empty return`,
          statement,
          sourceFile,
        );
      }
      expressionGraph = verifyExpression(statement.expression, bindings, currentFunction);
    }
    return sequenceGraph([
      expressionGraph,
      { kind: "return", type_name: returnType },
    ]);
  }
  if (ts.isThrowStatement(statement)) {
    const expressionGraph = verifyExpression(statement.expression, bindings, currentFunction);
    if (graphContainsCall(expressionGraph)) {
      refuse(
        `${diagnosticPrefix}.throw-expression-effect-unsupported`,
        "thrown values must be computed without any function call",
        statement.expression,
        sourceFile,
      );
    }
    const thrownType = primitiveResolvedType(statement.expression, "thrown value");
    return sequenceGraph([
      expressionGraph,
      {
        kind: "raise",
        exception_type: `ecmascript.throw.${thrownType}`,
        ...sourceLocation(statement),
      },
    ]);
  }
  if (ts.isIfStatement(statement)) {
    const conditionGraph = verifyExpression(statement.expression, bindings, currentFunction);
    const thenGraph = verifyStatement(statement.thenStatement, new Map(bindings), returnType, currentFunction);
    const elseGraph = statement.elseStatement
      ? verifyStatement(statement.elseStatement, new Map(bindings), returnType, currentFunction)
      : fallthroughGraph();
    return sequenceGraph([conditionGraph, branchGraph([thenGraph, elseGraph])]);
  }
  if (ts.isTryStatement(statement)) {
    if (!statement.catchClause && !statement.finallyBlock) {
      refuse(
        `${diagnosticPrefix}.try-shape-unsupported`,
        "a try statement requires a catch clause, a finally block, or both",
        statement,
        sourceFile,
      );
    }
    const tryGraph = verifyStatementList(
      statement.tryBlock.statements,
      new Map(bindings),
      returnType,
      currentFunction,
    );
    let protectedGraph = tryGraph;
    if (statement.catchClause) {
      const catchBindings = new Map(bindings);
      const declaration = statement.catchClause.variableDeclaration;
      if (declaration) {
        if (
          !ts.isIdentifier(declaration.name) ||
          declaration.initializer ||
          declaration.type
        ) {
          refuse(
            `${diagnosticPrefix}.catch-binding-shape-unsupported`,
            "catch binding must be one untyped identifier",
            declaration,
            sourceFile,
          );
        }
        catchBindings.set(declaration.name.text, { kind: "opaque-catch" });
      }
      const catchGraph = verifyStatementList(
        statement.catchClause.block.statements,
        catchBindings,
        returnType,
        currentFunction,
      );
      protectedGraph = { kind: "try-catch", try_body: tryGraph, catch_body: catchGraph };
    }
    if (!statement.finallyBlock) {
      return protectedGraph;
    }
    const finallyGraph = verifyStatementList(
      statement.finallyBlock.statements,
      new Map(bindings),
      returnType,
      currentFunction,
    );
    return { kind: "try-finally", body: protectedGraph, finally_body: finallyGraph };
  }
  if (ts.isSwitchStatement(statement)) {
    return verifyTerminalSwitch(statement, bindings, returnType, currentFunction);
  }
  if (ts.isExpressionStatement(statement) && ts.isCallExpression(statement.expression)) {
    return verifyExpression(statement.expression, bindings, currentFunction);
  }
  refuse(
    `${diagnosticPrefix}.statement-unsupported`,
    `unsupported statement ${ts.SyntaxKind[statement.kind]}`,
    statement,
    sourceFile,
  );
}

function verifyConstInstance(declaration, bindings, currentFunction) {
  const initializer = unwrapParentheses(declaration.initializer);
  if (!ts.isNewExpression(initializer)) {
    return null;
  }
  if (
    !ts.isIdentifier(initializer.expression) ||
    initializer.typeArguments ||
    !initializer.arguments
  ) {
    refuse(
      `${diagnosticPrefix}.class-construction-unsupported`,
      "class construction requires one direct nongeneric source-class constructor call",
      initializer,
      sourceFile,
    );
  }
  const symbol = checker.getSymbolAtLocation(initializer.expression);
  const classData = symbol ? classSymbols.get(symbol) : undefined;
  if (!classData) {
    refuse(
      `${diagnosticPrefix}.expression-unsupported`,
      "constructed class must resolve to one closed source-owned class in this module",
      initializer.expression,
      sourceFile,
    );
  }
  if (declaration.type) {
    const declared = checker.getTypeFromTypeNode(declaration.type);
    if (declared.symbol !== symbol || declared.aliasSymbol) {
      refuse(
        `${diagnosticPrefix}.class-construction-type-unsupported`,
        `local ${declaration.name.text} annotation must name the exact constructed class ${classData.name}`,
        declaration.type,
        sourceFile,
      );
    }
  }
  const constructorName = classMethodName(classData.name, "constructor");
  const signature = functionSignatures.get(constructorName);
  if (!signature || initializer.arguments.length !== signature.parameters.length) {
    refuse(
      `${diagnosticPrefix}.class-constructor-arity`,
      `constructor ${constructorName} must receive exactly ${signature ? signature.parameters.length : 0} primitive arguments`,
      initializer,
      sourceFile,
    );
  }
  const graphs = [];
  const argumentDescriptors = [];
  for (let index = 0; index < initializer.arguments.length; index += 1) {
    const argument = initializer.arguments[index];
    if (ts.isSpreadElement(argument)) {
      refuse(
        `${diagnosticPrefix}.class-constructor-spread-unsupported`,
        "closed source constructors do not accept spread arguments",
        argument,
        sourceFile,
      );
    }
    const verified = verifyCallArgument(
      argument,
      signature.parameters[index].descriptor,
      bindings,
      currentFunction,
    );
    graphs.push(verified.graph);
    argumentDescriptors.push(actualDescriptor(verified.descriptor));
  }
  callEdges.get(currentFunction).push({ callee: constructorName, node: initializer });
  graphs.push({
    kind: "call",
    callee: constructorName,
    arguments: argumentDescriptors,
    ...sourceLocation(initializer),
  });
  return {
    descriptor: { kind: "instance", class_name: classData.name },
    graph: sequenceGraph(graphs),
  };
}

function verifyStatementList(statements, bindings, returnType, currentFunction) {
  const graphs = [];
  for (let statementIndex = 0; statementIndex < statements.length; statementIndex += 1) {
    const statement = statements[statementIndex];
    if (ts.isSwitchStatement(statement) && statementIndex + 1 !== statements.length) {
      refuse(
        `${diagnosticPrefix}.switch-continuation-unsupported`,
        "a terminal switch must be the final statement in its lexical block",
        statements[statementIndex + 1],
        sourceFile,
      );
    }
    if (ts.isVariableStatement(statement)) {
      if ((statement.declarationList.flags & ts.NodeFlags.Const) === 0) {
        refuse(
          `${diagnosticPrefix}.mutable-local-unsupported`,
          "closed control flow permits only const local declarations",
          statement,
          sourceFile,
        );
      }
      for (const declaration of statement.declarationList.declarations) {
        if (!ts.isIdentifier(declaration.name) || !declaration.initializer) {
          refuse(
            `${diagnosticPrefix}.local-shape-unsupported`,
            "const locals require one identifier and an initializer",
            declaration,
            sourceFile,
          );
        }
        const collection = verifyConstCollection(declaration, bindings, currentFunction);
        if (collection) {
          bindings.set(declaration.name.text, collection.descriptor);
          graphs.push(collection.graph);
        } else {
          const record = verifyConstRecord(declaration, bindings, currentFunction);
          if (record) {
            bindings.set(declaration.name.text, record.descriptor);
            graphs.push(record.graph);
          } else {
            const instance = verifyConstInstance(declaration, bindings, currentFunction);
            if (instance) {
              bindings.set(declaration.name.text, instance.descriptor);
              graphs.push(instance.graph);
            } else {
              graphs.push(verifyExpression(declaration.initializer, bindings, currentFunction));
              const primitive = primitiveResolvedType(declaration.name, `local ${declaration.name.text}`);
              bindings.set(declaration.name.text, { kind: "primitive", primitive });
            }
          }
        }
      }
      continue;
    }
    graphs.push(verifyStatement(statement, bindings, returnType, currentFunction));
  }
  return sequenceGraph(graphs);
}

function hasJSDocTag(node, name) {
  return ts.getJSDocTags(node).some(tag => tag.tagName.text === name);
}

function primitiveMemberType(node, role) {
  const annotation = isJavaScript ? ts.getJSDocType(node) : node.type;
  const typeName = primitiveType(annotation, role);
  if (typeName === "void") {
    refuse(
      `${diagnosticPrefix}.class-field-type-unsupported`,
      `${role} must be number, boolean, or string`,
      node,
      sourceFile,
    );
  }
  return typeName;
}

function classMethodName(className, memberName) {
  return `${className}.${memberName}`;
}

function registerClass(statement) {
  const modifiers = statement.modifiers ? Array.from(statement.modifiers) : [];
  if (
    !statement.name ||
    statement.typeParameters ||
    statement.heritageClauses ||
    modifiers.length !== 0 ||
    classByName.has(statement.name ? statement.name.text : "")
  ) {
    refuse(
      `${diagnosticPrefix}.class-shape-unsupported`,
      "closed source classes must be uniquely named, unexported, nongeneric, and have no inheritance",
      statement,
      sourceFile,
    );
  }
  const className = statement.name.text;
  const symbol = checker.getSymbolAtLocation(statement.name);
  if (!symbol) {
    refuse(
      `${diagnosticPrefix}.class-symbol-unresolved`,
      `compiler did not resolve class ${className}`,
      statement.name,
      sourceFile,
    );
  }
  const data = {
    name: className,
    node: statement,
    fields: [],
    fieldSymbols: new Map(),
    constructor: null,
    methods: [],
  };
  const fieldNames = new Set();
  const methodNames = new Set();
  for (const member of statement.members) {
    if (ts.isPropertyDeclaration(member)) {
      const memberModifiers = member.modifiers ? Array.from(member.modifiers) : [];
      const readonly = isJavaScript
        ? hasJSDocTag(member, "readonly") && memberModifiers.length === 0
        : memberModifiers.length === 1 && memberModifiers[0].kind === ts.SyntaxKind.ReadonlyKeyword;
      if (
        !ts.isIdentifier(member.name) ||
        member.questionToken ||
        member.exclamationToken ||
        member.initializer ||
        !readonly ||
        !validRecordFieldName(ts.isIdentifier(member.name) ? member.name.text : "") ||
        fieldNames.has(ts.isIdentifier(member.name) ? member.name.text : "")
      ) {
        refuse(
          `${diagnosticPrefix}.class-field-unsupported`,
          `class ${className} fields must be unique required readonly primitive declarations without initializers`,
          member,
          sourceFile,
        );
      }
      const fieldName = member.name.text;
      const typeName = primitiveMemberType(member, `class ${className} field ${fieldName}`);
      const fieldSymbol = checker.getSymbolAtLocation(member.name);
      if (!fieldSymbol) {
        refuse(
          `${diagnosticPrefix}.class-field-symbol-unresolved`,
          `compiler did not resolve class field ${className}.${fieldName}`,
          member.name,
          sourceFile,
        );
      }
      const field = { name: fieldName, type_name: typeName };
      data.fields.push(field);
      data.fieldSymbols.set(fieldSymbol, field);
      classFields.set(fieldSymbol, { class_name: className, field });
      fieldNames.add(fieldName);
      continue;
    }
    if (ts.isConstructorDeclaration(member)) {
      if (
        data.constructor ||
        !member.body ||
        member.typeParameters ||
        (member.modifiers && member.modifiers.length !== 0)
      ) {
        refuse(
          `${diagnosticPrefix}.class-constructor-unsupported`,
          `class ${className} must have exactly one concrete nongeneric constructor`,
          member,
          sourceFile,
        );
      }
      data.constructor = member;
      continue;
    }
    if (ts.isMethodDeclaration(member)) {
      const memberModifiers = member.modifiers ? Array.from(member.modifiers) : [];
      if (
        !ts.isIdentifier(member.name) ||
        !member.body ||
        member.typeParameters ||
        member.questionToken ||
        member.asteriskToken ||
        memberModifiers.some(modifier => modifier.kind !== ts.SyntaxKind.AsyncKeyword) ||
        methodNames.has(ts.isIdentifier(member.name) ? member.name.text : "")
      ) {
        refuse(
          `${diagnosticPrefix}.class-method-unsupported`,
          `class ${className} methods must be unique, concrete, direct, nongeneric methods with only optional async syntax`,
          member,
          sourceFile,
        );
      }
      const methodName = member.name.text;
      const canonical = classMethodName(className, methodName);
      const methodSymbol = checker.getSymbolAtLocation(member.name);
      if (!methodSymbol) {
        refuse(
          `${diagnosticPrefix}.class-method-symbol-unresolved`,
          `compiler did not resolve method ${canonical}`,
          member.name,
          sourceFile,
        );
      }
      data.methods.push(canonical);
      classMemberDeclarations.push({ node: member, canonical, class_data: data, kind: "method" });
      classMembers.set(canonical, { class_name: className, kind: "method" });
      functionSymbols.set(methodSymbol, canonical);
      callEdges.set(canonical, []);
      methodNames.add(methodName);
      continue;
    }
    refuse(
      `${diagnosticPrefix}.class-member-unsupported`,
      `class ${className} permits only readonly primitive fields, one constructor, and direct methods`,
      member,
      sourceFile,
    );
  }
  if (data.fields.length === 0 || !data.constructor) {
    refuse(
      `${diagnosticPrefix}.class-shape-unsupported`,
      `class ${className} requires at least one readonly primitive field and exactly one constructor`,
      statement,
      sourceFile,
    );
  }
  const constructorName = classMethodName(className, "constructor");
  classMemberDeclarations.push({
    node: data.constructor,
    canonical: constructorName,
    class_data: data,
    kind: "constructor",
  });
  classMembers.set(constructorName, { class_name: className, kind: "constructor" });
  callEdges.set(constructorName, []);
  data.fields = canonicalFields(data.fields);
  data.methods.sort();
  classSymbols.set(symbol, data);
  classByName.set(className, data);
  classDeclarations.push(statement);
  classes.push({
    name: className,
    fields: data.fields,
    constructor: constructorName,
    methods: data.methods,
  });
}

for (const statement of sourceFile.statements) {
  if (ts.isClassDeclaration(statement)) {
    registerClass(statement);
  }
}

for (const statement of sourceFile.statements) {
  if (ts.isEmptyStatement(statement)) {
    continue;
  }
  if (ts.isClassDeclaration(statement)) {
    continue;
  }
  if (!isJavaScript && ts.isInterfaceDeclaration(statement)) {
    const modifiers = statement.modifiers ? Array.from(statement.modifiers, item => item.kind) : [];
    if (
      statement.typeParameters ||
      statement.heritageClauses ||
      modifiers.some(kind => kind !== ts.SyntaxKind.ExportKeyword) ||
      declaredRecordTypes.has(statement.name.text)
    ) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `interface ${statement.name.text} must be one unextended, nongeneric exact declaration`,
        statement,
        sourceFile,
      );
    }
    declaredRecordTypes.set(
      statement.name.text,
      recordFieldsFromMembers(statement.members, `interface ${statement.name.text}`),
    );
    continue;
  }
  if (!isJavaScript && ts.isTypeAliasDeclaration(statement)) {
    const modifiers = statement.modifiers ? Array.from(statement.modifiers, item => item.kind) : [];
    if (
      statement.typeParameters ||
      !ts.isTypeLiteralNode(statement.type) ||
      modifiers.some(kind => kind !== ts.SyntaxKind.ExportKeyword) ||
      declaredRecordTypes.has(statement.name.text)
    ) {
      refuse(
        `${diagnosticPrefix}.record-type-unsupported`,
        `type alias ${statement.name.text} must be one nongeneric exact readonly record literal`,
        statement,
        sourceFile,
      );
    }
    declaredRecordTypes.set(
      statement.name.text,
      recordFieldsFromMembers(statement.type.members, `type alias ${statement.name.text}`),
    );
    continue;
  }
  if (!ts.isFunctionDeclaration(statement) || !statement.name || !statement.body) {
    refuse(
      `${diagnosticPrefix}.top-level-unsupported`,
      `unsupported top-level declaration ${ts.SyntaxKind[statement.kind]}`,
      statement,
      sourceFile,
    );
  }
  if (functionNames.has(statement.name.text)) {
    refuse(`${diagnosticPrefix}.overload-unsupported`, `function ${statement.name.text} is declared more than once`, statement, sourceFile);
  }
  const symbol = checker.getSymbolAtLocation(statement.name);
  if (!symbol) {
    refuse(
      `${diagnosticPrefix}.function-symbol-unresolved`,
      `compiler did not resolve function ${statement.name.text}`,
      statement.name,
      sourceFile,
    );
  }
  functionNames.add(statement.name.text);
  functionDeclarations.push(statement);
  functionSymbols.set(symbol, statement.name.text);
  callEdges.set(statement.name.text, []);
}

for (const statement of functionDeclarations) {
  if (statement.asteriskToken || statement.typeParameters || statement.questionToken) {
    refuse(`${diagnosticPrefix}.function-shape`, `function ${statement.name.text} has unsupported generic, generator, or optional syntax`, statement, sourceFile);
  }
  const modifiers = statement.modifiers ? Array.from(statement.modifiers, item => item.kind) : [];
  if (modifiers.some(kind => ![
    ts.SyntaxKind.ExportKeyword,
    ts.SyntaxKind.DefaultKeyword,
    ts.SyntaxKind.AsyncKeyword,
  ].includes(kind))) {
    refuse(`${diagnosticPrefix}.function-modifier`, `function ${statement.name.text} has unsupported modifiers`, statement, sourceFile);
  }
  const exported = modifiers.includes(ts.SyntaxKind.ExportKeyword) ||
    modifiers.includes(ts.SyntaxKind.DefaultKeyword);
  const execution = modifiers.includes(ts.SyntaxKind.AsyncKeyword)
    ? "asynchronous"
    : "synchronous";
  const parameters = [];
  for (const parameter of statement.parameters) {
    if (!ts.isIdentifier(parameter.name) || parameter.dotDotDotToken || parameter.questionToken || parameter.initializer) {
      refuse(`${diagnosticPrefix}.parameter-shape`, `function ${statement.name.text} has an unsupported parameter`, parameter, sourceFile);
    }
    const parameterAnnotation = isJavaScript ? ts.getJSDocType(parameter) : parameter.type;
    const parameterDescriptor = parameterType(parameterAnnotation, `parameter ${parameter.name.text}`);
    parameters.push({ name: parameter.name.text, descriptor: parameterDescriptor });
  }
  const returnAnnotation = isJavaScript ? ts.getJSDocReturnType(statement) : statement.type;
  const returnType = execution === "asynchronous"
    ? asyncResultType(returnAnnotation, `async function ${statement.name.text} return`)
    : primitiveType(returnAnnotation, `function ${statement.name.text} return`);
  if (parameters.some(parameter => parameter.descriptor.kind === "callback")) {
    const requestedRoot = requestedSymbols.length === 0 || requestedSymbols.includes(statement.name.text);
    if (exported || requestedRoot) {
      refuse(
        `${diagnosticPrefix}.callback-boundary-unsupported`,
        `callback parameters are limited to private, unrequested helpers supplied by verified source call sites`,
        statement,
        sourceFile,
      );
    }
  }
  if (parameters.some(parameter => parameter.descriptor.kind === "record")) {
    const requestedRoot = requestedSymbols.length === 0 || requestedSymbols.includes(statement.name.text);
    if (!ts.isExternalModule(sourceFile) || exported || requestedRoot) {
      refuse(
        `${diagnosticPrefix}.record-boundary-unsupported`,
        `record parameters are limited to nonexported, nonrequested helpers in a source module`,
        statement,
        sourceFile,
      );
    }
  }
  functionSignatures.set(statement.name.text, {
    name: statement.name.text,
    exported,
    execution,
    parameters,
    returnType,
  });
}

for (const entry of classMemberDeclarations) {
  const statement = entry.node;
  const parameters = [];
  for (const parameter of statement.parameters) {
    if (
      !ts.isIdentifier(parameter.name) ||
      parameter.dotDotDotToken ||
      parameter.questionToken ||
      parameter.initializer ||
      (parameter.modifiers && parameter.modifiers.length !== 0)
    ) {
      refuse(
        `${diagnosticPrefix}.class-parameter-unsupported`,
        `${entry.canonical} parameters must be required named primitives without parameter properties, defaults, optional, or rest syntax`,
        parameter,
        sourceFile,
      );
    }
    const annotation = isJavaScript ? ts.getJSDocType(parameter) : parameter.type;
    const descriptor = parameterType(annotation, `parameter ${entry.canonical}.${parameter.name.text}`);
    if (descriptor.kind !== "primitive") {
      refuse(
        `${diagnosticPrefix}.class-parameter-type-unsupported`,
        `${entry.canonical} parameters must be primitive`,
        parameter,
        sourceFile,
      );
    }
    parameters.push({ name: parameter.name.text, descriptor });
  }
  const execution = entry.kind === "method" && statement.modifiers &&
    Array.from(statement.modifiers).some(modifier => modifier.kind === ts.SyntaxKind.AsyncKeyword)
    ? "asynchronous"
    : "synchronous";
  let returnType = "void";
  if (entry.kind === "method") {
    const annotation = isJavaScript ? ts.getJSDocReturnType(statement) : statement.type;
    returnType = execution === "asynchronous"
      ? asyncResultType(annotation, `async method ${entry.canonical} return`)
      : primitiveType(annotation, `method ${entry.canonical} return`);
  }
  functionSignatures.set(entry.canonical, {
    name: entry.canonical,
    exported: false,
    execution,
    parameters,
    returnType,
  });
}

for (const statement of functionDeclarations) {
  const signature = functionSignatures.get(statement.name.text);
  const parameters = new Map(
    signature.parameters.map(parameter => [parameter.name, parameter.descriptor]),
  );
  const outcomeGraph = verifyStatementList(
    statement.body.statements,
    parameters,
    signature.returnType,
    statement.name.text,
  );
  functions.push({
    name: statement.name.text,
    exported: signature.exported,
    execution: signature.execution,
    parameters: signature.parameters.map(parameter => ({
      name: parameter.name,
      descriptor: formalDescriptor(parameter.descriptor),
    })),
    return_type: signature.returnType,
    calls: [],
    outcome_graph: outcomeGraph,
  });
}

function verifyConstructorBody(entry, bindings) {
  const statements = Array.from(entry.node.body.statements);
  const assigned = new Set();
  const graphs = [];
  const fieldCount = entry.class_data.fields.length;
  if (statements.length < fieldCount) {
    refuse(
      `${diagnosticPrefix}.class-constructor-initialization-incomplete`,
      `constructor ${entry.canonical} must initialize every readonly field exactly once before other work`,
      entry.node,
      sourceFile,
    );
  }
  for (let index = 0; index < fieldCount; index += 1) {
    const statement = statements[index];
    const assignment = ts.isExpressionStatement(statement) &&
      ts.isBinaryExpression(statement.expression) &&
      statement.expression.operatorToken.kind === ts.SyntaxKind.EqualsToken
      ? statement.expression
      : null;
    if (
      !assignment ||
      !ts.isPropertyAccessExpression(assignment.left) ||
      assignment.left.questionDotToken ||
      assignment.left.expression.kind !== ts.SyntaxKind.ThisKeyword
    ) {
      refuse(
        `${diagnosticPrefix}.class-constructor-initialization-unsupported`,
        `constructor ${entry.canonical} must begin with direct this.field assignments`,
        statement,
        sourceFile,
      );
    }
    const fieldSymbol = checker.getSymbolAtLocation(assignment.left.name);
    const field = fieldSymbol ? entry.class_data.fieldSymbols.get(fieldSymbol) : undefined;
    if (!field || assigned.has(field.name)) {
      refuse(
        `${diagnosticPrefix}.class-constructor-initialization-unsupported`,
        `constructor ${entry.canonical} must initialize each declared field exactly once`,
        assignment.left,
        sourceFile,
      );
    }
    let readsThis = false;
    function findThis(node) {
      if (node.kind === ts.SyntaxKind.ThisKeyword) {
        readsThis = true;
        return;
      }
      ts.forEachChild(node, findThis);
    }
    findThis(assignment.right);
    if (readsThis) {
      refuse(
        `${diagnosticPrefix}.class-constructor-read-before-initialization`,
        `constructor ${entry.canonical} field initializers cannot read this before the complete immutable instance exists`,
        assignment.right,
        sourceFile,
      );
    }
    const graph = verifyExpression(assignment.right, bindings, entry.canonical);
    const actualType = primitiveResolvedType(
      assignment.right,
      `constructor value for ${entry.class_data.name}.${field.name}`,
    );
    if (actualType !== field.type_name) {
      refuse(
        `${diagnosticPrefix}.class-constructor-field-type`,
        `constructor value for ${entry.class_data.name}.${field.name} must be exactly ${field.type_name}`,
        assignment.right,
        sourceFile,
      );
    }
    assigned.add(field.name);
    graphs.push(graph);
  }
  graphs.push(verifyStatementList(
    statements.slice(fieldCount),
    bindings,
    "void",
    entry.canonical,
  ));
  return sequenceGraph(graphs);
}

for (const entry of classMemberDeclarations) {
  const signature = functionSignatures.get(entry.canonical);
  const parameters = new Map(
    signature.parameters.map(parameter => [parameter.name, parameter.descriptor]),
  );
  const outcomeGraph = entry.kind === "constructor"
    ? verifyConstructorBody(entry, parameters)
    : verifyStatementList(
      entry.node.body.statements,
      parameters,
      signature.returnType,
      entry.canonical,
    );
  functions.push({
    name: entry.canonical,
    exported: false,
    execution: signature.execution,
    parameters: signature.parameters.map(parameter => ({
      name: parameter.name,
      descriptor: formalDescriptor(parameter.descriptor),
    })),
    return_type: signature.returnType,
    calls: [],
    outcome_graph: outcomeGraph,
  });
}

if (functionNames.size === 0) {
  refuse(`${diagnosticPrefix}.empty-module`, `${sourceLanguage} module declares no supported functions`);
}
for (const requested of requestedSymbols) {
  if (!functionNames.has(requested)) {
    refuse(`${diagnosticPrefix}.symbol-missing`, `requested function ${requested} was not declared`);
  }
}

const visiting = new Set();
const visited = new Set();
function verifyAcyclicCalls(name, path) {
  if (visited.has(name)) {
    return;
  }
  visiting.add(name);
  for (const edge of callEdges.get(name)) {
    if (visiting.has(edge.callee)) {
      refuse(
        `${diagnosticPrefix}.call-cycle-unsupported`,
        `closed source call graph contains cycle ${[...path, name, edge.callee].join(" -> ")}`,
        edge.node,
        sourceFile,
      );
    }
    verifyAcyclicCalls(edge.callee, [...path, name]);
  }
  visiting.delete(name);
  visited.add(name);
}
for (const name of callEdges.keys()) {
  verifyAcyclicCalls(name, []);
}
for (const functionResult of functions) {
  functionResult.calls = Array.from(
    new Set(callEdges.get(functionResult.name).map(edge => edge.callee)),
  ).sort();
}
classes.sort((left, right) => left.name < right.name ? -1 : left.name > right.name ? 1 : 0);

process.stdout.write(JSON.stringify({
  status: "proved",
  schema: isJavaScript
    ? "maledictus-javascript-closed-verification/v8"
    : "maledictus-typescript-closed-verification/v8",
  compiler_version: ts.version,
  functions,
  classes,
}));
