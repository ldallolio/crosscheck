package bsh;

import java.io.StringReader;
import java.util.List;
import java.util.Vector;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.FunctionCall;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryArithmeticOperator;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.MinusIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.PostIncrementExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanOperator;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonOperator;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ProgramState;
import net.sf.metacad.revenge.state.ScopedState;
import net.sf.metacad.revenge.state.ScopedStateBase;
import net.sf.metacad.revenge.state.StateTransition;
import net.sf.metacad.revenge.statement.Assignment;
import net.sf.metacad.revenge.statement.Block;
import net.sf.metacad.revenge.statement.If;
import net.sf.metacad.revenge.statement.Lines;
import net.sf.metacad.revenge.statement.Return;
import net.sf.metacad.revenge.statement.While;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;
import net.sf.metacad.revenge.type.PrimitiveTypes;

public class JavaParser {

	/**
	 * Using this for holding variable and function definitions for early (during parsing) type resolving, not for the
	 * real state.
	 */
	CodeState nameResolutionState;

	private JavaParser() {
		nameResolutionState = new ProgramState();
		nameResolutionState.setCreatorDescription(new ToStringBuilder(this).toString());
	}

	private JavaParser(CodeState initialState) {
		// Avoid defining twice
		nameResolutionState = new ScopedState(initialState);
		nameResolutionState.setCreatorDescription(new ToStringBuilder(this).toString());
	}

	private StateTransition innerParse(String javaString) throws Exception {
		if (!javaString.trim().endsWith(";")) {
			javaString += ";";
		}
		Parser parser = new Parser(new StringReader(javaString));
		parser.setRetainComments(true);
		List<StateTransition> statements = new Vector<>();
		while (!parser.Line()) {
			SimpleNode node = parser.popNode();
			if (node != null) {
				statements.add(convertTransition(node));
			}

		}
		if (statements.size() == 1) {
			return statements.get(0);
		} else {
			return new Lines(statements);
		}
	}

	public static StateTransition parse(String javaString) throws Exception {
		JavaParser parser = new JavaParser();
		return parser.innerParse(javaString);
	}

	public static StateTransition parse(String javaString, CodeState initialState) throws Exception {
		JavaParser parser = new JavaParser(initialState);
		return parser.innerParse(javaString);
	}

	public static CodeState evaluate(String javaString, CodeState initialState) throws Exception {
		return JavaParser.parse(javaString, initialState).evaluate(initialState);
	}

	public static CodeState evaluate(String javaString) throws Exception {
		return JavaParser.parse(javaString).evaluate(new ProgramState());
	}

	public void run(String javaString) throws Exception {
		Interpreter i = new Interpreter();
		i.eval(javaString);
	}

	private StateTransition convertTransition(SimpleNode node) {

		if (node == null) {
			throw new IllegalArgumentException("Cannot conver node : [" + node + "]");
		}

		StateTransition stateTransition = null;

		if (node instanceof BSHFormalComment) {
			// not yet implemented
		}

		if (node instanceof BSHMethodDeclaration) {
			stateTransition = convertMethodDeclaration(node);
		}

		if (node instanceof BSHTypedVariableDeclaration) {
			stateTransition = convertVariableDeclaration((BSHTypedVariableDeclaration) node);
		}

		if (node instanceof BSHReturnStatement) {
			stateTransition = convertReturn((BSHReturnStatement) node);
		}

		if (node instanceof BSHAssignment) {
			stateTransition = convertAssignment((BSHAssignment) node);
		}

		if (node instanceof BSHUnaryExpression) {
			stateTransition = convertUnaryExpression((BSHUnaryExpression) node);
		}

		if (node instanceof BSHBinaryExpression) {
			stateTransition = convertBinaryExpression((BSHBinaryExpression) node);
		}

		if (node instanceof BSHPrimaryExpression) {
			stateTransition = convertPrimaryExpression((BSHPrimaryExpression) node);
		}

		if (node instanceof BSHIfStatement) {
			stateTransition = convertIf((BSHIfStatement) node);
		}

		if (node instanceof BSHWhileStatement) {
			stateTransition = convertWhile((BSHWhileStatement) node);
		}

		if (node instanceof BSHBlock) {
			stateTransition = convertBlock((BSHBlock) node);
		}

		if (stateTransition == null) {
			throw new UnsupportedOperationException("not yet implemented node : " + node + " class : " + node.getClass()
			+ " text : " + node.getText() + " num of children : " + node.jjtGetNumChildren());
		}

		return stateTransition;
	}

	private If convertIf(BSHIfStatement bshIf) {
		If if1 = new If(convertTransition(bshIf.getChild(0)), convertTransition(bshIf.getChild(1)));
		return if1;
	}

	private While convertWhile(BSHWhileStatement bshWhile) {
		While whileStatement = new While(convertTransition(bshWhile.getChild(0)),
				convertTransition(bshWhile.getChild(1)));
		return whileStatement;
	}

	private Block convertBlock(BSHBlock bshBlock) {
		List<StateTransition> blockStatements = new Vector<>();
		// Scoping for block handling
		nameResolutionState = new ScopedState(nameResolutionState);
		nameResolutionState.setCreatorDescription(new ToStringBuilder(this).toString());
		for (int i = 0; i < bshBlock.jjtGetNumChildren(); i++) {
			SimpleNode blockNode = bshBlock.getChild(i);
			blockStatements.add(convertTransition(blockNode));
		}
		nameResolutionState = ((ScopedStateBase) nameResolutionState).getWrappedState();
		Block block = new Block(blockStatements);
		return block;
	}

	private StateTransition convertMethodDeclaration(SimpleNode node) {
		// not yet implemented
		BSHMethodDeclaration methodDeclaration = (BSHMethodDeclaration) node;
		CodeType returnType = convertReturnType(methodDeclaration.getReturnTypeNode());
		// Scoping for parameter handling
		nameResolutionState = new ScopedState(nameResolutionState);
		nameResolutionState.setCreatorDescription(new ToStringBuilder(this).toString());
		List<VariableDefinition> parameters = convertParameters(methodDeclaration.paramsNode);
		Block functionBody = null;
		if (methodDeclaration.jjtGetNumChildren() == 3) {
			// first child should be return, second parameters, third should be
			// the block
			SimpleNode blockChild = methodDeclaration.getChild(2);
			functionBody = (Block) convertTransition(blockChild);
			blockChild.getClass();
		} else {
			throw new UnsupportedOperationException(
					"method node children number : [" + methodDeclaration.jjtGetNumChildren() + "] not yet parsed");
		}
		nameResolutionState = ((ScopedStateBase) nameResolutionState).getWrappedState();
		// Record here for variable type resolution
		FunctionDefinition functionDefinition = new FunctionDefinition(methodDeclaration.name, functionBody, parameters,
				returnType);
		nameResolutionState.defineFunction(functionDefinition);
		return functionDefinition;
	}

	private List<VariableDefinition> convertParameters(BSHFormalParameters paramsNode) {
		List<VariableDefinition> parameters = new Vector<>();
		for (int i = 0; i < paramsNode.jjtGetNumChildren(); i++) {
			BSHFormalParameter bshFormalParameter = (BSHFormalParameter) paramsNode.getChild(i);
			CodeType type = null;
			if (bshFormalParameter.jjtGetNumChildren() == 1) {
				SimpleNode paramChild = bshFormalParameter.getChild(0);
				type = convertType((BSHType) paramChild);
			} else {
				throw new UnsupportedOperationException("Parameter node children number : ["
						+ bshFormalParameter.jjtGetNumChildren() + "] not yet parsed");
			}
			VariableDefinition parameter = new VariableDefinition(bshFormalParameter.name, type);
			nameResolutionState.defineVariable(parameter);
			parameters.add(parameter);
		}
		return parameters;
	}

	private CodeType convertReturnType(BSHReturnType returnTypeNode) {
		CodeType codeType = null;
		if (returnTypeNode.isVoid) {
			codeType = PrimitiveTypes.VOID;
		} else if (returnTypeNode.getTypeNode() != null) {
			codeType = convertType(returnTypeNode.getTypeNode());
		} else {
			throw new UnsupportedOperationException(
					"return type : [" + returnTypeNode.getText() + "] not yet implemented");
		}
		return codeType;
	}

	@SuppressWarnings("unchecked")
	private CodeType convertType(BSHType typeNode) {
		CodeType codeType = null;
		if (typeNode.jjtGetNumChildren() == 1) {

			SimpleNode childTypeNode = typeNode.getChild(0);
			if (childTypeNode instanceof BSHPrimitiveType) {
				BSHPrimitiveType primitiveType = (BSHPrimitiveType) childTypeNode;
				if (primitiveType.getType().isAssignableFrom(Integer.TYPE)) {
					codeType = NumericType.INT;
				} else if (primitiveType.getType().isAssignableFrom(Boolean.TYPE)) {
					codeType = PrimitiveTypes.BOOLEAN;
				} else {
					throw new UnsupportedOperationException(
							"Type node class unknown : [" + primitiveType.getClass() + "] not yet parsed");
				}
			} else {
				throw new UnsupportedOperationException(
						"Type node unknown : [" + childTypeNode.getClass() + "] not yet parsed");
			}
		} else if (typeNode.jjtGetNumChildren() > 1) {
			throw new UnsupportedOperationException(
					"Type node multiple children : [" + typeNode.jjtGetNumChildren() + "] not yet parsed");
		}
		return codeType;
	}

	private StateTransition convertReturn(BSHReturnStatement returnStatement) {
		StateTransition returnExpression = null;
		if (returnStatement.jjtGetNumChildren() == 1) {
			SimpleNode bshReturnExpression = returnStatement.getChild(0);
			returnExpression = convertTransition(bshReturnExpression);
		} else {
			throw new UnsupportedOperationException("handling of return with number of children : "
					+ returnStatement.jjtGetNumChildren() + " not yet implemented");
		}
		StateTransition statement = new Return(returnExpression);
		return statement;
	}

	private StateTransition convertVariableDeclaration(BSHTypedVariableDeclaration typedVarDec) {
		if (typedVarDec.getDeclarators().length > 1) {
			throw new UnsupportedOperationException("inline multiple var declarations not yet parsed");
		}
		BSHVariableDeclarator varDec = typedVarDec.getDeclarators()[0];
		CodeExpression initialValue = null;
		if (varDec.jjtGetNumChildren() == 1) {
			initialValue = (CodeExpression) convertTransition(varDec.getChild(0));
		} else if (varDec.jjtGetNumChildren() > 1) {
			throw new UnsupportedOperationException(
					"variable declaration multiple children : [" + varDec.jjtGetNumChildren() + "] not yet parsed");
		} else {
			initialValue = MetaExpression.DEFINED_BUT_NOT_INITIALIZED_VARIABLE;
		}
		CodeType varType = null;
		if (typedVarDec.jjtGetNumChildren() == 2) {
			SimpleNode bshVariableType = typedVarDec.getChild(0);
			// second child should be the declarator
			if (bshVariableType instanceof BSHType) {
				varType = convertType((BSHType) bshVariableType);
			}
		} else {
			throw new UnsupportedOperationException("handling of typed variable with number of children : "
					+ typedVarDec.jjtGetNumChildren() + " not yet implemented");
		}
		VariableDefinition variableDefinition = new VariableDefinition(varDec.name, varType, initialValue);

		// Record here for variable type resolution
		nameResolutionState.defineVariable(variableDefinition);
		return variableDefinition;
	}

	private StateTransition convertAssignment(BSHAssignment assignmentStatement) {
		StateTransition statement;
		VariableReference variableReference = null;
		StateTransition variableValue = null;
		switch (assignmentStatement.operator) {
		case ParserConstants.ASSIGN:
			if (assignmentStatement.jjtGetNumChildren() == 2) {
				SimpleNode bshVariableReference = assignmentStatement.getChild(0);
				variableReference = (VariableReference) convertTransition(bshVariableReference);
				SimpleNode bshVariableValue = assignmentStatement.getChild(1);
				variableValue = convertTransition(bshVariableValue);
			} else {
				throw new UnsupportedOperationException("handling of assignment with number of children : "
						+ assignmentStatement.jjtGetNumChildren() + " not yet implemented");
			}
			break;

		default:
			throw new UnsupportedOperationException(
					"assignment operator : " + assignmentStatement.operator + " not yet handled");
		}
		statement = new Assignment(variableReference, variableValue);
		return statement;
	}

	private CodeExpression convertUnaryExpression(BSHUnaryExpression bshUnaryExpression) {
		CodeExpression expression = null;
		switch (bshUnaryExpression.kind) {
		case ParserConstants.PLUS:
			expression = (CodeExpression) convertTransition(bshUnaryExpression.getChild(0));
			break;
		case ParserConstants.MINUS:
			expression = MinusIntegerExpression
					.create((CodeExpression) convertTransition(bshUnaryExpression.getChild(0)));
			break;
		case ParserConstants.INCR:
			expression = new PostIncrementExpression(
					(ArithmeticVariableReference) convertTransition(bshUnaryExpression.getChild(0)));
			break;
		default:
			throw new UnsupportedOperationException("unary operator : " + bshUnaryExpression.kind + " not yet handled");
		}
		return expression;
	}

	private CodeExpression convertBinaryExpression(BSHBinaryExpression bshBinaryExpression) {
		CodeExpression expression = null;
		BinaryOperator operator = convertBinaryOperator(bshBinaryExpression.kind);
		if (operator instanceof BinaryArithmeticOperator) {
			expression = BinaryIntegerExpression.create((BinaryArithmeticOperator) operator,
					(CodeExpression) convertTransition(bshBinaryExpression.getChild(0)),
					(CodeExpression) convertTransition(bshBinaryExpression.getChild(1)));
		} else if (operator instanceof BinaryBooleanOperator) {
			expression = BinaryBooleanExpression.create((BinaryBooleanOperator) operator,
					(BooleanExpression) convertTransition(bshBinaryExpression.getChild(0)),
					(BooleanExpression) convertTransition(bshBinaryExpression.getChild(1)));
		} else if (operator instanceof ComparisonOperator) {
			expression = ComparisonExpression.create((ComparisonOperator) operator,
					(CodeExpression) convertTransition(bshBinaryExpression.getChild(0)),
					(CodeExpression) convertTransition(bshBinaryExpression.getChild(1)));
		} else {
			throw new UnsupportedOperationException("operator : " + operator.getClass() + " not yet handled");
		}
		return expression;
	}

	private BinaryOperator convertBinaryOperator(int binaryExpressionKind) {
		BinaryOperator operator = null;
		switch (binaryExpressionKind) {
		case ParserConstants.EQ:
			operator = ComparisonOperator.EQUAL;
			break;
		case ParserConstants.NE:
			operator = ComparisonOperator.NOTEQUAL;
			break;
		case ParserConstants.LE:
			operator = ComparisonOperator.LESSEREQUALTHAN;
			break;
		case ParserConstants.LT:
			operator = ComparisonOperator.LESSERTHAN;
			break;
		case ParserConstants.GE:
			operator = ComparisonOperator.GREATEREQUALTHAN;
			break;
		case ParserConstants.GT:
			operator = ComparisonOperator.GREATERTHAN;
			break;
		case ParserConstants.PLUS:
			operator = BinaryArithmeticOperator.PLUS;
			break;
		case ParserConstants.MINUS:
			operator = BinaryArithmeticOperator.MINUS;
			break;
		case ParserConstants.STAR:
			operator = BinaryArithmeticOperator.TIMES;
			break;
		case ParserConstants.SLASH:
			operator = BinaryArithmeticOperator.DIV;
			break;
		case ParserConstants.BOOL_OR:
			operator = BinaryBooleanOperator.OR;
			break;
		case ParserConstants.BOOL_AND:
			operator = BinaryBooleanOperator.AND;
			break;
		default:
			throw new UnsupportedOperationException("binary operator : " + binaryExpressionKind + " not yet handled");
		}
		return operator;
	}

	private CodeExpression convertPrimaryExpression(BSHPrimaryExpression bshExpression) {
		if (bshExpression.jjtGetNumChildren() == 1) {
			SimpleNode bshExpressionChild = bshExpression.getChild(0);

			if (bshExpressionChild instanceof BSHAmbiguousName) {
				return convertVariableReference((BSHAmbiguousName) bshExpressionChild);
			}

			if (bshExpressionChild instanceof BSHLiteral) {
				return convertLiteral((BSHLiteral) bshExpressionChild);
			}

			if (bshExpressionChild instanceof BSHMethodInvocation) {
				BSHMethodInvocation methodInvocation = (BSHMethodInvocation) bshExpressionChild;
				return convertFunctionCall(methodInvocation);
			}

			if (bshExpressionChild instanceof BSHBinaryExpression) {
				BSHBinaryExpression binaryExpression = (BSHBinaryExpression) bshExpressionChild;
				return convertBinaryExpression(binaryExpression);
			}

			throw new UnsupportedOperationException("not yet implemented node : " + bshExpression + " class : "
					+ bshExpression.getClass() + " text : " + bshExpression.getText() + " num of children : "
					+ bshExpression.jjtGetNumChildren() + " first child : [" + bshExpressionChild.getText()
					+ "] has class : [" + bshExpressionChild.getClass() + "]");
		} else {
			throw new UnsupportedOperationException("handling of primary expression with more than one child : "
					+ bshExpression.jjtGetNumChildren() + " not yet implemented");

		}
	}

	private VariableReference convertVariableReference(BSHAmbiguousName ambiguosName) {
		// TODO gestire i namespace
		String trimmedVariableName = ambiguosName.getText().trim();
		VariableDefinition variableDefinition = nameResolutionState.resolveVariable(trimmedVariableName);

		VariableReference variableReference;
		if (variableDefinition.type instanceof NumericType) {
			variableReference = new ArithmeticVariableReference(trimmedVariableName, variableDefinition.type);
		} else {
			throw new UnsupportedOperationException(
					"Variable reference of type : [" + variableDefinition.type + "] not yet handled");
		}
		return variableReference;
	}

	private CodeExpression convertFunctionCall(BSHMethodInvocation methodInvocation) {
		BSHAmbiguousName nameNode = methodInvocation.getNameNode();
		BSHArguments argsNode = methodInvocation.getArgsNode();
		List<CodeExpression> parameterValues = new Vector<>();
		for (int i = 0; i < argsNode.jjtGetNumChildren(); i++) {
			SimpleNode bshParameterValue = argsNode.getChild(i);
			CodeExpression parameterValue = (CodeExpression) convertTransition(bshParameterValue);
			parameterValues.add(parameterValue);
		}
		FunctionCall functionCall = new FunctionCall(nameNode.getText().trim(), parameterValues);
		return functionCall;
	}

	private CodeExpression convertLiteral(BSHLiteral literal) {
		Primitive bshPrimitive = (Primitive) literal.value;

		CodeExpression expression = null;
		if (bshPrimitive.isNumber()) {
			expression = new IntegerValueExpression(((Integer) bshPrimitive.getValue()).intValue());
		}
		if (bshPrimitive.getValue() instanceof Boolean) {
			if (((Boolean) bshPrimitive.getValue()).booleanValue()) {
				expression = BooleanValueExpression.TRUE;
			} else {
				expression = BooleanValueExpression.FALSE;
			}
		}
		return expression;
	}

}
