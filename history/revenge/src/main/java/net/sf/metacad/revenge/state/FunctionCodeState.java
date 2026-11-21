package net.sf.metacad.revenge.state;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;

interface FunctionCodeState {

	boolean isFunctionDefined(FunctionSignature signature);

	void defineFunction(FunctionDefinition function);

	void setRecursionCondition(FunctionSignature signature, BooleanExpression expression);

	BooleanExpression getRecursionCondition(FunctionSignature signature);

	FunctionDefinition resolveFunction(FunctionSignature signature);

	CodeExpression getReturnExpression();

	void setReturnExpression(CodeExpression returnExpression);

	CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues);
}