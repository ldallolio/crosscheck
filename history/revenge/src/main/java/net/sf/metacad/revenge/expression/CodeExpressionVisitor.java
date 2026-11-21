package net.sf.metacad.revenge.expression;

import java.util.Map;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.NotExpression;

public interface CodeExpressionVisitor {
	void useVariable(PlaceholderExpression expression);

	void useVariable(VariableReference expression);

	void callFunction(String functionName, CodeExpression[] parameterValues);

	void useSymbol(SymbolicExpression expression);

	void compare(ComparisonExpression expression);

	void compose(BinaryBooleanExpression expression);

	void arithmeticCondition(CodeExpression expression);

	void negate(NotExpression expression);

	void repeat(CodeExpression expression, IntegerExpression times, Map<String, CodeExpression> initialValues);

	void follow(CodeExpression expression);

	void stopAt(CodeExpression expression);
}