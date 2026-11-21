package net.sf.metacad.revenge.expression;

public interface BinaryExpression {
	BinaryOperator getOperator();

	CodeExpression getLeftSide();

	CodeExpression getRightSide();
}
