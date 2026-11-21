package net.sf.metacad.revenge.constraint;

import java.util.Map;

import net.sf.metacad.revenge.expression.BinaryExpression;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.PlaceholderExpression;
import net.sf.metacad.revenge.expression.SymbolicExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.BinaryIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.MinusIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.RationalValueExpression;
import net.sf.metacad.revenge.expression.logic.BinaryBooleanExpression;
import net.sf.metacad.revenge.expression.logic.ComparisonExpression;
import net.sf.metacad.revenge.expression.logic.NotExpression;

class InfixExpressionPrinter implements CodeExpressionVisitor {

	StringBuffer infixExpressionBuffer;

	public String convert(CodeExpression codeExpression) {
		infixExpressionBuffer = new StringBuffer();
		codeExpression.accept(this);
		return infixExpressionBuffer.toString();
	}

	@Override
	public void arithmeticCondition(CodeExpression expression) {
		if (expression instanceof BinaryIntegerExpression) {
			BinaryIntegerExpression binaryIntegerExpression = (BinaryIntegerExpression) expression;
			infixExpressionBuffer.append("(");

			binaryIntegerExpression.leftSide.accept(this);

			infixExpressionBuffer.append(")");

			switch (binaryIntegerExpression.operator) {
			case DIV:
				infixExpressionBuffer.append("/");
				break;
			case MINUS:
				infixExpressionBuffer.append("-");
				break;
			case PLUS:
				infixExpressionBuffer.append("+");
				break;
			case EXP:
				infixExpressionBuffer.append("^");
				break;
			case TIMES:
				infixExpressionBuffer.append("*");
				break;
			default:
				throw new UnsupportedOperationException("not yet implemented " + binaryIntegerExpression.operator);
			}

			infixExpressionBuffer.append("(");

			binaryIntegerExpression.rightSide.accept(this);

			infixExpressionBuffer.append(")");

		}
		if (expression instanceof MinusIntegerExpression) {
			MinusIntegerExpression minusIntegerExpression = (MinusIntegerExpression) expression;
			infixExpressionBuffer.append("-(");
			minusIntegerExpression.rightSide.accept(this);
			infixExpressionBuffer.append(")");
		}
		if (expression instanceof RationalValueExpression) {
			RationalValueExpression rationalExpression = (RationalValueExpression) expression;
			infixExpressionBuffer.append("(");
			infixExpressionBuffer.append(rationalExpression.numerator());
			infixExpressionBuffer.append("/");
			infixExpressionBuffer.append(rationalExpression.denominator());
			infixExpressionBuffer.append(")");
		}
		if (expression instanceof IntegerValueExpression) {
			IntegerValueExpression integerValueExpression = (IntegerValueExpression) expression;
			infixExpressionBuffer.append(integerValueExpression.value);
		}
	}

	@Override
	public void compare(ComparisonExpression expression) {
		if (expression.leftSide instanceof BinaryExpression) {
			infixExpressionBuffer.append("(");
		}
		expression.leftSide.accept(this);
		if (expression.leftSide instanceof BinaryExpression) {
			infixExpressionBuffer.append(")");
		}
		switch (expression.operator) {
		case EQUAL:
			infixExpressionBuffer.append("=" /* needed for Prolog equations */);
			break;
		default:
			throw new UnsupportedOperationException("not yet implemented " + expression.operator);
		}
		if (expression.rightSide instanceof BinaryExpression) {
			infixExpressionBuffer.append("(");
		}
		expression.rightSide.accept(this);
		if (expression.rightSide instanceof BinaryExpression) {
			infixExpressionBuffer.append(")");
		}
	}

	@Override
	public void compose(BinaryBooleanExpression expression) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void follow(CodeExpression expression) {
		expression.accept(this);
	}

	@Override
	public void negate(NotExpression expression) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void repeat(CodeExpression expression, IntegerExpression times, Map<String, CodeExpression> initialValues) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void useVariable(PlaceholderExpression expression) {
		infixExpressionBuffer.append(expression.getName());
	}

	@Override
	public void useVariable(VariableReference expression) {
		infixExpressionBuffer.append(expression.name);
	}

	@Override
	public void useSymbol(SymbolicExpression expression) {
		infixExpressionBuffer.append(expression.getName());
	}

	@Override
	public void callFunction(String functionName, CodeExpression[] parameterValues) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void stopAt(CodeExpression expression) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

}