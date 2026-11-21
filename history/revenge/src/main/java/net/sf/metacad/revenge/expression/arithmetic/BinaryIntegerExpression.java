package net.sf.metacad.revenge.expression.arithmetic;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.BinaryExpression;
import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.ExpressionBase;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.RepeatedExpression;
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

/**
 * @author Luca Dall'Olio
 *
 */
public class BinaryIntegerExpression extends ExpressionBase implements IntegerExpression, BinaryExpression {

	private static final long serialVersionUID = -1129634190097420788L;
	public final BinaryArithmeticOperator operator;
	public final CodeExpression leftSide;
	public final CodeExpression rightSide;

	private BinaryIntegerExpression(BinaryArithmeticOperator operator, CodeExpression leftSide,
			CodeExpression rightSide) {
		super();
		this.operator = operator;
		this.leftSide = leftSide;
		this.rightSide = rightSide;
	}

	public static CodeExpression create(BinaryArithmeticOperator operator, CodeExpression leftSide,
			CodeExpression rightSide) {
		if (leftSide == null) {
			throw new IllegalArgumentException("leftside not valid : [" + leftSide + "]");
		}

		if (operator == null) {
			throw new IllegalArgumentException("operator not valid : [" + operator + "]");
		}

		if (rightSide == null) {
			throw new IllegalArgumentException("rightside not valid : [" + rightSide + "]");
		}

		if (leftSide instanceof RationalExpression && rightSide instanceof RationalExpression) {
			int leftNumerator = ((RationalExpression) leftSide).numerator();
			int leftDenominator = ((RationalExpression) leftSide).denominator();
			int rightNumerator = ((RationalExpression) rightSide).numerator();
			int rightDenominator = ((RationalExpression) rightSide).denominator();
			ArithmeticExpression result;
			switch (operator) {
			case MINUS:
				result = RationalValueExpression.create(
						leftNumerator * rightDenominator - rightNumerator * leftDenominator,
						leftDenominator * rightDenominator);
				break;
			case PLUS:
				result = RationalValueExpression.create(
						leftNumerator * rightDenominator + rightNumerator * leftDenominator,
						leftDenominator * rightDenominator);
				break;
			case TIMES:
				result = RationalValueExpression.create(leftNumerator * rightNumerator,
						leftDenominator * rightDenominator);
				break;
			case DIV:
				result = RationalValueExpression.create(leftNumerator * rightDenominator,
						leftDenominator * rightNumerator);
				break;
			case EXP:
				if (rightDenominator == 1) {
					result = RationalValueExpression.create(leftNumerator ^ rightNumerator,
							leftDenominator ^ rightNumerator);
				} else {
					result = new BinaryIntegerExpression(operator, leftSide, rightSide);
				}
				break;
			default:
				return new BinaryIntegerExpression(operator, leftSide, rightSide);
			}
			return result;
		}

		if (leftSide instanceof RationalExpression) {
			int leftNumerator = ((RationalExpression) leftSide).numerator();
			int leftDenominator = ((RationalExpression) leftSide).denominator();
			switch (operator) {
			case MINUS:
				if (leftNumerator == 0) {
					return MinusIntegerExpression.create(rightSide);
				}
				break;
			case PLUS:
				if (leftNumerator == 0) {
					return rightSide;
				}
				break;
			case EXP:
				// 1 ^ x == cannot say, if x is irrational
				break;
			case TIMES:
				if (leftNumerator == 0) {
					// 0 * x == 0
					return new IntegerValueExpression(0);
				} else if (leftNumerator == leftDenominator) {
					return rightSide;
				}
				break;
			case DIV:
				if (leftNumerator == leftDenominator) {
					// x / 1 == x
					return rightSide;
				}
				break;
			}
		}

		if (rightSide instanceof RationalExpression) {
			int rightNumerator = ((RationalExpression) rightSide).numerator();
			int rightDenominator = ((RationalExpression) rightSide).denominator();
			switch (operator) {
			case MINUS:
				if (rightNumerator == 0) {
					return leftSide;
				}
				break;
			case PLUS:
				if (rightNumerator == 0) {
					return leftSide;
				}
				break;
			case EXP:
				if (rightNumerator == rightDenominator) {
					// x ^ 1 = x
					return leftSide;
				} else if (rightNumerator == 0) {
					// x ^ 0 == 1, even 0 ^ 0 == 1
					// http://en.wikipedia.org/wiki/Exponentiation#Zero_to_the_power_of_zero
					return new IntegerValueExpression(1);
				}
				break;
			case TIMES:
				if (rightNumerator == rightDenominator) {
					return leftSide;
				}
				break;
			case DIV:
				if (rightNumerator == 0) {
					// division by rational 0/x
					throw new IllegalStateException("Division by zero");
				} else if (rightNumerator == rightDenominator) {
					// division by rational 1/1
					return leftSide;
				}
				break;
			}
		}

		if (leftSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression leftMultiple = (MultipleConditionedExpression) leftSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : leftMultiple.getConditions()) {
				CodeExpression leftExpression = leftMultiple.getExpression(condition);
				conditionedExpressions.put(condition,
						BinaryIntegerExpression.create(operator, leftExpression, rightSide));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		if (rightSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression rightMultiple = (MultipleConditionedExpression) rightSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : rightMultiple.getConditions()) {
				CodeExpression rightExpression = rightMultiple.getExpression(condition);
				conditionedExpressions.put(condition,
						BinaryIntegerExpression.create(operator, leftSide, rightExpression));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		return new BinaryIntegerExpression(operator, leftSide, rightSide);
	}

	@Override
	public boolean isAbout(String variableName) {
		return leftSide.isAbout(variableName) || rightSide.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		SortedSet<VariableReference> binaryAffected = new TreeSet<>();
		binaryAffected.addAll(leftSide.affectedVariables());
		binaryAffected.addAll(rightSide.affectedVariables());
		return binaryAffected;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.arithmeticCondition(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		switch (operator) {
		case PLUS:
			// Example : for (i = 1:3) x = y + 5
			// becomes x = y + 5 * 3
			visitor.arithmeticCondition(BinaryIntegerExpression.create(BinaryArithmeticOperator.PLUS,
					RepeatedExpression.create(leftSide, times, initialValues),
					BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
							RepeatedExpression.create(rightSide, times, initialValues), times)));
			break;
		case MINUS:
			// Example : for (i = 1:3) x = y - 5
			// becomes x = y - 5 * 3
			visitor.arithmeticCondition(BinaryIntegerExpression.create(BinaryArithmeticOperator.MINUS,
					RepeatedExpression.create(leftSide, times, initialValues),
					BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
							RepeatedExpression.create(rightSide, times, initialValues), times)));
			break;
		case TIMES:
			if (rightSide instanceof IntegerValueExpression) {
				// Example : for (i = 1:3) x = y * 5
				// becomes x = y * 5 ^ 3
				visitor.arithmeticCondition(BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
						RepeatedExpression.create(leftSide, times, initialValues),
						BinaryIntegerExpression.create(BinaryArithmeticOperator.EXP,
								RepeatedExpression.create(rightSide, times, initialValues), times)));
			} else {
				// Example : for (i = 1:3) x = 5 * z
				// does not become anything simpler
				// Example : for (i = 1:3) x = y * z
				// does not become anything simpler
				visitor.stopAt(RepeatedExpression.create(this, times, initialValues));
			}
			break;
		case DIV:
			// Example : for (i = 1:3) x = y / 5
			// becomes x = y / 5 ^ 3
			visitor.arithmeticCondition(BinaryIntegerExpression.create(BinaryArithmeticOperator.DIV,
					RepeatedExpression.create(leftSide, times, initialValues),
					BinaryIntegerExpression.create(BinaryArithmeticOperator.EXP,
							RepeatedExpression.create(rightSide, times, initialValues), times)));
			break;
		case EXP:
			throw new UnsupportedOperationException("Power repeat has not been implemented yet");
		default:
			throw new UnsupportedOperationException("unknown operator, repeat has not been implemented yet");
		}
	}

	@Override
	public CodeType type() {
		// TODO handle number types
		return NumericType.INT;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState leftSideState = leftSide.evaluate(initialState);
		CodeExpression leftSideLeftValue = leftSideState.getLeftValue();
		CodeState rightSideState = rightSide.evaluate(leftSideState);
		CodeExpression rightSideLeftValue = rightSideState.getLeftValue();
		rightSideState.setLeftValue(BinaryIntegerExpression.create(operator, leftSideLeftValue, rightSideLeftValue));
		return rightSideState;
	}

	@Override
	public String toString() {
		StringBuffer buffer = new StringBuffer();
		if (!(leftSide instanceof UnaryExpression)) {
			buffer.append("(");
		}
		buffer.append(leftSide);
		if (!(leftSide instanceof UnaryExpression)) {
			buffer.append(")");
		}
		buffer.append(" ");
		buffer.append(operator);
		buffer.append(" ");
		if (!(rightSide instanceof UnaryExpression)) {
			buffer.append("(");
		}
		buffer.append(rightSide);
		if (!(rightSide instanceof UnaryExpression)) {
			buffer.append(")");
		}

		return buffer.toString();
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return BinaryIntegerExpression.create(operator, leftSide.replace(search, replace),
					rightSide.replace(search, replace));
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || leftSide.contains(search) || rightSide.contains(search));
	}

	@Override
	public CodeExpression getLeftSide() {
		return leftSide;
	}

	@Override
	public BinaryOperator getOperator() {
		return operator;
	}

	@Override
	public CodeExpression getRightSide() {
		return rightSide;
	}

}
