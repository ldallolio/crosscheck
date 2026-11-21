package net.sf.metacad.revenge.expression.logic;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.BinaryExpression;
import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;

/**
 * @author Luca Dall'Olio
 *
 */
public class BinaryBooleanExpression extends BooleanExpressionBase implements BooleanExpression, BinaryExpression {

	private static final long serialVersionUID = -6554757906369258904L;
	public final BinaryBooleanOperator operator;
	public final BooleanExpression leftSide;
	public final BooleanExpression rightSide;

	@Override
	public CodeExpression getLeftSide() {
		return leftSide;
	}

	@Override
	public CodeExpression getRightSide() {
		return rightSide;
	}

	private BinaryBooleanExpression(BinaryBooleanOperator operator, BooleanExpression leftSide,
			BooleanExpression rightSide) {
		super();
		this.operator = operator;
		this.leftSide = leftSide;
		this.rightSide = rightSide;
	}

	public static BooleanExpression create(BinaryBooleanOperator operator, BooleanExpression leftSide,
			BooleanExpression rightSide) {

		if (operator == null) {
			throw new IllegalArgumentException("operator not valid : [" + operator + "]");
		}

		if (leftSide == null) {
			throw new IllegalArgumentException("left side not valid : [" + leftSide + "]");
		}

		if (rightSide == null) {
			throw new IllegalArgumentException("right side not valid : [" + rightSide + "]");
		}

		if (BinaryBooleanOperator.AND.equals(operator)) {
			if (BooleanValueExpression.FALSE.equals(leftSide) || BooleanValueExpression.FALSE.equals(rightSide)) {
				// Identity law
				return BooleanValueExpression.FALSE;
			}

			if (BooleanValueExpression.TRUE.equals(leftSide)) {
				// Identity law
				return rightSide;
			}

			if (BooleanValueExpression.TRUE.equals(rightSide)) {
				// Identity law
				return leftSide;
			}

			if (leftSide.equals(rightSide)) {
				// Idempotent law
				return leftSide;
			}

			if (leftSide.equals(NotExpression.create(rightSide))) {
				// Complement law
				return BooleanValueExpression.FALSE;
			}

			if (leftSide.contains(rightSide)) {
				if (BooleanValueExpression.FALSE.equals(leftSide.replace(rightSide, BooleanValueExpression.FALSE))) {
					return rightSide;
				}
			}
			if (rightSide.contains(leftSide)) {
				if (BooleanValueExpression.FALSE.equals(rightSide.replace(leftSide, BooleanValueExpression.FALSE))) {
					return leftSide;
				}
			}
			if (leftSide instanceof ComparisonExpression && rightSide instanceof ComparisonExpression) {
				ComparisonExpression leftComparison = (ComparisonExpression) leftSide;
				ComparisonExpression rightComparison = (ComparisonExpression) rightSide;
				if (leftComparison.operator.equals(ComparisonOperator.NOTEQUAL)
						&& (rightComparison.operator.equals(ComparisonOperator.EQUAL))) {
					if (leftComparison.leftSide.equals(rightComparison.leftSide)
							&& !leftComparison.rightSide.equals(rightComparison.rightSide)) {
						return rightComparison;
					}
				} else if (leftComparison.operator.equals(ComparisonOperator.EQUAL)
						&& (rightComparison.operator.equals(ComparisonOperator.EQUAL))) {
					if (leftComparison.leftSide.equals(rightComparison.leftSide)
							&& !leftComparison.rightSide.equals(rightComparison.rightSide)) {
						return BooleanValueExpression.FALSE;
					}
				}
			}

		}

		if (BinaryBooleanOperator.OR.equals(operator)) {
			if (BooleanValueExpression.TRUE.equals(leftSide) || BooleanValueExpression.TRUE.equals(rightSide)) {
				// Identity law
				return BooleanValueExpression.TRUE;
			}

			if (BooleanValueExpression.FALSE.equals(leftSide)) {
				// Identity law
				return rightSide;
			}

			if (BooleanValueExpression.FALSE.equals(rightSide)) {
				// Identity law
				return leftSide;
			}

			if (leftSide.equals(rightSide)) {
				// Idempotent law
				return leftSide;
			}

			if (leftSide.equals(NotExpression.create(rightSide))) {
				// Complement law
				return BooleanValueExpression.TRUE;
			}

			if (leftSide.contains(rightSide)) {
				if (BooleanValueExpression.TRUE.equals(leftSide.replace(rightSide, BooleanValueExpression.TRUE))) {
					return rightSide;
				}
			}
			if (rightSide.contains(leftSide)) {
				if (BooleanValueExpression.TRUE.equals(rightSide.replace(leftSide, BooleanValueExpression.TRUE))) {
					return leftSide;
				}
			}

		}

		BooleanExpression booleanExpression;
		booleanExpression = new BinaryBooleanExpression(operator, leftSide, rightSide);
		return booleanExpression;
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
		visitor.compose(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState leftSideState = leftSide.evaluate(initialState);
		CodeExpression leftSideLeftValue = leftSideState.getLeftValue();
		// TODO handle shortcircuit : for some operators it should become a
		// conditionedexpression, it will be evaluated only if the leftside will
		// not evaluate to some values
		CodeState rightSideState = rightSide.evaluate(leftSideState);
		CodeExpression rightSideLeftValue = rightSideState.getLeftValue();
		rightSideState.setLeftValue(BinaryBooleanExpression.create(operator, (BooleanExpression) leftSideLeftValue,
				(BooleanExpression) rightSideLeftValue));
		return rightSideState;
	}

	@Override
	public String toString() {
		StringBuffer toStringBuffer = new StringBuffer();
		if (!(leftSide instanceof UnaryExpression)) {
			toStringBuffer.append("(");
		}
		toStringBuffer.append(leftSide.toString());
		if (!(leftSide instanceof UnaryExpression)) {
			toStringBuffer.append(")");
		}

		toStringBuffer.append(" " + operator.toString() + " ");

		if (!(rightSide instanceof UnaryExpression)) {
			toStringBuffer.append("(");
		}
		toStringBuffer.append(rightSide.toString());
		if (!(rightSide instanceof UnaryExpression)) {
			toStringBuffer.append(")");
		}
		return toStringBuffer.toString();
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return BinaryBooleanExpression.create(operator, (BooleanExpression) leftSide.replace(search, replace),
					(BooleanExpression) rightSide.replace(search, replace));
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || leftSide.contains(search) || rightSide.contains(search));
	}

	@Override
	public BinaryOperator getOperator() {
		return operator;
	}

}