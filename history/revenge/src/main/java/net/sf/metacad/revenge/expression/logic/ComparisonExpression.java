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
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.PlaceholderReference;
import net.sf.metacad.revenge.expression.RepeatedExpression;
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.IntegerValueExpression;
import net.sf.metacad.revenge.expression.arithmetic.MinusIntegerExpression;
import net.sf.metacad.revenge.expression.arithmetic.UnaryArithmeticExpression;
import net.sf.metacad.revenge.state.CodeState;

/**
 * @author Luca Dall'Olio
 *
 */
public class ComparisonExpression extends BooleanExpressionBase implements BooleanExpression, BinaryExpression {

	private static final long serialVersionUID = -1L;
	public final ComparisonOperator operator;
	public final CodeExpression leftSide;
	public final CodeExpression rightSide;

	private ComparisonExpression(ComparisonOperator operator, CodeExpression leftSide, CodeExpression rightSide) {
		super();
		this.operator = operator;
		this.leftSide = leftSide;
		this.rightSide = rightSide;
	}

	public static BooleanExpression create(ComparisonOperator operator, CodeExpression leftSide,
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

		if (leftSide instanceof IntegerValueExpression && rightSide instanceof IntegerValueExpression) {
			int leftValue = ((IntegerValueExpression) leftSide).value;
			int rightValue = ((IntegerValueExpression) rightSide).value;
			BooleanValueExpression result;
			switch (operator) {
			case EQUAL:
				result = BooleanValueExpression.create(leftValue == rightValue);
				break;
			case NOTEQUAL:
				result = BooleanValueExpression.create(leftValue != rightValue);
				break;
			case GREATEREQUALTHAN:
				result = BooleanValueExpression.create(leftValue >= rightValue);
				break;
			case GREATERTHAN:
				result = BooleanValueExpression.create(leftValue > rightValue);
				break;
			case LESSEREQUALTHAN:
				result = BooleanValueExpression.create(leftValue <= rightValue);
				break;
			case LESSERTHAN:
				result = BooleanValueExpression.create(leftValue < rightValue);
				break;
			default:
				throw new UnsupportedOperationException("Operator : [" + operator + "] not yet handled.");
			}
			return result;
		}

		if (leftSide instanceof MinusIntegerExpression && rightSide instanceof MinusIntegerExpression) {
			CodeExpression innerLeftSide = ((MinusIntegerExpression) leftSide).rightSide;
			CodeExpression innerRightSide = ((MinusIntegerExpression) rightSide).rightSide;
			return ComparisonExpression.create(operator.swap(), innerLeftSide, innerRightSide);
		}

		if (rightSide instanceof VariableReference && !(leftSide instanceof VariableReference)) {
			return new ComparisonExpression(operator.swap(), rightSide, leftSide);
		}

		if (leftSide instanceof MinusIntegerExpression && rightSide instanceof IntegerValueExpression) {
			CodeExpression innerLeftSide = ((MinusIntegerExpression) leftSide).rightSide;
			CodeExpression innerRightSide = new IntegerValueExpression(-((IntegerValueExpression) rightSide).value);
			return ComparisonExpression.create(operator.swap(), innerLeftSide, innerRightSide);
		}

		if (leftSide instanceof IntegerValueExpression && rightSide instanceof MinusIntegerExpression) {
			CodeExpression innerLeftSide = new IntegerValueExpression(-((IntegerValueExpression) leftSide).value);
			CodeExpression innerRightSide = ((MinusIntegerExpression) rightSide).rightSide;
			return ComparisonExpression.create(operator.swap(), innerLeftSide, innerRightSide);
		}

		switch (operator) {
		case LESSEREQUALTHAN:
		case GREATEREQUALTHAN:
		case EQUAL:
			if (leftSide.equals(rightSide)) {
				return BooleanValueExpression.TRUE;
			}
			break;
		case LESSERTHAN:
		case GREATERTHAN:
		case NOTEQUAL:
			if (leftSide.equals(rightSide)) {
				return BooleanValueExpression.FALSE;
			}
			break;
		}

		if (leftSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression multipleLeft = (MultipleConditionedExpression) leftSide;
			BooleanExpression compositeExpression = null;
			for (BooleanExpression condition : multipleLeft.getConditions()) {
				CodeExpression leftExpression = multipleLeft.getExpression(condition);
				BooleanExpression comparison = ComparisonExpression.create(operator, leftExpression, rightSide);
				if (compositeExpression != null) {
					compositeExpression = BinaryBooleanExpression.create(BinaryBooleanOperator.OR, compositeExpression,
							comparison);
				} else {
					compositeExpression = comparison;
				}
			}
			return compositeExpression;
		}

		if (rightSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression multipleRight = (MultipleConditionedExpression) rightSide;
			BooleanExpression compositeExpression = null;
			for (BooleanExpression condition : multipleRight.getConditions()) {
				CodeExpression rightExpression = multipleRight.getExpression(condition);
				BooleanExpression comparison = BinaryBooleanExpression.create(BinaryBooleanOperator.AND, condition,
						ComparisonExpression.create(operator, leftSide, rightExpression));
				if (compositeExpression != null) {
					compositeExpression = BinaryBooleanExpression.create(BinaryBooleanOperator.OR, compositeExpression,
							comparison);
				} else {
					compositeExpression = comparison;
				}
			}
			return compositeExpression;
		}

		return new ComparisonExpression(operator, leftSide, rightSide);
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
		visitor.compare(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// TODO : this should be really done in SymbolicVisitor...
		if (operator.equals(ComparisonOperator.EQUAL)) {
			if (leftRecursive()) {
				PlaceholderReference leftVariable = (PlaceholderReference) leftSide.affectedVariables().first();
				CodeExpression replaced = rightSide.replace(leftSide, initialValues.get(leftVariable.localName));
				// TODO : add check for commutativity or at least for
				// iterated function known solution
				CodeExpression replaced2 = replaced.replace(leftSide, initialValues.get(leftVariable.localName));
				visitor.compare((ComparisonExpression) ComparisonExpression.create(operator, leftSide, replaced));
			} else if (leftNormalizedInAVariable()) {
				visitor.follow(ComparisonExpression.create(operator, leftSide,
						RepeatedExpression.create(rightSide, times, initialValues)));
			} else {
				throw new UnsupportedOperationException("Repeat of : [" + toString() + "] not yet implemented");
			}
		} else {
			throw new UnsupportedOperationException("Repeat of : [" + operator.toString() + "] not yet implemented");
		}
	}

	private boolean leftRecursive() {
		return leftSide.affectedVariables().size() == 1
				&& leftSide.affectedVariables().equals(rightSide.affectedVariables());
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState leftSideState = leftSide.evaluate(initialState);
		CodeExpression leftSideLeftValue = leftSideState.getLeftValue();
		CodeState rightSideState = rightSide.evaluate(leftSideState);
		CodeExpression rightSideLeftValue = rightSideState.getLeftValue();
		rightSideState.setLeftValue(ComparisonExpression.create(operator, leftSideLeftValue, rightSideLeftValue));
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
			return ComparisonExpression.create(operator, leftSide.replace(search, replace),
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

	public boolean constant() {
		return leftSide.affectedVariables().isEmpty() && rightSide.affectedVariables().isEmpty();
	}

	public boolean leftSolved() {
		return leftSide instanceof VariableReference && rightSide.affectedVariables().isEmpty();
	}

	public boolean leftNormalizedInAVariable() {
		return leftSide instanceof VariableReference && !rightSide.affectedVariables().contains(leftSide);
	}

	public boolean rightNormalizedInAVariable() {
		return rightSide instanceof VariableReference && !leftSide.affectedVariables().contains(rightSide);
	}

	public BooleanExpression swapsides() {
		return ComparisonExpression.create(operator.swap(), rightSide, leftSide);
	}

	public BooleanExpression minimize(VariableReference variable) {
		BooleanExpression result;
		if (!affectedVariables().contains(variable)) {
			result = this;
		} else {
			CodeExpression minimizedLeftSide = null;
			if (leftSide instanceof ComparisonExpression) {
				minimizedLeftSide = ((ComparisonExpression) leftSide).minimize(variable);
			} else {
				minimizedLeftSide = leftSide;
			}
			CodeExpression minimizedRightSide = null;
			if (rightSide instanceof ComparisonExpression) {
				minimizedRightSide = ((ComparisonExpression) rightSide).minimize(variable);
			} else {
				minimizedRightSide = rightSide;
			}
			switch (operator) {
			case GREATEREQUALTHAN:
				result = ComparisonExpression.create(ComparisonOperator.EQUAL, minimizedLeftSide,
						UnaryArithmeticExpression.create(operator.minimizingOperator(), minimizedRightSide));
				break;
				// case EQUAL:
				// result = this;
				// break;
				// case GREATERTHAN:
				// result = ComparisonExpression.create(ComparisonOperator.EQUAL, minimizedLeftSide,
				// BinaryIntegerExpression.create(BinaryArithmeticOperator.MINUS, minimizedRightSide,
				// new IntegerValueExpression(1)));
				// break;
				// case NOTEQUAL:
				// result = ComparisonExpression.create(ComparisonOperator.LESSERTHAN, minimizedLeftSide,
				// minimizedRightSide);
				// break;
			default:
				result = this;
			}
		}
		return result;
	}

}
