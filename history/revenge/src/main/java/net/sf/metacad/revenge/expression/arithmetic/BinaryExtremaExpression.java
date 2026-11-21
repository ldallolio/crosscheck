package net.sf.metacad.revenge.expression.arithmetic;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import org.apache.commons.lang.ObjectUtils;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.BinaryExpression;
import net.sf.metacad.revenge.expression.BinaryOperator;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.ExpressionBase;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

//TODO merge with BinaryIntegerExpression ?
public class BinaryExtremaExpression extends ExpressionBase
implements ArithmeticExpression, BinaryExpression {
	private static final long serialVersionUID = -1L;
	public final CodeExpression leftSide;
	public final CodeExpression rightSide;
	public final ExtremumOperator operation;

	private BinaryExtremaExpression(ExtremumOperator operation, CodeExpression leftSide,
			CodeExpression rightSide) {
		super();
		this.leftSide = leftSide;
		this.rightSide = rightSide;
		this.operation = operation;
	}

	@SuppressWarnings("unchecked")
	public static CodeExpression create(ExtremumOperator operator, CodeExpression leftSide,
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

		if ((leftSide instanceof IntegerValueExpression || leftSide instanceof RationalValueExpression)
				&& (rightSide instanceof IntegerValueExpression || rightSide instanceof RationalValueExpression)) {
			Comparable<ArithmeticExpression> leftValue = (Comparable<ArithmeticExpression>) leftSide;
			Comparable<ArithmeticExpression> rightValue = (Comparable<ArithmeticExpression>) rightSide;

			ArithmeticExpression result;
			switch (operator) {
			case MIN:
				result = (ArithmeticExpression) ObjectUtils.min(leftValue, rightValue);
				break;
			case MAX:
				result = (ArithmeticExpression) ObjectUtils.max(leftValue, rightValue);
				;
				break;
			default:
				throw new UnsupportedOperationException("Operator : [" + operator + "] not yet handled.");
			}
			return result;
		}

		if (leftSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression leftMultiple = (MultipleConditionedExpression) leftSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : leftMultiple.getConditions()) {
				CodeExpression leftExpression = leftMultiple.getExpression(condition);
				conditionedExpressions.put(condition,
						BinaryExtremaExpression.create(operator, leftExpression, rightSide));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		if (rightSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression rightMultiple = (MultipleConditionedExpression) rightSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : rightMultiple.getConditions()) {
				CodeExpression rightExpression = rightMultiple.getExpression(condition);
				conditionedExpressions.put(condition,
						BinaryExtremaExpression.create(operator, leftSide, rightExpression));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		return new BinaryExtremaExpression(operator, leftSide, rightSide);
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
		switch (operation) {
		case MIN:
		case MAX:
			// Example : for (i = 1:3) x = min(5,7)
			// becomes x = min(5,7)
			visitor.arithmeticCondition(this);
			break;

		default:
			throw new UnsupportedOperationException("not yet implemented repeat of : [" + operation + "]");
		}
	}

	@Override
	public CodeType type() {
		switch (operation) {
		case MIN:
		case MAX:
			return NumericType.INT;

		default:
			throw new UnsupportedOperationException("not yet implemented type of : [" + operation + "]");
		}
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState leftSideState = leftSide.evaluate(initialState);
		CodeExpression leftSideLeftValue = leftSideState.getLeftValue();
		CodeState rightSideState = rightSide.evaluate(leftSideState);
		CodeExpression rightSideLeftValue = rightSideState.getLeftValue();
		rightSideState.setLeftValue(
				BinaryExtremaExpression.create(operation, leftSideLeftValue, rightSideLeftValue));
		return rightSideState;
	}

	@Override
	public String toString() {
		return operation.name() + "(" + leftSide.toString() + "," + rightSide.toString() + ")";
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return BinaryExtremaExpression.create(operation, leftSide.replace(search, replace),
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
		return operation;
	}

	@Override
	public CodeExpression getRightSide() {
		return rightSide;
	}

}
