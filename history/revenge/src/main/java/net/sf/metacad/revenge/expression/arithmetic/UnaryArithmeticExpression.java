package net.sf.metacad.revenge.expression.arithmetic;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.SortedSet;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.CodeExpressionVisitor;
import net.sf.metacad.revenge.expression.ExpressionBase;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;
import net.sf.metacad.revenge.type.NumericType;

public class UnaryArithmeticExpression extends ExpressionBase implements ArithmeticExpression {
	private static final long serialVersionUID = -1L;
	public final CodeExpression rightSide;
	public final UnaryArithmeticOperator operation;

	private UnaryArithmeticExpression(UnaryArithmeticOperator operation, CodeExpression rightSide) {
		super();
		this.rightSide = rightSide;
		this.operation = operation;
	}

	public static CodeExpression create(UnaryArithmeticOperator operation, CodeExpression rightSide) {

		if (operation == null) {
			throw new IllegalArgumentException("operation not valid : [" + operation + "]");
		}

		if (rightSide == null) {
			throw new IllegalArgumentException("rightside not valid : [" + rightSide + "]");
		}

		switch (operation) {
		case CEIL:
			if (rightSide instanceof IntegerValueExpression) {
				// ex ceil(7) == 7
				return rightSide;
			}

			if (rightSide instanceof RationalValueExpression) {
				// ex ceil(5/7)
				RationalExpression rational = (RationalExpression) rightSide;
				return new IntegerValueExpression(
						(int) Math.ceil(rational.numerator() / (double) rational.denominator()));
			}

			if (rightSide instanceof UnaryArithmeticExpression
					&& ((UnaryArithmeticExpression) rightSide).operation.equals(operation)) {
				// ex ceil(ceil(x)) == ceil(x)
				return rightSide;
			}
			break;
		case FLOOR:
			if (rightSide instanceof IntegerValueExpression) {
				return rightSide;
			}

			if (rightSide instanceof RationalExpression) {
				// ex ceil(5/7)
				RationalExpression rational = (RationalExpression) rightSide;
				return new IntegerValueExpression(
						(int) Math.floor(rational.numerator() / (double) rational.denominator()));
			}

			if (rightSide instanceof UnaryArithmeticExpression
					&& ((UnaryArithmeticExpression) rightSide).operation.equals(operation)) {
				// ex floor(floor(x)) == floor(x)
				return rightSide;
			}
			break;
		}

		if (rightSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression rightMultiple = (MultipleConditionedExpression) rightSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : rightMultiple.getConditions()) {
				CodeExpression expression = rightMultiple.getExpression(condition);
				conditionedExpressions.put(condition, UnaryArithmeticExpression.create(operation, expression));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		return new UnaryArithmeticExpression(operation, rightSide);
	}

	@Override
	public boolean isAbout(String variableName) {
		return rightSide.isAbout(variableName);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		return rightSide.affectedVariables();
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// TODO Auto-generated method stub
		//
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		switch (operation) {
		case CEIL:
		case FLOOR:
			// Example : for (i = 1:3) x = ceil(5/7)
			// becomes x = ceil(5/7)
			visitor.arithmeticCondition(this);
			break;

		default:
			throw new UnsupportedOperationException("not yet implemented repeat of : [" + operation + "]");
		}
	}

	@Override
	public CodeType type() {
		switch (operation) {
		case CEIL:
		case FLOOR:
			return NumericType.INT;
		default:
			throw new UnsupportedOperationException("Not yet implemented type of : [" + operation + "]");
		}
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState rightSideState = rightSide.evaluate(initialState);
		rightSideState
		.setLeftValue(UnaryArithmeticExpression.create(operation, rightSideState.getLeftValue()));
		return rightSideState;
	}

	@Override
	public String toString() {
		return operation.name() + "(" + rightSide.toString() + ")";
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return UnaryArithmeticExpression.create(operation, rightSide.replace(search, replace));
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || rightSide.contains(search));
	}
}
