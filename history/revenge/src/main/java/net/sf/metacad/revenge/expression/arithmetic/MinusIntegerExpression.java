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
import net.sf.metacad.revenge.expression.UnaryExpression;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

/**
 * @author Luca Dall'Olio
 *
 */
public class MinusIntegerExpression extends ExpressionBase implements IntegerExpression, UnaryExpression {

	private static final long serialVersionUID = 8079834255682461850L;
	public final CodeExpression rightSide;

	private MinusIntegerExpression(CodeExpression rightSide) {
		super();
		this.rightSide = rightSide;
	}

	public static CodeExpression create(CodeExpression rightSide) {

		if (rightSide == null) {
			throw new IllegalArgumentException("rightside not valid : [" + rightSide + "]");
		}

		if (rightSide instanceof MinusIntegerExpression) {
			return ((MinusIntegerExpression) rightSide).rightSide;
		}

		if (rightSide instanceof IntegerValueExpression) {
			return new IntegerValueExpression(((IntegerValueExpression) rightSide).value * -1);
		}

		if (rightSide instanceof RationalExpression) {
			return RationalValueExpression.create(((RationalExpression) rightSide).numerator() * -1,
					((RationalExpression) rightSide).denominator());
		}

		if (rightSide instanceof MultipleConditionedExpression) {
			MultipleConditionedExpression rightMultiple = (MultipleConditionedExpression) rightSide;
			Map<BooleanExpression, CodeExpression> conditionedExpressions = new LinkedHashMap<>();
			for (BooleanExpression condition : rightMultiple.getConditions()) {
				CodeExpression expression = rightMultiple.getExpression(condition);
				conditionedExpressions.put(condition, MinusIntegerExpression.create(expression));
			}
			return MultipleConditionedExpression.create(conditionedExpressions);
		}

		return new MinusIntegerExpression(rightSide);
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
		visitor.arithmeticCondition(this);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// Example : for (i = 1:3) x = - y
		// becomes x = -1 ^ 3 * y
		// TODO : simplify using a factory method (if "times" is even then ...)
		visitor.arithmeticCondition(BinaryIntegerExpression.create(BinaryArithmeticOperator.TIMES,
				BinaryIntegerExpression.create(BinaryArithmeticOperator.EXP, new IntegerValueExpression(-1), times),
				rightSide));
	}

	@Override
	public CodeType type() {
		return rightSide.type();
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState rightSideState = rightSide.evaluate(initialState);
		rightSideState.setLeftValue(MinusIntegerExpression.create(rightSideState.getLeftValue()));
		return rightSideState;
	}

	@Override
	public String toString() {
		return "MINUS(" + rightSide.toString() + ")";
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		if (equals(search)) {
			return replace;
		} else {
			return MinusIntegerExpression.create(rightSide.replace(search, replace));
		}
	}

	@Override
	public boolean contains(CodeExpression search) {
		return (equals(search) || rightSide.contains(search));
	}

}
